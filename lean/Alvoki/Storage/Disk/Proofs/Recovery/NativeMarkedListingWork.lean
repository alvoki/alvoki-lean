import Alvoki.Storage.Disk.Proofs.Recovery.FailedCheckpointDigestCensus
import Alvoki.Storage.Disk.Proofs.Recovery.NativeOpenListingError
import Alvoki.Storage.Disk.Proofs.Recovery.MetadataRecoveryChunkWork

namespace Alvoki.Storage.DiskSession

open System Manifest RecoveryRequestCount WalSegmentRepair

private def dropCount {state α : Type} : EStateM.Result IO.Error (state × Nat) α → EStateM.Result IO.Error state α
  | .ok value (reached, _) => .ok value reached
  | .error cause (reached, _) => .error cause reached

private def charged {state α : Type} (action : EStateM IO.Error state α) (calls : Nat) :
    EStateM IO.Error (state × Nat) α := fun (before, count) =>
  match action before with
  | .ok value after => .ok value (after, count + calls)
  | .error cause after => .error cause (after, count + calls)

private theorem dropCount_charged {state α : Type} (action : EStateM IO.Error state α) (calls count : Nat) (before : state) :
    dropCount (charged action calls (before, count)) = action before := by
  cases observed : action before <;> simp [charged, observed, dropCount]

namespace NativeReaddirFailure

variable {entry : DescriptorInventory} {view : DirectoryReadNamespace} {root : DeviceInode} {path : FilePath}

/-- The charged scan uses the original stream callbacks. Its names count
the successful readdir steps and its terminal error counts the last one. -/
def directoryWork (seen : NativeReaddirFailure entry view root path) : DirectoryReadWork :=
  (CheckedDirectoryReadReport.scanned seen.scan).work

private def directoryCalls (seen : NativeReaddirFailure entry view root path) : Nat :=
  seen.directoryWork.opendirCalls + seen.directoryWork.readdirCalls + seen.directoryWork.closedirCalls

def counted (seen : NativeReaddirFailure entry view root path) :
    EStateM IO.Error (DescriptorInventory × Nat) (Array IO.FS.DirEntry) :=
  charged seen.run seen.directoryCalls

theorem counted_projects (seen : NativeReaddirFailure entry view root path) (count : Nat) :
    dropCount (seen.counted (entry, count)) = seen.run entry := dropCount_charged seen.run _ count entry

theorem counted_error (seen : NativeReaddirFailure entry view root path) (count : Nat) :
    seen.counted (entry, count) = .error seen.cause (entry, count + (seen.scan.names.length + 3)) ∧
    seen.directoryWork.opendirCalls = 1 ∧ seen.directoryWork.readdirCalls = seen.scan.names.length + 1 ∧
    seen.directoryWork.closedirCalls = 1 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [counted, charged, seen.run_error, directoryCalls, directoryWork, CheckedDirectoryReadReport.work]
  congr 2
  omega

end NativeReaddirFailure

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {seen : NativeMarkedListingError admission}

private def discardCache {α : Type} (action : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) α)
    (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState α := fun before =>
  match action (cache, before) with
  | .ok value (_, reached) => .ok value reached
  | .error cause (_, reached) => .error cause reached

private def runExtent (reads : CheckpointRunChunkReads) (path : FilePath) : Except IO.Error Nat := do
  let (metadata, _) ← reads.stat path
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  return metadata.byteSize.toNat

private theorem readsListingMarker {reads : CheckpointRunChunkReads} {release : FilePath → List LockReferenceDrop}
    (file : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root seen.marker)
    (available : PrefixChunksAvailableUntilEof seen.marker (reads.readChunk file.observesFile.slot.description))
    (custody : TemporaryPrefixCustody file.calls seen.atMarker (release (directory.file .walBoundary)))
    (entered : seen.atListing = seen.atMarker.afterDrops (custody.beforeOpen ++ release (directory.file .walBoundary)))
    (callback : seen.readOptional = fun path => discardCache (readTemporaryMetadata reads directory release path) admission.cache) :
    seen.readOptional (directory.file .walBoundary) (seen.atMarker, admission.held) =
      .ok (some seen.marker) (seen.atListing, admission.held) := by
  have bounded := file.markerPrefix available
  have size : seen.marker.size ≤ WAL.Boundary.acquisitionLimit := by
    rw [← WAL.Boundary.decode_reencode seen.decoded, WAL.Boundary.encode_size]
    decide
  rw [Nat.min_eq_right size, ByteArray.extract_zero_size] at bounded
  have read := custody.readMetadata bounded admission.cache admission.held
  simp only [callback, discardCache, read, entered]

private abbrev CountedOpenState := CensusOpenState × Nat
private abbrev CountedMetadataRead := FilePath → EStateM IO.Error CountedOpenState (Option ByteArray)
private abbrev CountedRunRead := FilePath → Nat → EStateM IO.Error CountedOpenState ByteArray

private def countedListingWorker (metadata : CountedMetadataRead) (runPrefix : CountedRunRead)
    (rest : NativeMarkedListingError.Remainder) : EStateM IO.Error CountedOpenState Reopened :=
  reopenMarkedBoundedWithCachedExtents directory metadata (fun path => charged (seen.readRunSize path) 0)
    runPrefix (fun path => charged (seen.list path) seen.listing.directoryCalls)
    (fun path => charged (rest.lstat path) 0) (fun path count => charged (rest.readSeal path count) 0)
    (fun path count size => charged (rest.readKeeper path count size) 0) (fun path => charged (rest.remove path) 0)
    (fun path bytes => charged (rest.stage path bytes) 0) (fun paths => charged (rest.sync paths) 0)
    (fun source target => charged (rest.rename source target) 0)

private theorem countedListingWorker_error (metadata : CountedMetadataRead) (runPrefix : CountedRunRead)
    (rest : NativeMarkedListingError.Remainder) {atMarker atListing : Nat}
    (checkpoint : readIntegrityCheckpointSized directory (metadata (directory.file .manifest))
      (fun path => charged (seen.readRunSize path) 0) runPrefix ((admission.reached, admission.held), 0) =
        .ok seen.checkpoint ((seen.atMarker, admission.held), atMarker))
    (marker : metadata (directory.file .walBoundary) ((seen.atMarker, admission.held), atMarker) =
      .ok (some seen.marker) ((seen.atListing, admission.held), atListing)) :
    countedListingWorker (seen := seen) metadata runPrefix rest ((admission.reached, admission.held), 0) =
      .error seen.listing.cause ((seen.atListing, admission.held), atListing + seen.listing.directoryCalls) := by
  have listed := seen.listed
  rw [seen.listing.run_error] at listed
  simp only [countedListingWorker, reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders,
    readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate, Bind.bind, EStateM.bind, checkpoint, marker,
    seen.decoded, seen.checked, true_and, ↓reduceIte, liftExcept, Except.mapError, Pure.pure, EStateM.pure, charged, listed]

private theorem markedListingError (rest : NativeMarkedListingError.Remainder) :
    seen.marked rest directory (admission.reached, admission.held) = .error seen.listing.cause (seen.atListing, admission.held) := by
  have actual := seen.stopsAtListing rest (pure ⟨.empty, 0, 0, 0⟩)
  rw [admission.recoverWithMarked_selects seen.flat seen.route] at actual
  simpa only [Option.isSome_some, ↓reduceIte] using actual

/-- A returned readdir error after an accepted present manifest. Each
raw read is tied to the failing worker's original callback. The run
opens and closes follow increasing manifest index before the marker read. -/
structure NativeMarkedListingWork (seen : NativeMarkedListingError admission) where
  reads : CheckpointRunChunkReads
  bytes : ByteArray
  selected : retry.image.directory.active.manifest = some bytes
  manifest : IntegrityCheckpoint
  decoded : IntegrityCheckpoint.decode bytes = .ok manifest
  file : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes
  fits : IntegrityCheckpoint.acquisitionSize bytes < USize.size
  release : FilePath → List LockReferenceDrop
  manifestCustody : TemporaryPrefixCustody file.calls admission.reached (release (directory.file .manifest))
  atRuns : DescriptorInventory
  enteredRuns : atRuns = admission.reached.afterDrops (manifestCustody.beforeOpen ++ release (directory.file .manifest))
  payload : Nat → ByteArray
  events : Nat → List LockReferenceDrop
  runs : ∀ index < manifest.header.runCount.toNat,
    ReachedDigestRun reads directory admission.view admission.root manifest index (payload index)
      (atRuns.afterDrops (runReadDrops events index)) (release (directory.file (.run manifest.header.generation index)))
  order : ∀ index (within : index < manifest.header.runCount.toNat),
    events index = (runs index within).custody.beforeOpen ++ release (directory.file (.run manifest.header.generation index))
  enteredMarker : seen.atMarker = atRuns.afterDrops (runReadDrops events manifest.header.runCount.toNat)
  selectedMarker : retry.image.directory.active.walBoundary = some seen.marker
  markerFile : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root seen.marker
  markerAvailable : PrefixChunksAvailableUntilEof seen.marker (reads.readChunk markerFile.observesFile.slot.description)
  markerCustody : TemporaryPrefixCustody markerFile.calls seen.atMarker (release (directory.file .walBoundary))
  enteredListing : seen.atListing = seen.atMarker.afterDrops (markerCustody.beforeOpen ++ release (directory.file .walBoundary))
  metadataCallback : seen.readOptional = fun path => discardCache (readTemporaryMetadata reads directory release path) admission.cache
  sizeCallback : seen.readRunSize = fun path => liftExcept (runExtent reads path)
  prefixCallback : seen.readRunPrefix = fun path count =>
    discardCache (readTemporaryPrefix reads (IO.userError checkpointIntegrityMismatch) release path count) admission.cache

namespace NativeMarkedListingWork

def manifestChunks (report : NativeMarkedListingWork seen) : Nat :=
  recoveryCalls Prod.snd (report.reads.countMetadata directory (directory.file .manifest) (0, 0))

def markerChunks (report : NativeMarkedListingWork seen) : Nat :=
  recoveryCalls Prod.snd (report.reads.countMetadata directory (directory.file .walBoundary) (0, 0))

noncomputable def runChunks (report : NativeMarkedListingWork seen) (path : FilePath) (count : Nat) : Nat :=
  reached (report.reads.countPrefix (IO.userError checkpointIntegrityMismatch) path count 0)

private noncomputable def countRuns (report : NativeMarkedListingWork seen) (index : Nat) : Nat :=
  ((List.range index).map fun i => (report.manifest.runs[i]?.map fun stamp =>
    report.runChunks (directory.file (.run report.manifest.header.generation i)) stamp.byteCount.toNat).getD 0).sum

private theorem countRuns_step (report : NativeMarkedListingWork seen) {index : Nat} {stamp : RunIntegrity}
    (stamped : report.manifest.runs[index]? = some stamp) :
    report.countRuns (index + 1) = report.countRuns index +
      report.runChunks (directory.file (.run report.manifest.header.generation index)) stamp.byteCount.toNat := by
  simp only [countRuns, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, stamped, Option.map_some, Option.getD_some]

noncomputable def chunkRequests (report : NativeMarkedListingWork seen) : Nat :=
  report.manifestChunks + report.countRuns report.manifest.header.runCount.toNat + report.markerChunks

private def countedMetadata (report : NativeMarkedListingWork seen) (path : FilePath) :
    EStateM IO.Error (CensusOpenState × Nat) (Option ByteArray) :=
  charged (seen.readOptional path) (recoveryCalls Prod.snd (report.reads.countMetadata directory path (0, 0)))

private noncomputable def countedRunPrefix (report : NativeMarkedListingWork seen) (path : FilePath) (count : Nat) :
    EStateM IO.Error (CensusOpenState × Nat) ByteArray :=
  charged (seen.readRunPrefix path count) (report.runChunks path count)

private theorem readsManifest (report : NativeMarkedListingWork seen) :
    seen.readOptional (directory.file .manifest) (admission.reached, admission.held) =
      .ok (some report.bytes) (report.atRuns, admission.held) := by
  have exactPrefix := report.file.manifestPrefix report.fits
  rw [IntegrityCheckpoint.acquisitionPrefix_eq_of_decode report.decoded] at exactPrefix
  have read := report.manifestCustody.readMetadata exactPrefix admission.cache admission.held
  simp only [report.metadataCallback, discardCache, read, report.enteredRuns]

private theorem readsMarker (report : NativeMarkedListingWork seen) :
    seen.readOptional (directory.file .walBoundary) (seen.atMarker, admission.held) =
      .ok (some seen.marker) (seen.atListing, admission.held) :=
  readsListingMarker report.markerFile report.markerAvailable report.markerCustody report.enteredListing report.metadataCallback

private def atRun (report : NativeMarkedListingWork seen) (index : Nat) : CensusOpenState :=
  (report.atRuns.afterDrops (runReadDrops report.events index), admission.held)

private theorem readsRun (report : NativeMarkedListingWork seen) (index : Nat)
    (within : index < report.manifest.header.runCount.toNat) :
    let run := report.runs index within
    let path := directory.file (.run report.manifest.header.generation index)
    seen.readRunSize path (report.atRun index) = .ok run.stamp.byteCount.toNat (report.atRun index) ∧
    seen.readRunPrefix path run.stamp.byteCount.toNat (report.atRun index) =
      .ok (report.payload index) (report.atRun (index + 1)) := by
  intro run path
  have measured : runExtent report.reads path = .ok run.stamp.byteCount.toNat := run.measures
  have read := run.custody.readPrefix (IO.userError checkpointIntegrityMismatch) run.bound run.contents
    (run.extent.symm ▸ run.fits) admission.cache admission.held
  rw [run.extent] at read
  have later : (report.atRun index).1.afterDrops (run.custody.beforeOpen ++ report.release path) =
      (report.atRun (index + 1)).1 := by
    simp only [atRun, runReadDrops, report.order index within, DescriptorInventory.afterDrops_append]
    rfl
  change readTemporaryPrefix report.reads (IO.userError checkpointIntegrityMismatch) report.release path
    run.stamp.byteCount.toNat (admission.cache, report.atRun index) =
    .ok (report.payload index) (admission.cache,
      (report.atRun index).1.afterDrops (run.custody.beforeOpen ++ report.release path), admission.held) at read
  refine ⟨?_, ?_⟩
  · simp only [report.sizeCallback, measured, liftExcept, Pure.pure, EStateM.pure]
  · simp only [report.prefixCallback, discardCache, read, later]
    rfl

private theorem readsRuns (report : NativeMarkedListingWork seen) :
    readIntegrityRunBytesSized directory report.manifest seen.readRunSize seen.readRunPrefix (report.atRun 0) =
      .ok ((List.range report.manifest.header.runCount.toNat).map report.payload)
        (report.atRun report.manifest.header.runCount.toNat) := by
  apply readIntegrityRunBytesSized_effects directory report.manifest seen.readRunSize seen.readRunPrefix
    report.atRun report.payload
  intro index within
  let run := report.runs index within
  exact ⟨run.stamp, run.stamped, run.fits, run.extent, (report.readsRun index within).1, (report.readsRun index within).2⟩

private theorem countedRuns (report : NativeMarkedListingWork seen) (start : Nat) :
    readIntegrityRunBytesSized directory report.manifest (fun path => charged (seen.readRunSize path) 0)
      report.countedRunPrefix (report.atRun 0, start) =
      .ok ((List.range report.manifest.header.runCount.toNat).map report.payload)
        (report.atRun report.manifest.header.runCount.toNat, start + report.countRuns report.manifest.header.runCount.toNat) := by
  let states := fun i => (report.atRun i, start + report.countRuns i)
  change readIntegrityRunBytesSized directory report.manifest (fun path => charged (seen.readRunSize path) 0)
    report.countedRunPrefix (states 0) = .ok _ (states report.manifest.header.runCount.toNat)
  apply readIntegrityRunBytesSized_effects directory report.manifest _ _ states report.payload
  intro index within
  let run := report.runs index within
  refine ⟨run.stamp, run.stamped, run.fits, run.extent, ?_, ?_⟩
  · simp only [states, charged, (report.readsRun index within).1, Nat.add_zero]
    rfl
  · have read : seen.readRunPrefix (directory.file (.run report.manifest.header.generation index))
        run.stamp.byteCount.toNat (report.atRun index) = .ok (report.payload index) (report.atRun (index + 1)) :=
      (report.readsRun index within).2
    simp only [states, countedRunPrefix, charged, read]
    simp only [report.countRuns_step run.stamped, Nat.add_assoc]

private theorem atRun_zero (report : NativeMarkedListingWork seen) : report.atRun 0 = (report.atRuns, admission.held) := by
  simp only [atRun, runReadDrops]
  cases report.atRuns
  simp [DescriptorInventory.afterDrops]

private theorem atRun_marker (report : NativeMarkedListingWork seen) :
    report.atRun report.manifest.header.runCount.toNat = (seen.atMarker, admission.held) := by
  simp only [atRun, report.enteredMarker]

/-- Execute the sized checkpoint reader while retaining separate counts
for its actual manifest and selected run reads. The loaded checkpoint and
reached census agree with the worker before its marker read. -/
theorem countedCheckpoint (report : NativeMarkedListingWork seen) :
    readIntegrityCheckpointSized directory (report.countedMetadata (directory.file .manifest))
      (fun path => charged (seen.readRunSize path) 0) report.countedRunPrefix ((admission.reached, admission.held), 0) =
      .ok seen.checkpoint ((seen.atMarker, admission.held),
        report.manifestChunks + report.countRuns report.manifest.header.runCount.toNat) := by
  have countedManifest : report.countedMetadata (directory.file .manifest) ((admission.reached, admission.held), 0) =
      .ok (some report.bytes) (report.atRun 0, report.manifestChunks) := by
    simp only [countedMetadata, charged, report.readsManifest, report.atRun_zero, Nat.zero_add, manifestChunks]
  have loaded := seen.loaded
  have rawRuns := report.readsRuns
  rw [report.atRun_zero, report.atRun_marker] at rawRuns
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, report.readsManifest, report.decoded,
    Except.mapError, liftExcept, Pure.pure, EStateM.pure, rawRuns] at loaded
  have countedRuns := report.countedRuns report.manifestChunks
  rw [report.atRun_marker] at countedRuns
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, countedManifest, report.decoded,
    Except.mapError, liftExcept, Pure.pure, EStateM.pure, countedRuns]
  cases loadedRun : loadIntegrityRunSet report.manifest ((List.range report.manifest.header.runCount.toNat).map report.payload) with
  | error cause => simp [loadedRun, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at loaded
  | ok table =>
    simp only [loadedRun, EStateM.pure, EStateM.Result.ok.injEq] at loaded
    simp only [EStateM.pure, loaded.1]

theorem countedCheckpoint_projects (report : NativeMarkedListingWork seen) :
    dropCount (readIntegrityCheckpointSized directory (report.countedMetadata (directory.file .manifest))
      (fun path => charged (seen.readRunSize path) 0) report.countedRunPrefix ((admission.reached, admission.held), 0)) =
      readIntegrityCheckpointSized directory (seen.readOptional (directory.file .manifest)) seen.readRunSize seen.readRunPrefix
        (admission.reached, admission.held) := by
  rw [report.countedCheckpoint, seen.loaded]
  rfl

private theorem countedMarker (report : NativeMarkedListingWork seen) (start : Nat) :
    report.countedMetadata (directory.file .walBoundary) ((seen.atMarker, admission.held), start) =
      .ok (some seen.marker) ((seen.atListing, admission.held), start + report.markerChunks) := by
  simp only [countedMetadata, charged, report.readsMarker, markerChunks]

def directoryRequests (_report : NativeMarkedListingWork seen) : Nat := seen.listing.directoryCalls

theorem directoryRequests_exact (report : NativeMarkedListingWork seen) :
    report.directoryRequests = seen.listing.scan.names.length + 3 := by
  simp only [directoryRequests, NativeReaddirFailure.directoryCalls, NativeReaddirFailure.directoryWork,
    CheckedDirectoryReadReport.work]
  omega

/-- The counted worker uses the same sized reader, selected WAL checks
and repair continuation. On this path the directory error stops before
any extent or WAL payload callback and before any repair. -/
noncomputable def countedMarked (report : NativeMarkedListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    EStateM IO.Error (CensusOpenState × Nat) Reopened :=
  countedListingWorker (seen := seen) report.countedMetadata report.countedRunPrefix rest

theorem countedMarked_error (report : NativeMarkedListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    report.countedMarked rest ((admission.reached, admission.held), 0) =
      .error seen.listing.cause ((seen.atListing, admission.held), report.chunkRequests + report.directoryRequests) :=
  countedListingWorker_error _ _ rest report.countedCheckpoint (report.countedMarker _)

/-- Erasure yields the original marked worker's exact route error and
pre-unlock census. The existing native opener then applies local unlock
on this state and gives its error precedence over the listing error. -/
theorem countedMarked_projects (report : NativeMarkedListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    dropCount (report.countedMarked rest ((admission.reached, admission.held), 0)) =
      seen.marked rest directory (admission.reached, admission.held) := by
  rw [report.countedMarked_error, markedListingError rest]
  rfl

theorem listingInodes (report : NativeMarkedListingWork seen) : seen.atListing.inode = admission.reached.inode := by
  have listing := congrArg DescriptorInventory.inode report.enteredListing
  have marker := congrArg DescriptorInventory.inode report.enteredMarker
  have runs := congrArg DescriptorInventory.inode report.enteredRuns
  change seen.atListing.inode = seen.atMarker.inode at listing
  change seen.atMarker.inode = report.atRuns.inode at marker
  change report.atRuns.inode = admission.reached.inode at runs
  exact listing.trans (marker.trans runs)

def selectedRunBytes (report : NativeMarkedListingWork seen) : Nat :=
  (report.manifest.runs.map (·.byteCount.toNat)).sum

private theorem countRuns_le (report : NativeMarkedListingWork seen) (index : Nat)
    (within : index ≤ report.manifest.header.runCount.toNat) :
    report.countRuns index ≤ ((report.manifest.runs.take index).map (·.byteCount.toNat)).sum := by
  induction index with
  | zero => simp [countRuns]
  | succ index ih =>
    let run := report.runs index (by omega)
    have bounded := report.reads.countPrefix_le (IO.userError checkpointIntegrityMismatch)
      (directory.file (.run report.manifest.header.generation index)) run.stamp.byteCount.toNat 0
    rw [report.countRuns_step run.stamped, List.take_add_one, run.stamped]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    exact Nat.add_le_add (ih (by omega)) (by simpa only [runChunks, Nat.zero_add] using bounded)

theorem chunkRequests_le (report : NativeMarkedListingWork seen) :
    report.chunkRequests ≤ report.bytes.size + report.selectedRunBytes + WAL.Boundary.acquisitionLimit := by
  have different : (directory.file .manifest == directory.file .walBoundary) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have paths := congrArg FilePath.toString same
    change (directory.path.toString ++ "/") ++ "MANIFEST" =
      (directory.path.toString ++ "/") ++ "WAL.commit" at paths
    exact (by decide : "MANIFEST" ≠ "WAL.commit") ((String.append_right_inj _).mp paths)
  let file := report.file.observesFile
  have manifestCount : report.manifestChunks ≤ report.bytes.size := by
    have bound := report.reads.countMetadata_le directory (directory.file .manifest) (0, 0)
    simpa [manifestChunks, different, file.stat, file.extent, Except.toOption] using bound
  have markerCount : report.markerChunks ≤ WAL.Boundary.acquisitionLimit := by
    have bound := report.reads.countMetadata_le directory (directory.file .walBoundary) (0, 0)
    simpa only [markerChunks, beq_self_eq_true, ↓reduceIte, Nat.zero_add] using bound
  have runsCount := report.countRuns_le report.manifest.header.runCount.toNat (Nat.le_refl _)
  rw [← (IntegrityCheckpoint.decode_spec report.decoded).2.2, List.take_length] at runsCount
  have runBudget : report.countRuns report.manifest.header.runCount.toNat ≤ report.selectedRunBytes := by
    simpa only [selectedRunBytes, (IntegrityCheckpoint.decode_spec report.decoded).2.2] using runsCount
  exact Nat.add_le_add (Nat.add_le_add manifestCount runBudget) markerCount

end NativeMarkedListingWork

/-- The marked reader finds no manifest at the captured root. The raw
no-follow ENOENT supplies that same optional callback. The selected
marker then uses a temporary descriptor and closes before listing. -/
structure NativeAbsentManifestListingWork (seen : NativeMarkedListingError admission) where
  reads : CheckpointRunChunkReads
  absent : retry.image.directory.active.manifest = none
  canonicalAbsent : admission.view.child admission.root "MANIFEST" = none
  noFollowMissing : ∃ name message, reads.stat (directory.file .manifest) = .error (.noFileOrDirectory name 2 message)
  release : FilePath → List LockReferenceDrop
  selectedMarker : retry.image.directory.active.walBoundary = some seen.marker
  markerFile : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root seen.marker
  markerAvailable : PrefixChunksAvailableUntilEof seen.marker (reads.readChunk markerFile.observesFile.slot.description)
  markerCustody : TemporaryPrefixCustody markerFile.calls seen.atMarker (release (directory.file .walBoundary))
  enteredListing : seen.atListing = seen.atMarker.afterDrops (markerCustody.beforeOpen ++ release (directory.file .walBoundary))
  metadataCallback : seen.readOptional = fun path => discardCache (readTemporaryMetadata reads directory release path) admission.cache

namespace NativeAbsentManifestListingWork

def chunkRequests (report : NativeAbsentManifestListingWork seen) : Nat :=
  recoveryCalls Prod.snd (report.reads.countMetadata directory (directory.file .walBoundary) (0, 0))

private def countedMetadata (report : NativeAbsentManifestListingWork seen) (path : FilePath) :
    EStateM IO.Error CountedOpenState (Option ByteArray) :=
  charged (seen.readOptional path) (recoveryCalls Prod.snd (report.reads.countMetadata directory path (0, 0)))

private def runPrefix (path : FilePath) (count : Nat) : EStateM IO.Error CountedOpenState ByteArray :=
  charged (seen.readRunPrefix path count) 0

theorem readsMissingManifest (report : NativeAbsentManifestListingWork seen) :
    seen.readOptional (directory.file .manifest) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held) := by
  obtain ⟨name, message, missing⟩ := report.noFollowMissing
  simp only [report.metadataCallback, discardCache, readTemporaryMetadata,
    runCachedMetadataRead_missing _ _ _ name message missing]

theorem checkpointAbsent (report : NativeAbsentManifestListingWork seen) :
    seen.checkpoint = none ∧ seen.atMarker = admission.reached := by
  have loaded := seen.loaded
  simp only [readIntegrityCheckpointSized, report.readsMissingManifest, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, EStateM.Result.ok.injEq, Prod.mk.injEq, and_true] at loaded
  exact ⟨loaded.1.symm, loaded.2.symm⟩

theorem manifestChunks_zero (report : NativeAbsentManifestListingWork seen) :
    recoveryCalls Prod.snd (report.reads.countMetadata directory (directory.file .manifest) (0, 0)) = 0 := by
  obtain ⟨_, _, missing⟩ := report.noFollowMissing
  simp [CheckpointRunChunkReads.countMetadata, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    missing, Except.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, recoveryCalls]

/-- The reached ENOENT returns the absent checkpoint at the original
census. Every possible run callback is bypassed with zero chunk requests. -/
theorem countedCheckpoint (report : NativeAbsentManifestListingWork seen) (readRun : CountedRunRead) :
    readIntegrityCheckpointSized directory (report.countedMetadata (directory.file .manifest))
      (fun path => charged (seen.readRunSize path) 0) readRun ((admission.reached, admission.held), 0) =
      .ok seen.checkpoint ((seen.atMarker, admission.held), 0) := by
  simp only [readIntegrityCheckpointSized, countedMetadata, charged, report.readsMissingManifest,
    report.manifestChunks_zero, Nat.zero_add, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    report.checkpointAbsent.1, report.checkpointAbsent.2]

def countedMarked (report : NativeAbsentManifestListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    EStateM IO.Error CountedOpenState Reopened :=
  countedListingWorker (seen := seen) report.countedMetadata (runPrefix (seen := seen)) rest

theorem countedMarked_error (report : NativeAbsentManifestListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    report.countedMarked rest ((admission.reached, admission.held), 0) =
      .error seen.listing.cause ((seen.atListing, admission.held), report.chunkRequests + seen.listing.directoryCalls) := by
  have read := readsListingMarker report.markerFile report.markerAvailable report.markerCustody
    report.enteredListing report.metadataCallback
  apply countedListingWorker_error _ _ rest (report.countedCheckpoint _)
  simp only [countedMetadata, charged, read, Nat.zero_add, chunkRequests]

theorem countedMarked_projects (report : NativeAbsentManifestListingWork seen) (rest : NativeMarkedListingError.Remainder) :
    dropCount (report.countedMarked rest ((admission.reached, admission.held), 0)) =
      seen.marked rest directory (admission.reached, admission.held) := by
  rw [report.countedMarked_error, markedListingError rest]
  rfl

theorem chunkRequests_le (report : NativeAbsentManifestListingWork seen) :
    report.chunkRequests ≤ WAL.Boundary.acquisitionLimit := by
  have bounded := report.reads.countMetadata_le directory (directory.file .walBoundary) (0, 0)
  simpa only [chunkRequests, beq_self_eq_true, ↓reduceIte, Nat.zero_add] using bounded

theorem listingInodes (report : NativeAbsentManifestListingWork seen) : seen.atListing.inode = admission.reached.inode := by
  have reached := congrArg DescriptorInventory.inode report.enteredListing
  change seen.atListing.inode = seen.atMarker.inode at reached
  rw [reached, report.checkpointAbsent.2]

end NativeAbsentManifestListingWork

inductive NativeListingWork (seen : NativeMarkedListingError admission) where
  | present (report : NativeMarkedListingWork seen)
  | absent (report : NativeAbsentManifestListingWork seen)

namespace NativeListingWork

noncomputable def chunkRequests : NativeListingWork seen → Nat
  | .present report => report.chunkRequests
  | .absent report => report.chunkRequests

def selectedRunBytes : NativeListingWork seen → Nat
  | .present report => report.selectedRunBytes
  | .absent _ => 0

def directoryRequests (_report : NativeListingWork seen) : Nat := seen.listing.directoryCalls

theorem listingInodes (report : NativeListingWork seen) : seen.atListing.inode = admission.reached.inode := by
  cases report with
  | present report => exact report.listingInodes
  | absent report => exact report.listingInodes

theorem chunkRequests_le (report : NativeListingWork seen) :
    report.chunkRequests ≤ (retry.image.directory.active.manifest.map ByteArray.size).getD 0 +
      (report.selectedRunBytes + WAL.Boundary.acquisitionLimit) := by
  cases report with
  | present report =>
    simpa only [chunkRequests, selectedRunBytes, report.selected, Option.map_some, Option.getD_some, Nat.add_assoc]
      using report.chunkRequests_le
  | absent report =>
    simpa only [chunkRequests, selectedRunBytes, report.absent, Option.map_none, Option.getD_none, Nat.zero_add]
      using report.chunkRequests_le

end NativeListingWork

end Alvoki.Storage.DiskSession
