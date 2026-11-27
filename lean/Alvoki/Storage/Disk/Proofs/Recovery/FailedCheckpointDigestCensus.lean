import Alvoki.Storage.Disk.Proofs.Session.CapturedCheckpointReadCensus
import Alvoki.Storage.Disk.Proofs.Recovery.FailedMarkerReadCensus
import Alvoki.Storage.Disk.CachedCheckpointExtentRetry

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

private def measuredSize (reads : CheckpointRunChunkReads) (path : FilePath) : Except IO.Error Nat := do
  let (metadata, _) ← reads.stat path
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  return metadata.byteSize.toNat

/-- A selected run may have the exact extent from its stamp and still
fail digest verification. Its stat and open resolve the same child.
The temporary descriptions close in the manifest reader's actual order. -/
structure ReachedDigestRun (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (view : DirectoryReadNamespace) (root : DeviceInode) (manifest : IntegrityCheckpoint)
    (index : Nat) (bytes : ByteArray) (initial : DescriptorInventory) (released : List LockReferenceDrop) where
  stamp : RunIntegrity
  stamped : manifest.runs[index]? = some stamp
  extent : bytes.size = stamp.byteCount.toNat
  fits : stamp.byteCount.toNat < USize.size
  object : DeviceInode
  bound : view.child root (renderRunFileName manifest.header.generation index) = some object
  contents : reads.objectBytes (view.modelObject object) = some bytes
  file : RunChunkPathReport reads (directory.file (.run manifest.header.generation index))
    (renderRunFileName manifest.header.generation index) root view
  custody : TemporaryPrefixCustody file initial released

namespace ReachedDigestRun

variable {reads directory view root manifest index bytes initial released}

theorem measures (run : ReachedDigestRun reads directory view root manifest index bytes initial released) :
    measuredSize reads (directory.file (.run manifest.header.generation index)) = .ok run.stamp.byteCount.toNat := by
  let observed := run.file.observesFile run.bound run.contents
  simp [measuredSize, observed.stat, observed.regular, observed.extent, run.extent, Bind.bind, Except.bind,
    Pure.pure, Except.pure, show (IO.FS.FileType.file == .file) = true from rfl]

theorem suppliesPrefix (run : ReachedDigestRun reads directory view root manifest index bytes initial released) :
    reads.readPrefix (directory.file (.run manifest.header.generation index)) run.stamp.byteCount.toNat = .ok bytes := by
  let observed := run.file.observesFile run.bound run.contents
  simpa only [run.extent] using observed.readExact (run.extent.symm ▸ run.fits)

end ReachedDigestRun

/-- Every actually selected run has reached regular-file no-follow stat,
raw open, exact successful reads and temporary close. The designated run
begins with a positive short chunk and has a mismatched complete digest. -/
structure HeldCheckpointDigestFailure {input : FilePath} {directory : DiskDirectory}
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    (admission : CensusOpenAdmissionReports input directory inventory retry) where
  reads : CheckpointRunChunkReads
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  marker : IO.FS.Metadata
  route : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  bytes : ByteArray
  binding : retry.image.directory.active.manifest = some bytes
  manifest : IntegrityCheckpoint
  decoded : IntegrityCheckpoint.decode bytes = .ok manifest
  file : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes
  fits : IntegrityCheckpoint.acquisitionSize bytes < USize.size
  manifestRelease : FilePath → List LockReferenceDrop
  manifestCustody : TemporaryPrefixCustody file.calls admission.reached (manifestRelease (directory.file .manifest))
  payload : Nat → ByteArray
  runRelease : FilePath → List LockReferenceDrop
  events : Nat → List LockReferenceDrop
  runs : ∀ index < manifest.header.runCount.toNat,
    ReachedDigestRun reads directory admission.view admission.root manifest index (payload index)
      ((admission.reached.afterDrops (manifestCustody.beforeOpen ++ manifestRelease (directory.file .manifest))).afterDrops
        (runReadDrops events index)) (runRelease (directory.file (.run manifest.header.generation index)))
  chronological : ∀ index (within : index < manifest.header.runCount.toNat),
    events index = (runs index within).custody.beforeOpen ++ runRelease (directory.file (.run manifest.header.generation index))
  index : Nat
  within : index < manifest.header.runCount.toNat
  chunk : ByteArray
  next : Nat
  positive : 0 < chunk.size
  short : chunk.size < (payload index).size
  first : reads.readChunk (runs index within).file.slot.description
    (runs index within).stamp.byteCount.toNat.toUSize 0 = .ok chunk next
  digest : checksumRun (payload index) ≠ (runs index within).stamp.checksum
  ownerRetained : admission.owner ∈
    ((admission.reached.afterDrops (manifestCustody.beforeOpen ++ manifestRelease (directory.file .manifest))).afterDrops
      (runReadDrops events manifest.header.runCount.toNat)).slots
  directoryRetained : admission.cached ∈
    ((admission.reached.afterDrops (manifestCustody.beforeOpen ++ manifestRelease (directory.file .manifest))).afterDrops
      (runReadDrops events manifest.header.runCount.toNat)).slots

namespace HeldCheckpointDigestFailure

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

def atIndex (fault : HeldCheckpointDigestFailure admission) (index : Nat) : DescriptorInventory :=
  (admission.reached.afterDrops (fault.manifestCustody.beforeOpen ++ fault.manifestRelease (directory.file .manifest))).afterDrops
    (runReadDrops fault.events index)

def afterRead (fault : HeldCheckpointDigestFailure admission) : DescriptorInventory :=
  fault.atIndex fault.manifest.header.runCount.toNat

private def ignoreCache {result : Type} (cache : CensusDirectoryCache)
    (action : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) result) :
    EStateM IO.Error CensusOpenState result := fun state =>
  match action (cache, state) with
  | .ok value (_, after) => .ok value after
  | .error cause (_, after) => .error cause after

def readOptional (fault : HeldCheckpointDigestFailure admission) (resolved : DiskDirectory) (path : FilePath) :
    EStateM IO.Error CensusOpenState (Option ByteArray) :=
  ignoreCache admission.cache (readTemporaryMetadata fault.reads resolved fault.manifestRelease path)

def readSize (fault : HeldCheckpointDigestFailure admission) (path : FilePath) : EStateM IO.Error CensusOpenState Nat :=
  liftExcept (measuredSize fault.reads path)

def readPrefix (fault : HeldCheckpointDigestFailure admission) (path : FilePath) (count : Nat) :
    EStateM IO.Error CensusOpenState ByteArray :=
  ignoreCache admission.cache (readTemporaryPrefix fault.reads (IO.userError checkpointIntegrityMismatch)
    fault.runRelease path count)

private theorem manifestBytes (fault : HeldCheckpointDigestFailure admission) :
    runCachedMetadataRead fault.reads directory (directory.file .manifest) 0 =
      .ok (some fault.bytes) (IntegrityCheckpoint.acquisitionSize fault.bytes) := by
  have same := fault.file.manifestPrefix fault.fits
  rwa [IntegrityCheckpoint.acquisitionPrefix_eq_of_decode fault.decoded] at same

theorem readsManifest (fault : HeldCheckpointDigestFailure admission) :
    fault.readOptional directory (directory.file .manifest) (admission.reached, admission.held) =
      .ok (some fault.bytes) (fault.atIndex 0, admission.held) := by
  have reached := fault.manifestCustody.readMetadata fault.manifestBytes admission.cache admission.held
  have noDrops : ∀ census : DescriptorInventory, census.afterDrops [] = census := by
    intro census
    cases census
    simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
  simp only [readOptional, ignoreCache, reached, atIndex, runReadDrops, noDrops]

theorem readsRuns (fault : HeldCheckpointDigestFailure admission) :
    readIntegrityRunBytesSized directory fault.manifest fault.readSize fault.readPrefix
      (fault.atIndex 0, admission.held) =
    .ok ((List.range fault.manifest.header.runCount.toNat).map fault.payload) (fault.afterRead, admission.held) := by
  let state := fun index => (fault.atIndex index, admission.held)
  apply readIntegrityRunBytesSized_effects directory fault.manifest fault.readSize fault.readPrefix state fault.payload
  intro index within
  let run := fault.runs index within
  refine ⟨run.stamp, run.stamped, run.fits, run.extent, ?_, ?_⟩
  · simp [readSize, run.measures, liftExcept, Pure.pure, EStateM.pure]
  · have data := run.custody.readPrefix (IO.userError checkpointIntegrityMismatch) run.bound run.contents
      (run.extent.symm ▸ run.fits) admission.cache admission.held
    have reached : (fault.atIndex index).afterDrops
        (run.custody.beforeOpen ++ fault.runRelease (directory.file (.run fault.manifest.header.generation index))) =
          fault.atIndex (index + 1) := by
      rw [atIndex, atIndex, runReadDrops, fault.chronological index within, DescriptorInventory.afterDrops_append]
    rw [run.extent] at data
    change readTemporaryPrefix fault.reads (IO.userError checkpointIntegrityMismatch) fault.runRelease
      (directory.file (.run fault.manifest.header.generation index)) run.stamp.byteCount.toNat
      (admission.cache, fault.atIndex index, admission.held) =
      .ok (fault.payload index) (admission.cache, (fault.atIndex index).afterDrops _, admission.held) at data
    simp only [readPrefix, ignoreCache, state, data, reached]

/-- The designated run's first fragment comes from its canonical inode
and its raw description is live during each reported read interval. -/
theorem corruptRunCustody (fault : HeldCheckpointDigestFailure admission) :
    let run := fault.runs fault.index fault.within
    run.file.openLookup.child = run.file.statLookup.child ∧
    fault.next = fault.chunk.size ∧
    fault.chunk = (fault.payload fault.index).extract 0 fault.next ∧
    (∀ earlier remaining, run.custody.beforeClose = earlier ++ remaining →
      run.file.slot ∈ (run.file.inventory.afterDrops earlier).slots) ∧
    DescriptorInventory.references (run.file.inventory.afterDrops
      (fault.runRelease (directory.file (.run fault.manifest.header.generation fault.index))))
      run.file.slot.description = [] := by
  intro run
  let observed := run.file.observesFile run.bound run.contents
  have contents := observed.sameObject.symm ▸ observed.contents
  obtain ⟨next, fragment⟩ := (observed.observes _ contents) _ _ _ _ fault.first
  exact ⟨(run.file.openLookup.child_eq run.bound).trans (run.file.statLookup.child_eq run.bound).symm,
    by simpa using next, fragment, fun _ _ ordered => run.custody.liveAtRead ordered, run.custody.closes.2⟩

theorem rejectsDigest (fault : HeldCheckpointDigestFailure admission) :
    readIntegrityCheckpointSized directory (fault.readOptional directory (directory.file .manifest))
      fault.readSize fault.readPrefix (admission.reached, admission.held) =
    .error (IO.userError checkpointIntegrityMismatch) (fault.afterRead, admission.held) := by
  let files := (List.range fault.manifest.header.runCount.toNat).map fault.payload
  have atIndex : files[fault.index]? = some (fault.payload fault.index) := by
    simp [files, fault.within]
  have rejected := IntegrityCheckpoint.rejects_run (fault.runs fault.index fault.within).stamped atIndex (.inr fault.digest)
  have loadFailed : loadIntegrityRunSet fault.manifest files = .error checkpointIntegrityMismatch := by
    simp [loadIntegrityRunSet, rejected]
  simp [readIntegrityCheckpointSized, fault.readsManifest, fault.decoded, fault.readsRuns, files, loadFailed,
    Bind.bind, EStateM.bind, liftExcept, Except.mapError, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    Pure.pure, EStateM.pure]

/-- Run the original marked schedule against the exact selected run reads. -/
def recover (fault : HeldCheckpointDigestFailure admission) (tail : RejectedMarkerTail)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :=
  admission.recoverMarkedWithReads fault.readOptional fault.readSize fault.readPrefix tail bootstrap install

/-- Digest verification fails before the marker payload or any WAL
or repair callback. The shared opener invokes the same held unlock. -/
theorem reachesCleanup (fault : HeldCheckpointDigestFailure admission) (tail : RejectedMarkerTail)
    (bootstrap install) :
    admission.run (fault.recover tail bootstrap install) =
      match admission.unlock admission.owner () (fault.afterRead, admission.held) with
      | .ok () after => .error (IO.userError checkpointIntegrityMismatch) after
      | .error cleanup after => .error cleanup after := by
  apply admission.run_reachesReadCleanup
  have selected : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some fault.marker) (admission.reached, admission.held) := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, fault.route, Pure.pure, EStateM.pure]
  simp only [recover, CensusOpenAdmissionReports.recoverMarkedWithReads, recoverSegmentedWalWith,
    rejectFlatWalWith, reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders,
    Bind.bind, EStateM.bind, fault.flat, selected, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, fault.rejectsDigest]

private def attempt (fault : HeldCheckpointDigestFailure admission) (tail : RejectedMarkerTail)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (localFlock : unlock.LocalFlock) : CachedOpenAttempt directory retry where
  descriptor := admission.owner.description
  nextRef := 0
  acquisition := acquisition
  unlock := unlock
  localUnlock := localFlock
  readOptional := fun path => liftExcept (cachedMetadataReadResult (runCachedMetadataRead fault.reads directory path 0))
  readRunSize := fun path => liftExcept (measuredSize fault.reads path)
  readRunPrefix := fun path count => liftExcept (fault.reads.readPrefix path count)
  list := tail.list
  lstat := tail.lstat
  readSeal := tail.readSeal
  readKeeper := tail.readKeeper
  removeFile := tail.removeFile
  write := tail.write
  sync := tail.sync
  renameFile := tail.renameFile

/-- The same raw reads certify the existing file-only rejection rule.
The failed physical operation remains tied to the native census. -/
def certifies (fault : HeldCheckpointDigestFailure admission) (tail : RejectedMarkerTail)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (localFlock : unlock.LocalFlock) : CachedOpenRejection directory retry := by
  let actual := fault.attempt tail acquisition unlock localFlock
  let manifest : actual.CheckpointManifestRead := ⟨fault.bytes, fault.binding, by
    change liftExcept (m := EStateM IO.Error FileImage)
      (cachedMetadataReadResult (runCachedMetadataRead fault.reads directory (directory.file .manifest) 0))
      retry.image = _
    simp [fault.manifestBytes, cachedMetadataReadResult, liftExcept, Pure.pure, EStateM.pure], fault.manifest, fault.decoded⟩
  have reads : manifest.RunReads manifest.manifest.header.runCount.toNat fault.payload := by
    intro index within
    let run := fault.runs index within
    refine ⟨run.stamp, run.stamped, run.fits, run.extent, ?_, ?_⟩
    · change liftExcept (m := EStateM IO.Error FileImage)
        (measuredSize fault.reads (directory.file (.run fault.manifest.header.generation index)))
        retry.image = _
      simp [run.measures, liftExcept, Pure.pure, EStateM.pure]
    · change liftExcept (m := EStateM IO.Error FileImage)
        (fault.reads.readPrefix (directory.file (.run fault.manifest.header.generation index))
        run.stamp.byteCount.toNat) retry.image = _
      simp [run.suppliesPrefix, liftExcept, Pure.pure, EStateM.pure]
  exact CachedOpenRejection.ofCheckpointRunDigest manifest fault.payload reads fault.within
    (fault.runs fault.index fault.within).stamped fault.digest

/-- The native rejection returns with the census after the ordered
manifest and run reads. The common failed-reopen prefix keeps the
same files and uses the exact cleanup diagnostic and owner. -/
theorem continues (fault : HeldCheckpointDigestFailure admission) (tail : RejectedMarkerTail)
    (cleanup : ReportedReadCleanup admission fault.afterRead) (bootstrap install)
    {keeper : Nat} {origin : LockedFileState FileImage}
    (earlier : ReportedReopenPrefix directory keeper origin retry)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) :
    let rejected := fault.certifies tail acquisition cleanup.outcome cleanup.localFlock
    admission.run (fault.recover tail bootstrap install) = .error rejected.error (fault.afterRead, rejected.after) ∧
      rejected.after.image = retry.image ∧
      ReportedReopenPrefix directory keeper origin rejected.after ∧
      admission.owner ∈ fault.afterRead.slots ∧ admission.cached ∈ fault.afterRead.slots := by
  intro rejected
  refine ⟨?_, rejected.attempt.cleanupError_keepsFiles rejected.cause retry.image, earlier.rejected rejected,
    fault.ownerRetained, fault.directoryRetained⟩
  rw [fault.reachesCleanup tail bootstrap install]
  exact cleanup.matchesRejection rejected rfl rfl

end HeldCheckpointDigestFailure

end Alvoki.Storage.DiskSession
