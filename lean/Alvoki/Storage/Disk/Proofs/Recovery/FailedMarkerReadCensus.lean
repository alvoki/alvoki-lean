import Alvoki.Storage.Disk.LockCensusOpenAdmission
import Alvoki.Storage.Disk.Proofs.Recovery.HeldMetadataReadObservations

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private abbrev MarkerCursor := Option DescriptorInventory × Nat

private def rawMetadataOpen (reads : CheckpointRunChunkReads) (path : FilePath) :
    EStateM IO.Error MarkerCursor DescriptorSlot := fun cursor =>
  match reads.openRead path with
  | .error cause => .error cause cursor
  | .ok (census, slot, offset) => .ok slot (some census, offset)

private def rawMetadataChunk (reads : CheckpointRunChunkReads) (slot : DescriptorSlot) (count : USize) :
    EStateM IO.Error MarkerCursor ByteArray := fun (opened, offset) =>
  match reads.readChunk slot.description count offset with
  | .ok bytes next => .ok bytes (opened, next)
  | .error cause next => .error cause (opened, next)

private def metadataRead (reads : CheckpointRunChunkReads) (directory : DiskDirectory) (path : FilePath) :
    EStateM IO.Error MarkerCursor (Option ByteArray) :=
  readOptionalCachedOpenFileWith directory path (pure ((reads.stat path).map Prod.fst))
    (rawMetadataOpen reads) (rawMetadataChunk reads)

/-- Keep the census returned by the selected metadata handle and its
reported finalization on both outcomes. A lookup error or missing file
has no opened descriptor to finalize. -/
def readMetadataWithCensus (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (released : FilePath → List LockReferenceDrop) (path : FilePath) :
    EStateM IO.Error CensusOpenState (Option ByteArray) := fun (census, files) =>
  let reached := fun opened => (opened.map (fun openedCensus => openedCensus.afterDrops (released path))).getD census
  match metadataRead reads directory path (none, 0) with
  | .ok bytes (opened, _) => .ok bytes (reached opened, files)
  | .error cause (opened, _) => .error cause (reached opened, files)

private theorem metadataRead_missing (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (path : FilePath) {name message : String}
    (absent : reads.stat path = .error (.noFileOrDirectory name 2 message)) :
    metadataRead reads directory path (none, 0) = .ok none (none, 0) := by
  simp [metadataRead, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    absent, Except.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- A successful lookup selects the marked route. The read-side stat
and successful raw open resolve the same stable marker inode. The first
bounded read returns a positive short fragment. The next request reports
a primitive error, followed by the temporary slot's observed release. -/
structure HeldMarkerChunkFailure {input : FilePath} {directory : DiskDirectory}
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    (admission : CensusOpenAdmissionReports input directory inventory retry) where
  reads : CheckpointRunChunkReads
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  manifestMissing : retry.image.directory.active.manifest = none
  manifestEntry : admission.view.child admission.root "MANIFEST" = none
  manifestProbe : ∃ name message, reads.stat (directory.file .manifest) = .error (.noFileOrDirectory name 2 message)
  statLookup : RunChildLookup admission.root "WAL.commit" admission.view
  openLookup : RunChildLookup admission.root "WAL.commit" admission.view
  metadata : IO.FS.Metadata
  stat : reads.stat (directory.file .walBoundary) = .ok (metadata, admission.view.modelObject statLookup.child)
  regular : metadata.type = .file
  route : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok metadata) (admission.reached, admission.held)
  source : ByteArray
  markerBytes : retry.image.directory.active.walBoundary = some source
  contents : reads.objectBytes (admission.view.modelObject statLookup.child) = some source
  slot : DescriptorSlot
  beforeOpen : List LockReferenceDrop
  free : ∀ old ∈ (admission.reached.afterDrops beforeOpen).slots, old.address ≠ slot.address
  fresh : (admission.reached.afterDrops beforeOpen).references slot.description = []
  openObject : admission.view.modelObject openLookup.child = admission.reached.inode slot.description
  opened : reads.openRead (directory.file .walBoundary) =
    .ok ((admission.reached.afterDrops beforeOpen).insert slot free, slot, 0)
  shortChunk : ByteArray
  next : Nat
  positive : 0 < shortChunk.size
  short : shortChunk.size < WAL.Boundary.acquisitionLimit
  observes : PrefixChunkObserves source (reads.readChunk slot.description)
  first : reads.readChunk slot.description WAL.Boundary.acquisitionLimit.toUSize 0 = .ok shortChunk next
  cause : IO.Error
  failedCursor : Nat
  failed : reads.readChunk slot.description (WAL.Boundary.acquisitionLimit - shortChunk.size).toUSize next =
    .error cause failedCursor
  duringRead : List LockReferenceDrop
  slotRetained : ∀ event ∈ duringRead, event.removes slot.reference = false
  close : LockReferenceDrop
  finalizes : close = slot.closeEvent
  ownerRetained : admission.owner ∈
    (admission.reached.afterDrops (beforeOpen ++ duringRead ++ [close])).slots
  directoryRetained : admission.cached ∈
    (admission.reached.afterDrops (beforeOpen ++ duringRead ++ [close])).slots

namespace HeldMarkerChunkFailure

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

def release (fault : HeldMarkerChunkFailure admission) (path : FilePath) : List LockReferenceDrop :=
  if path = directory.file .walBoundary then fault.duringRead ++ [fault.close] else []

def afterRead (fault : HeldMarkerChunkFailure admission) : DescriptorInventory :=
  admission.reached.afterDrops (fault.beforeOpen ++ fault.duringRead ++ [fault.close])

/-- Both reported lookups resolve the same inode. The first chunk is
from offset zero on its opened description and that description is
live across the reported read interval. -/
theorem custody (fault : HeldMarkerChunkFailure admission) :
    fault.openLookup.child = fault.statLookup.child ∧
    fault.next = fault.shortChunk.size ∧
    fault.shortChunk = fault.source.extract 0 fault.next ∧
    admission.reached.inode fault.slot.description = admission.view.modelObject fault.statLookup.child ∧
    (∀ earlier rest, fault.duringRead = earlier ++ rest →
      fault.slot ∈ (((admission.reached.afterDrops fault.beforeOpen).insert fault.slot fault.free).afterDrops earlier).slots) ∧
    fault.afterRead.references fault.slot.description = [] ∧
    admission.owner ∈ fault.afterRead.slots ∧ admission.cached ∈ fault.afterRead.slots := by
  have bound := fault.statLookup.binds
  rw [fault.statLookup.atRoot, fault.statLookup.atName] at bound
  have same := fault.openLookup.child_eq bound
  obtain ⟨advanced, fragment⟩ := fault.observes WAL.Boundary.acquisitionLimit.toUSize 0 fault.next fault.shortChunk fault.first
  refine ⟨same, by simpa using advanced, fragment, fault.openObject.symm.trans (congrArg _ same), ?_, ?_,
    fault.ownerRetained, fault.directoryRetained⟩
  · intro earlier rest ordered
    refine List.mem_filter.mpr ⟨List.mem_cons_self, List.all_eq_true.mpr fun event member => ?_⟩
    rw [fault.slotRetained event (ordered ▸ List.mem_append_left _ member)]
    rfl
  · unfold afterRead
    rw [List.append_assoc, ← DescriptorInventory.afterDrops_append,
      DescriptorInventory.references_afterDrops, fault.fresh]
    rfl

theorem missingManifest (fault : HeldMarkerChunkFailure admission) :
    readMetadataWithCensus fault.reads directory fault.release (directory.file .manifest) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held) := by
  obtain ⟨name, message, missing⟩ := fault.manifestProbe
  simp [readMetadataWithCensus, metadataRead_missing _ _ _ missing]

private def openedCensus (fault : HeldMarkerChunkFailure admission) : DescriptorInventory :=
  (admission.reached.afterDrops fault.beforeOpen).insert fault.slot fault.free

private theorem rawError (fault : HeldMarkerChunkFailure admission) :
    metadataRead fault.reads directory (directory.file .walBoundary) (none, 0) =
      .error fault.cause (some fault.openedCensus, fault.failedCursor) := by
  let opened := fault.openedCensus
  have first :
      rawMetadataChunk fault.reads fault.slot WAL.Boundary.acquisitionLimit.toUSize (some opened, 0) =
        .ok fault.shortChunk (some opened, fault.next) := by simp [rawMetadataChunk, fault.first]
  have second :
      rawMetadataChunk fault.reads fault.slot (WAL.Boundary.acquisitionLimit - fault.shortChunk.size).toUSize
        (some opened, fault.next) = .error fault.cause (some opened, fault.failedCursor) := by
    simp [rawMetadataChunk, fault.failed]
  have read := readPrefixUntilEofWith_shortThenError (IO.userError "invalid WAL boundary length") _
    fault.positive fault.short (bytes := ByteArray.empty) first second
  simp [metadataRead, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata, fault.stat,
    fault.regular, rawMetadataOpen, fault.opened, openedCensus, Except.map, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, show (IO.FS.FileType.file == .file) = true from rfl]
  exact congrArg
    (fun outcome : EStateM.Result IO.Error MarkerCursor ByteArray =>
      EStateM.bind (fun _ => outcome) (fun bytes => EStateM.pure (some bytes)) (none, 0)) read

theorem returnsError (fault : HeldMarkerChunkFailure admission) :
    readMetadataWithCensus fault.reads directory fault.release (directory.file .walBoundary) (admission.reached, admission.held) =
      .error fault.cause (fault.afterRead, admission.held) := by
  unfold readMetadataWithCensus
  rw [fault.rawError]
  have closed : fault.openedCensus.afterDrops (fault.release (directory.file .walBoundary)) = fault.afterRead := by
    rw [release, ite_eq_left rfl, fault.finalizes]
    unfold openedCensus afterRead
    rw [DescriptorInventory.insert_thenClose, DescriptorInventory.afterDrops_append, List.append_assoc, fault.finalizes]
  simpa only [Option.map_some, Option.getD_some] using congrArg
    (fun census => EStateM.Result.error fault.cause (census, admission.held)) closed

end HeldMarkerChunkFailure

/-- Callbacks after a successful metadata prefix. Their values remain
arbitrary here because the marked route cannot reach them on this error. -/
structure RejectedMarkerTail where
  readRunSize : FilePath → EStateM IO.Error FileImage Nat
  readRunPrefix : FilePath → Nat → EStateM IO.Error FileImage ByteArray
  list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry)
  lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata)
  readSeal : FilePath → Nat → EStateM IO.Error FileImage ByteArray
  readKeeper : FilePath → Nat → Nat → EStateM IO.Error FileImage ByteArray
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

private def liftFile {result : Type} (action : EStateM IO.Error FileImage result) :
    EStateM IO.Error CensusOpenState result := fun (census, before) =>
  match action before.image with
  | .ok value after => .ok value (census, { before with image := after })
  | .error cause after => .error cause (census, { before with image := after })

/-- The shared held marked branches pass the reached metadata and run
callbacks into the original bounded reader and its original continuations. -/
def CensusOpenAdmissionReports.recoverMarkedWithReads
    (admission : CensusOpenAdmissionReports input directory inventory retry)
    (readOptional : DiskDirectory → FilePath → EStateM IO.Error CensusOpenState (Option ByteArray))
    (readSize : FilePath → EStateM IO.Error CensusOpenState Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray) (tail : RejectedMarkerTail)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession)
    (resolved : DiskDirectory) (owner : DescriptorSlot) (cache : CensusDirectoryCache) :
    EStateM IO.Error CensusOpenState SegmentedSession := do
  let opened ← recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (admission.lookup (resolved.file .wal))))
    (optionalMetadataWith (admission.lookup (resolved.file .walBoundary)))
    (reopenMarkedBoundedWithCachedExtents resolved (readOptional resolved) readSize readPrefix
      (fun path => liftFile (tail.list path)) (fun path => liftFile (tail.lstat path))
      (fun path count => liftFile (tail.readSeal path count))
      (fun path count size => liftFile (tail.readKeeper path count size))
      (fun path => liftFile (tail.removeFile path)) (fun path bytes => liftFile (tail.write path bytes))
      (fun paths => liftFile (tail.sync paths)) (fun source target => liftFile (tail.renameFile source target)))
    (bootstrap resolved cache)
  install resolved owner cache opened

theorem CensusOpenAdmissionReports.run_reachesReadCleanup
    (admission : CensusOpenAdmissionReports input directory inventory retry)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache →
      EStateM IO.Error CensusOpenState SegmentedSession)
    {cause : IO.Error} {reached : DescriptorInventory}
    (failed : recover directory admission.owner admission.cache (admission.reached, admission.held) =
      .error cause (reached, admission.held)) :
    admission.run recover =
      match admission.unlock admission.owner () (reached, admission.held) with
      | .ok () after => .error cause after
      | .error cleanup after => .error cleanup after := by
  rw [admission.run_reachesRecovery]
  simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, failed, Bind.bind, EStateM.bind,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.Backtrackable.restore, EStateM.dummyRestore]
  cases admission.unlock admission.owner () (reached, admission.held) with
  | ok answer reached => cases answer; rfl
  | error error reached => rfl

namespace HeldMarkerChunkFailure

private def readFiles (fault : HeldMarkerChunkFailure admission) (path : FilePath) :
    EStateM IO.Error FileImage (Option ByteArray) := fun files =>
  match metadataRead fault.reads directory path (none, 0) with
  | .ok bytes _ => .ok bytes files
  | .error cause _ => .error cause files

/-- The actual held marked schedule, with the metadata read census. -/
def recover (fault : HeldMarkerChunkFailure admission) (tail : RejectedMarkerTail)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :=
  admission.recoverMarkedWithReads (readMetadataWithCensus fault.reads · fault.release)
    (fun path => liftFile (tail.readRunSize path)) (fun path count => liftFile (tail.readRunPrefix path count))
    tail bootstrap install

/-- The raw marker read fails after the empty checkpoint is reached.
The bounded worker returns the exact diagnostic and census directly to
the existing unlock handler. The subsequent operations are unreachable. -/
theorem reachesCleanup (fault : HeldMarkerChunkFailure admission) (tail : RejectedMarkerTail)
    (bootstrap install) :
    admission.run (fault.recover tail bootstrap install) =
      match admission.unlock admission.owner () (fault.afterRead, admission.held) with
      | .ok () after => .error fault.cause after
      | .error cleanup after => .error cleanup after := by
  apply admission.run_reachesReadCleanup
  have selected : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some fault.metadata) (admission.reached, admission.held) := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, fault.route, Pure.pure, EStateM.pure]
  simp only [recover, CensusOpenAdmissionReports.recoverMarkedWithReads, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, readIntegrityCheckpointSized,
    Bind.bind, EStateM.bind, fault.flat, selected, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, fault.missingManifest, fault.returnsError]

private def attempt (fault : HeldMarkerChunkFailure admission) (tail : RejectedMarkerTail)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (localFlock : unlock.LocalFlock) : CachedOpenAttempt directory retry where
  descriptor := admission.owner.description
  nextRef := 0
  acquisition := acquisition
  unlock := unlock
  localUnlock := localFlock
  readOptional := fault.readFiles
  readRunSize := tail.readRunSize
  readRunPrefix := tail.readRunPrefix
  list := tail.list
  lstat := tail.lstat
  readSeal := tail.readSeal
  readKeeper := tail.readKeeper
  removeFile := tail.removeFile
  write := tail.write
  sync := tail.sync
  renameFile := tail.renameFile

/-- The same primitive reads certify the file-only rejection in the
shared retry model. That projection keeps the original files. -/
def certifies (fault : HeldMarkerChunkFailure admission) (tail : RejectedMarkerTail)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (localFlock : unlock.LocalFlock) : CachedOpenRejection directory retry := by
  let projected := fault.attempt tail acquisition unlock localFlock
  have absent : projected.readOptional (directory.file .manifest) retry.image = .ok none retry.image := by
    obtain ⟨_, _, missing⟩ := fault.manifestProbe
    change fault.readFiles (directory.file .manifest) retry.image = _
    simp only [readFiles, metadataRead_missing _ _ _ missing]
  apply CachedOpenRejection.ofMarkerReadError projected (checkpoint := none) (cause := fault.cause)
  · simp [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, absent, Pure.pure, EStateM.pure]
  · change fault.readFiles (directory.file .walBoundary) retry.image = _
    simp only [readFiles, fault.rawError]

end HeldMarkerChunkFailure

private def readCleanupResult (admission : CensusOpenAdmissionReports input directory inventory retry)
    (reached : DescriptorInventory) (outcome : UnlockReport) :
    EStateM.Result IO.Error CensusOpenState PUnit :=
  match outcome with
  | .success => .ok () (reached, ⟨retry.image, retry.owners.set (directory.file .lock) none⟩)
  | .failure cause _ => .error cause (reached, admission.held)

/-- The same live lock slot receives the native cleanup callback once
the read handles have finalized. Local Linux flock errors keep the lock
description live and take precedence over the read diagnostic. -/
structure ReportedReadCleanup (admission : CensusOpenAdmissionReports input directory inventory retry)
    (reached : DescriptorInventory) where
  outcome : UnlockReport
  localFlock : outcome.LocalFlock
  returned : admission.unlock admission.owner () (reached, admission.held) = readCleanupResult admission reached outcome

theorem ReportedReadCleanup.matchesRejection {reached : DescriptorInventory}
    (cleanup : ReportedReadCleanup admission reached) (rejected : CachedOpenRejection directory retry)
    (owner : rejected.attempt.descriptor = admission.owner.description)
    (reported : rejected.attempt.unlock = cleanup.outcome) :
    (match admission.unlock admission.owner () (reached, admission.held) with
    | .ok () after => .error rejected.cause after
    | .error error after => .error error after : EStateM.Result IO.Error CensusOpenState SegmentedSession) =
    .error rejected.error (reached, rejected.after) := by
  rw [cleanup.returned]
  simp only [CachedOpenRejection.after, CachedOpenRejection.error, CachedOpenAttempt.cleanupError,
    owner, reported]
  cases cleanup.outcome <;> rfl

namespace HeldMarkerChunkFailure

abbrev Cleanup (fault : HeldMarkerChunkFailure admission) := ReportedReadCleanup admission fault.afterRead

/-- The exact visible file state of the native failed open is the common
retry prefix's rejection endpoint. Its descriptor census comes from the
same selected marker's open and reported temporary close. -/
theorem continues (fault : HeldMarkerChunkFailure admission) (tail : RejectedMarkerTail)
    (cleanup : fault.Cleanup) (bootstrap install)
    {keeper : Nat} {origin : LockedFileState FileImage}
    (earlier : ReportedReopenPrefix directory keeper origin retry)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) :
    let rejected := fault.certifies tail acquisition cleanup.outcome cleanup.localFlock
    admission.run (fault.recover tail bootstrap install) = .error rejected.error (fault.afterRead, rejected.after) ∧
      rejected.after.image = retry.image ∧
      ReportedReopenPrefix directory keeper origin rejected.after ∧
      fault.afterRead.references fault.slot.description = [] ∧
      admission.owner ∈ fault.afterRead.slots ∧ admission.cached ∈ fault.afterRead.slots := by
  intro rejected
  have custody := fault.custody
  refine ⟨?_, rejected.attempt.cleanupError_keepsFiles rejected.cause retry.image, earlier.rejected rejected,
    custody.2.2.2.2.2.1, fault.ownerRetained, fault.directoryRetained⟩
  rw [fault.reachesCleanup tail bootstrap install]
  exact cleanup.matchesRejection rejected rfl rfl

end HeldMarkerChunkFailure

end Alvoki.Storage.DiskSession
