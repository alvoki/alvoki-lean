import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

/-- The independent projections a read-only callback frames. The names
also cover the later alias check. Live bytes are needed only for the
one keeper that the selected plan will open. -/
structure MarkedOpenReadFrame (directory : DiskDirectory) (protectedPaths : FilePath → Prop)
    (keeperPath : FilePath) (before after : CheckpointStorageObservation)
    (beforeBytes afterBytes : Nat → ByteArray) : Prop where
  durable : before.Frames protectedPaths after
  names : ∀ path, (path = directory.path ∨ ∃ file, path = directory.file file) →
    after.files.names path = before.files.names path
  keeper : (CheckpointSurvivingFiles.mk before.files.names fun inode => [beforeBytes inode]).Frames
    (· = keeperPath) ⟨after.files.names, fun inode => [afterBytes inode]⟩

theorem MarkedOpenReadFrame.refl (directory : DiskDirectory) (protectedPaths : FilePath → Prop)
    (keeperPath : FilePath) (storage : CheckpointStorageObservation) (bytes : Nat → ByteArray) :
    MarkedOpenReadFrame directory protectedPaths keeperPath storage storage bytes bytes :=
  ⟨.refl _ _, fun _ _ => rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

theorem MarkedOpenReadFrame.trans {directory : DiskDirectory} {protectedPaths : FilePath → Prop}
    {keeperPath : FilePath} {before middle after : CheckpointStorageObservation}
    {beforeBytes middleBytes afterBytes : Nat → ByteArray}
    (first : MarkedOpenReadFrame directory protectedPaths keeperPath before middle beforeBytes middleBytes)
    (second : MarkedOpenReadFrame directory protectedPaths keeperPath middle after middleBytes afterBytes) :
    MarkedOpenReadFrame directory protectedPaths keeperPath before after beforeBytes afterBytes :=
  ⟨first.durable.trans second.durable, fun path inside => (second.names path inside).trans (first.names path inside),
    first.keeper.trans second.keeper⟩

structure MarkedDirectoryReadCalls.ScopeFrames {heap stream : Type}
    (calls : MarkedDirectoryReadCalls heap stream) (directory : DiskDirectory)
    (frame : heap → heap → Prop) : Prop where
  openDir : ∀ {entry reached handle}, calls.openDir directory.path entry = .ok handle reached → frame entry reached
  readDir : ∀ handle entry, frame entry (calls.readDir handle entry).2
  closeDir : ∀ {entry reached handle}, calls.closeDir handle entry = .ok () reached → frame entry reached

section Listing

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}

variable {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot}

/-- Apply a scoped frame through the actual directory stream's open,
scan and close. Local laws can frame both bytes and parent settlement. -/
theorem MarkedDirectoryReadReport.framesScan
    (seen : MarkedDirectoryReadReport prepared directoryCalls slotOf)
    (frame : heap → heap → Prop) (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (effects : directoryCalls.ScopeFrames directory frame) :
    frame prepared.atScan seen.reached := by
  have scan := effects.readDir seen.descriptor seen.opened
  rw [seen.readRaw] at scan
  exact trans (trans (effects.openDir seen.openedRaw) scan) (effects.closeDir seen.closedRaw)

/-- Each selected seal read carries the same scope through its actual
returned heap, including the release. The keeper is still unread. -/
theorem MarkedSealReadChain.framesSeals {released : FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)} {initial : DescriptorInventory} {drops : List LockReferenceDrop}
    {physical : CapturedSealReadChain reads released required initial drops} {before reached : heap}
    (observed : MarkedSealReadChain seed fileCalls physical before reached)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (one : ∀ first count {start finish bytes},
      fileCalls.seal (directory.file (.walSegment first)) count start = .ok bytes finish → frame start finish) :
    frame before reached := by
  induction observed with
  | keeper => exact refl _
  | sealed _ _ _ _ raw _ rest =>
    exact trans (one _ _ raw.returns.1) rest

end Listing

section Healthy

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit} {stream : Type}

variable {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}

/-- Carry the frame to the checked listing and separately through the
ordered seal reads to the keeper entry. The extent probes did not move
the heap. The split exposes the point where the link census was read. -/
theorem RawHealthyMarkedOpenEffects.framesReadPrefix
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (reads : raw.fileCalls.ScopeFrames frame)
    (listing : raw.directoryCalls.ScopeFrames directory frame) :
    frame raw.seed.afterPending raw.listing.reached ∧ frame raw.listing.reached raw.beforeKeeper := by
  have sealFrame (first count : Nat) {start finish : heap} {bytes : ByteArray}
      (returned : raw.fileCalls.seal (directory.file (.walSegment first)) count start = .ok bytes finish) :
      frame start finish := by
    have read := raw.fileCalls.readWithFrames reads trans (directory.file (.walSegment first)) _
      (fun file => exactReadFrames refl trans selectedWalSpanError (raw.fileCalls.readChunk file)
        (reads.readChunk file) count ByteArray.empty) start
    change frame start (reachedState (raw.fileCalls.seal (directory.file (.walSegment first)) count start)) at read
    simpa only [returned, reachedState] using read
  exact ⟨trans (raw.checkpoint.framesScan selected reads refl trans)
    (raw.listing.framesScan frame trans listing), raw.seals.framesSeals frame refl trans sealFrame⟩

end Healthy

end Alvoki.Storage.DiskSession
