import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

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
    (openFrame : ∀ {entryHeap reached handle}, directoryCalls.openDir directory.path entryHeap = .ok handle reached →
      frame entryHeap reached)
    (scanFrame : ∀ handle entryHeap, frame entryHeap (directoryCalls.readDir handle entryHeap).2)
    (closeFrame : ∀ {entryHeap reached handle}, directoryCalls.closeDir handle entryHeap = .ok () reached →
      frame entryHeap reached) :
    frame prepared.atScan seen.reached := by
  have scan := scanFrame seen.descriptor seen.opened
  rw [seen.readRaw] at scan
  exact trans (trans (openFrame seen.openedRaw) scan) (closeFrame seen.closedRaw)

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

/-- Continue the exact checkpoint frame through that worker's checked
listing and ordered seals. The extent probes between them did not move
the heap, and the keeper is reached at its own reported entry. -/
theorem RawHealthyMarkedOpenEffects.framesBeforeKeeper
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (reads : raw.fileCalls.ScopeFrames frame)
    (listed : ∀ {entryHeap reached handle}, raw.directoryCalls.openDir directory.path entryHeap = .ok handle reached →
      frame entryHeap reached)
    (scan : ∀ handle entryHeap, frame entryHeap (raw.directoryCalls.readDir handle entryHeap).2)
    (closed : ∀ {entryHeap reached handle}, raw.directoryCalls.closeDir handle entryHeap = .ok () reached →
      frame entryHeap reached) :
    frame raw.seed.afterPending raw.beforeKeeper := by
  have sealFrame (first count : Nat) {start finish : heap} {bytes : ByteArray}
      (returned : raw.fileCalls.seal (directory.file (.walSegment first)) count start = .ok bytes finish) :
      frame start finish := by
    have read := raw.fileCalls.readWithFrames reads trans (directory.file (.walSegment first)) _
      (fun file => exactReadFrames refl trans selectedWalSpanError (raw.fileCalls.readChunk file)
        (reads.readChunk file) count ByteArray.empty) start
    change frame start (reachedState (raw.fileCalls.seal (directory.file (.walSegment first)) count start)) at read
    simpa only [returned, reachedState] using read
  exact trans (raw.checkpoint.framesScan selected reads refl trans)
    (trans (raw.listing.framesScan frame trans listed scan closed) (raw.seals.framesSeals frame refl trans sealFrame))

end Healthy

end Alvoki.Storage.DiskSession
