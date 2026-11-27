import Alvoki.Storage.Disk.NativeMarkedScanFrame

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

/-- Reading a longer keeper leaves through the temporary handle's release.
The frame need only cover read operations and that release. -/
theorem MarkedTemporaryReadCalls.longKeeperReadFrames {heap : Type} (calls : MarkedTemporaryReadCalls heap)
    {frame : heap → heap → Prop} (effects : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (path : FilePath) {count physical : Nat} {before after : heap} {bytes : ByteArray}
    (longer : count < physical)
    (returned : calls.readKeeperWithRelease remember path count physical before = .ok bytes after) :
    frame before after := by
  obtain ⟨file, opened, read, _, _, acquired, payload, finalized⟩ :=
    calls.readKeeperWithRelease_ok remember path count physical returned
  obtain aligned | ⟨_, released⟩ := finalized
  · exact (Nat.ne_of_lt longer aligned.1).elim
  · let error := IO.userError "short or oversized WAL keeper read"
    let body := fun file => readExactPrefixWith error (calls.readChunk file) count .empty
    have longerRead : calls.readWith path body before = .ok bytes after := by
      simp only [MarkedTemporaryReadCalls.readWith, acquired, body, error, payload, dataErrorDropState, released]
    have kept := calls.readWithFrames effects trans path body (calls.exactPrefixFrames refl trans error count) before
    change frame before (reachedState (calls.readWith path body before)) at kept
    simpa only [longerRead, reachedState] using kept

section FromAllocation

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls} {slotOf : heap → stream → DescriptorSlot}

/-- The checkpoint, listing and seal chain establish the cache and descriptor
census at keeper entry. The longer keeper need only preserve the selected fact. -/
theorem MarkedDirectoryReadReport.invariantAfterLongKeeper
    (listing : MarkedDirectoryReadReport prepared directoryCalls slotOf)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    {beforeKeeper afterKeeper : heap}
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (invariant : heap → Prop)
    (establish : view.descriptors beforeKeeper = keeper.atOpen →
      MarkedReadCacheFrame seed seed.afterPending beforeKeeper → invariant beforeKeeper)
    (readEffects : fileCalls.ScopeFrames (fun before after => invariant before → invariant after))
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (longer : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (read : fileCalls.readKeeperWithRelease remember (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper =
        .ok layout.keeper.bytes afterKeeper) :
    invariant afterKeeper := by
  obtain ⟨_, _, _, _, start, _, _, _⟩ := prepared.reachesScan selected (fun _ _ => pure (⟨[], []⟩, 0))
  obtain ⟨_, census, _, _, listed⟩ := listing.returns
  obtain ⟨_, _, sealedReads, afterSeals⟩ := seals.reaches census
  have keeperRead := fileCalls.longKeeperReadFrames readEffects (fun _ => id)
    (fun first last => last ∘ first) remember _ longer read
  exact keeperRead (establish afterSeals ((start.trans listed).trans sealedReads))

end FromAllocation

section Clearing

variable {heap image : Type} (view : OpenCloseHeapView heap image)
  (calls : AlignedKeeperCacheCallbacks heap) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
  (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)

/-- Clearing the actual singleton stage entry can only discard a
reference to that inode. A local drop law and name frame then preserve
the live bytes of every protected inode. -/
theorem AlignedKeeperCacheCallbacks.clearsOnlyStagedKeeper
    {staged loaded consumed : heap} {path : FilePath} {file : IO.FS.Handle} {slot : DescriptorSlot} {inode : Nat}
    {entries : List (FilePath × IO.FS.Handle)} {scope : FilePath → Prop}
    (recorded : view.pending staged pending = [(path, file)])
    (readPending : calls.getPending pending staged = .ok entries loaded)
    (reads : calls.getPending pending staged = .ok entries loaded →
      entries = view.pending staged pending ∧ view.pending loaded pending = view.pending staged pending)
    (cleared : calls.setPending pending (entries.filter (fun entry => entry.1 != path)) loaded = .ok () consumed)
    (attached : attachedReadSlot view file slot inode loaded)
    (offInode : view.pending loaded pending = [(path, file)] → attachedReadSlot view file slot inode loaded →
      calls.setPending pending [] loaded = .ok () consumed →
      ∀ path, scope path → ∀ other, names loaded path = some other →
        other ≠ inode → visible consumed other = visible loaded other)
    (keepsNames : ∀ other, scope other → names consumed other = names loaded other)
    (outside : ∀ other, scope other → names loaded other ≠ some inode) :
    (⟨names loaded, fun object => [visible loaded object]⟩ : CheckpointSurvivingFiles).Frames scope
      ⟨names consumed, fun object => [visible consumed object]⟩ := by
  obtain ⟨observed, unchanged⟩ := reads readPending
  have only := unchanged.trans recorded
  have clear : calls.setPending pending [] loaded = .ok () consumed := by
    simpa [observed, recorded] using cleared
  intro other selected
  refine ⟨keepsNames other selected, fun object named => ?_⟩
  have separate : object ≠ inode := fun same => outside other selected (same ▸ named)
  exact congrArg (fun bytes => [bytes]) (offInode only attached clear other selected object named separate)

end Clearing

end Alvoki.Storage.DiskSession
