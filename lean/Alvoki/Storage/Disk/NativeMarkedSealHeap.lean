import Alvoki.Storage.Disk.NativeMarkedWalExtentsHeap

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Use the bounded production seal reader and retain the report of its
scoped descriptor release before the next selected read. -/
def MarkedTemporaryReadCalls.seal (calls : MarkedTemporaryReadCalls heap) (path : FilePath) (count : Nat) :
    EStateM IO.Error heap ByteArray :=
  calls.readWith path fun file => readExactPrefixWith selectedWalSpanError (calls.readChunk file) count ByteArray.empty

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}

/-- One raw read and finalizer for each selected seal, at the heaps and
physical slots of the same chronological chain. The last selected extent
belongs to the keeper and has its own callback. -/
inductive MarkedSealReadChain (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (calls : MarkedTemporaryReadCalls heap) {released : FilePath → List LockReferenceDrop} :
    ∀ {required : List (Nat × IO.FS.Metadata)} {initial : DescriptorInventory} {drops : List LockReferenceDrop},
      CapturedSealReadChain reads released required initial drops → heap → heap → Prop where
  | keeper {initial : DescriptorInventory} {state : heap} :
      MarkedSealReadChain seed calls (.keeper (initial := initial)) state state
  | sealed {initial : DescriptorInventory} {segment : WalSegment} {next : Nat} {nextMetadata : IO.FS.Metadata}
      {rest : List (Nat × IO.FS.Metadata)} {drops : List LockReferenceDrop} {before observed reached : heap}
      (member : segment ∈ layout.sealed) (forward : segment.first < next)
      (size : segment.bytes.size = (next - segment.first) * WAL.frameSize)
      (custody : TemporaryPrefixCustody (reads.wal.sealedFile segment member).calls initial
        (released (directory.file (.walSegment segment.first))))
      {physical : CapturedSealReadChain reads released ((next, nextMetadata) :: rest)
        (initial.afterDrops (custody.beforeOpen ++ released (directory.file (.walSegment segment.first)))) drops}
      (raw : MarkedTemporaryReadReport (reads := reads) seed calls (directory.file (.walSegment segment.first))
        (released (directory.file (.walSegment segment.first)))
        (fun file => readExactPrefixWith selectedWalSpanError (calls.readChunk file) segment.bytes.size ByteArray.empty)
        segment.bytes before observed)
      (remaining : MarkedSealReadChain seed calls physical observed reached) :
      MarkedSealReadChain seed calls (.sealed member forward size custody physical) before reached

/-- Each local report certifies the bytes returned by that actual seal
callback. The reached cache, files and census are derived by iteration
through its observed releases. -/
theorem MarkedSealReadChain.reaches {released : FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)} {initial : DescriptorInventory} {drops : List LockReferenceDrop}
    {physical : CapturedSealReadChain reads released required initial drops} {before reached : heap}
    (seen : MarkedSealReadChain seed fileCalls physical before reached)
    (census : view.descriptors before = initial) :
    ∃ schedule : CachedWalKeeperReached directory fileCalls.seal layout.keeper.first reads.wal.keeper.calls.metadata
        required before reached,
      schedule.HasPayloads (fun first bytes => retry.image.kept first = some bytes) ∧
      MarkedReadCacheFrame seed before reached ∧ view.descriptors reached = initial.afterDrops drops := by
  induction seen with
  | @keeper initial state =>
    refine ⟨.noSeals, .noSeals, MarkedReadCacheFrame.refl _ _, ?_⟩
    rw [census]
    cases initial
    simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
  | @sealed initial segment next nextMetadata rest drops before observed reached member forward size custody physical raw tail ih =>
    let file := reads.wal.sealedFile segment member
    have rawCensus := (raw.censusAfter custody).1
    obtain ⟨continuation, certified, frame, returned⟩ := ih rawCensus
    have observedRead : fileCalls.seal (directory.file (.walSegment segment.first))
        segment.bytes.size before = .ok segment.bytes observed := raw.returns.1
    rw [size] at observedRead
    have extent := file.observesFile.extent.trans size
    have fits := size ▸ reads.wal.sealFits segment member
    have schedule := CachedWalKeeperReached.sealed forward extent fits observedRead size continuation
    refine ⟨schedule, .sealed (forward := forward) (span := extent) (fits := fits) (reported := observedRead)
      (size := size) (reads.wal.kept segment member) certified, raw.returns.2.trans frame, ?_⟩
    simpa only [DescriptorInventory.afterDrops_append, List.append_assoc] using returned

namespace MarkedWalExtentReports

variable {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls} {slotOf : heap → stream → DescriptorSlot}
  {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf} {beforeKeeper : heap}

private theorem sameWalPayloads {before after : List (Nat × ByteArray)}
    (offsets : before.map Prod.fst = after.map Prod.fst)
    (left : ∀ entry ∈ before, retry.image.kept entry.1 = some entry.2)
    (right : ∀ entry ∈ after, retry.image.kept entry.1 = some entry.2) : before = after := by
  let payload (first : Nat) := (first, (retry.image.kept first).getD ByteArray.empty)
  have read (files : List (Nat × ByteArray)) (kept : ∀ entry ∈ files, retry.image.kept entry.1 = some entry.2) :
      files = (files.map Prod.fst).map payload := by
    rw [List.map_map]
    calc
      files = files.map id := (List.map_id _).symm
      _ = _ := List.map_congr_left fun file member => by cases file; simp [payload, kept _ member]
  exact ((read _ left).trans (congrArg (List.map payload) offsets)).trans (read _ right).symm

/-- The guarded marked worker's selected payload loop issues exactly the
reported sealed reads and finalizers before the keeper. The final callback
still reads and validates the keeper on this exact raw reached heap. -/
theorem reachesKeeper (extents : MarkedWalExtentReports prepared listing)
    (observed : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ retry.image.later.visible, layout.range.through < start)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) :
    let watermark := (checkpoint.getD (.empty, 0)).1.committed.toNat
    let sealPayloads := layout.sealed.map fun segment => (segment.first, segment.bytes)
    ∃ length : UInt64,
      WAL.Boundary.decode chronology.marker.bytes = .ok length ∧
      length.toNat = layout.range.through * WAL.frameSize ∧
      (length.toNat / WAL.frameSize - layout.keeper.first) * WAL.frameSize = layout.keeper.bytes.size ∧
      view.descriptors beforeKeeper = keeper.atOpen ∧ MarkedReadCacheFrame seed seed.afterPending beforeKeeper ∧
      view.cacheAt beforeKeeper seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      view.files beforeKeeper = admission.held ∧
      readSelectedWithCachedExtents directory watermark length directoryCalls.run (inspect fileCalls) fileCalls.seal readKeeper
          prepared.atScan =
        (do
          let (last, size) ← readCachedWalPayloads directory (length.toNat / WAL.frameSize) fileCalls.seal readKeeper
            [(layout.keeper.first, reads.wal.keeper.calls.metadata)]
          pure (⟨sealPayloads ++ last, retry.image.later.visible⟩, size) : EStateM IO.Error heap (WalSegmentMarkerReads × Nat))
          beforeKeeper := by
  intro watermark sealPayloads
  obtain ⟨length, _, decoded, count, _, _, closedCensus, _, _, _, _, _, _, entered⟩ :=
    extents.selects selected following later fileCalls.seal readKeeper
  obtain ⟨seals, certified, sealFrame, census⟩ := observed.reaches closedCensus
  obtain ⟨earlier, offsets, bytes, payloads⟩ := seals.reachesReadWithPayloads (length.toNat / WAL.frameSize) readKeeper certified
  have earlierOffsets : earlier.map Prod.fst = layout.sealed.map WalSegment.first := by
    simpa only [List.map_dropLast, chronology.offsets, List.map_append, List.map_cons, List.map_nil, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil] using offsets
  have earlierRead : earlier = sealPayloads := by
    apply sameWalPayloads (retry := retry) (by simpa [sealPayloads, List.map_map, Function.comp_def] using earlierOffsets) bytes
    intro file member
    obtain ⟨segment, included, rfl⟩ := List.mem_map.mp member
    exact reads.wal.kept segment included
  rw [earlierRead] at payloads
  have through : length.toNat / WAL.frameSize = layout.range.through := by
    rw [count, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have requested : (length.toNat / WAL.frameSize - layout.keeper.first) * WAL.frameSize = layout.keeper.bytes.size := by
    rw [through]
    exact layout.target.trimmedSize.symm
  let walRead := fun watermark length =>
    readSelectedWithCachedExtents directory watermark length directoryCalls.run (inspect fileCalls) fileCalls.seal readKeeper
  obtain ⟨_, _, _, _, startFrame, _, _, _⟩ := prepared.reachesScan selected walRead
  have frame := (startFrame.trans listing.returns.2.2.2.2).trans sealFrame
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, held, _, _, _, _, _⟩ := seed.installs
  refine ⟨length, decoded, count, requested, census, frame, ?_, frame.files.trans held, ?_⟩
  · simp only [OpenCloseHeapView.cacheAt, frame.directoryCell, frame.activeCell, frame.pendingCell,
      seed.directoryKept, seed.directorySet, seed.activeKept, seed.activeSet, seed.pendingSet, Option.map_some,
      Option.map_none, List.map_nil, frame.directoryHandle, seed.sameHandle, seed.openedHandle, CensusOpenAdmissionReports.cache]
    rfl
  · rw [entered]
    simp only [Bind.bind, EStateM.bind, payloads, Pure.pure, EStateM.pure]
    cases readCachedWalPayloads directory (length.toNat / WAL.frameSize) fileCalls.seal readKeeper
        [(layout.keeper.first, reads.wal.keeper.calls.metadata)] beforeKeeper with
    | error cause after => rfl
    | ok result after => cases result; rfl

end MarkedWalExtentReports

end Alvoki.Storage.DiskSession
