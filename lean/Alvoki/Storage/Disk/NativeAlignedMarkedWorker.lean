import Alvoki.Storage.Disk.NativeMarkedSealHeap

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The keeper uses the same primitive handle open and chunk reader as
the other selected files. Its pending-cell callbacks are specific to repair. -/
def AlignedKeeperCacheCallbacks.withFileReads (callbacks : AlignedKeeperCacheCallbacks heap)
    (files : MarkedTemporaryReadCalls heap) : AlignedKeeperCacheCallbacks heap :=
  { callbacks with openRead := files.openRead, readChunk := files.readChunk }

section

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {checkpoint : Option (PackedTable × UInt64)}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper}
  {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
  {beforeKeeper afterKeeper : heap}

/-- The selected checkpoint and WAL observations identify the result and heap
of the real preparation before any repair callback can mutate that heap. -/
theorem MarkedWalExtentReports.preparesMeasuredWal
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    (keeperRead : readKeeper (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper) :
    ∃ opened,
      prepareBoundedMarkedFromReaders directory
        (readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
          fileCalls.runSize fileCalls.runPrefix) (fileCalls.readOptional directory)
        (fun watermark length => readSelectedWithCachedExtents directory watermark length directoryCalls.run
          (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal readKeeper) seed.afterPending =
        .ok (layout.boundedPlan, opened, reads.wal.keeper.calls.metadata.byteSize.toNat) afterKeeper ∧
      reads.walReads.prepare reads.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) ∧
      ∃ model, opened.table.Refines model ∧ RepresentsWalHistory history model := by
  let readWal := fun watermark length =>
    readSelectedWithCachedExtents directory watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal readKeeper
  have later := valid.newer _ List.mem_cons_self
  obtain ⟨length, decoded, _, requested, _, _, _, _, reachedKeeper⟩ :=
    extents.reachesKeeper seals selected following later readKeeper
  have extent : reads.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    reads.wal.keeper.observesFile.extent
  have covers : layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [extent]
    change layout.keeper.bytes.size ≤ (layout.keeper.bytes ++ layout.tail).size
    rw [ByteArray.size_append]
    exact Nat.le_add_right ..
  have finishKeeper := readCachedWalPayloads_keeperSuccess directory (length.toNat / WAL.frameSize)
    fileCalls.seal readKeeper requested.symm covers keeperRead
  have wal : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat length prepared.atScan =
      .ok (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
        [(layout.keeper.first, layout.keeper.bytes)], retry.image.later.visible⟩,
        reads.wal.keeper.calls.metadata.byteSize.toNat) afterKeeper := by
    unfold readWal
    rw [reachedKeeper]
    simp only [Bind.bind, EStateM.bind, finishKeeper, Pure.pure, EStateM.pure]
  obtain ⟨opened, actual, projected, model⟩ :=
    reads.preparesFromSelectedWal selected chronology.marker.bound decoded following valid.newer accepted ordered readWal wal
  obtain ⟨_, _, _, _, _, _, _, atScan⟩ := prepared.reachesScan selected readWal
  exact ⟨opened, atScan.trans (extent ▸ actual), projected, model⟩

/-- Run the guarded marked worker on the opened cache. The keeper
callback and the chosen repair start at their actual reached heaps.
Both the raw worker and the read-only comparison use the same prepared
checkpoint and WAL payloads. The selected finisher determines the outward
result and reached heap on both success and failure. -/
theorem MarkedWalExtentReports.recoversFromOpenedCacheWith
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    (keeperRead : readKeeper (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {result : EStateM.Result IO.Error heap Unit}
    (repaired : finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write sync rename afterKeeper = result)
    (bootstrap : EStateM IO.Error heap Reopened) :
    ∃ opened,
      recoverSegmentedWalWith
        (rejectFlatWalWith directory (optionalMetadataWith (fileCalls.stat (directory.file .wal))))
        (optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)))
        (reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
          fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
          fileCalls.seal readKeeper remove write sync rename)
        bootstrap seed.afterPending = (match result with
          | .ok () ended => .ok opened ended
          | .error cause ended => .error cause ended) ∧
      reads.walReads.prepare reads.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) := by
  obtain ⟨opened, actual, projected, _⟩ := extents.preparesMeasuredWal seals selected valid following accepted ordered
    readKeeper keeperRead
  refine ⟨opened, ?_, projected⟩
  simp only [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker,
    Option.isSome, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure,
    reopenMarkedBoundedWithCachedExtents, actual, repaired]
  cases result <;> rfl

end

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedAlignedFinish calls reads vacant selected}
  {chronology : CapturedMarkedReadCensus reads finish.readCustody}
  {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
  {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}

/-- The healthy aligned marked worker reads the actual selected files and
repairs on the heap reached by that same keeper read. Its returned replay,
cache, file image and census agree with the chronological recovery. -/
theorem AlignedKeeperCacheReport.recoversFromOpenedCache
    (seen : AlignedKeeperCacheReport finish view init entry seed (callbacks.withFileReads fileCalls) beforeKeeper)
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending =
      .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : EStateM IO.Error heap Reopened) :
    ∃ opened,
      recoverSegmentedWalWith
        (rejectFlatWalWith directory (optionalMetadataWith (fileCalls.stat (directory.file .wal))))
        (optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)))
        (reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
          fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
          fileCalls.seal ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) remove write
          ((callbacks.withFileReads fileCalls).syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef)
          rename)
        bootstrap seed.afterPending = .ok opened seen.reached ∧
      finish.recoverFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
        directory admission.cache (admission.reached, admission.held) =
          .ok opened (view.descriptors seen.reached, view.files seen.reached) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  obtain ⟨opened, ran, projected⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered flat marker
    ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) seen.readsKeeper remove write
    ((callbacks.withFileReads fileCalls).syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef)
    rename (seen.repairsAfterRead remove write rename) bootstrap
  obtain ⟨captured, samePreparation, normalized⟩ :=
    finish.recoversWithSelectedPreparation chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  have physical := (seen.returns remove write rename).2.2.2.2
  refine ⟨opened, ran, ?_, congrArg Prod.fst physical⟩
  rw [show (view.descriptors seen.reached, view.files seen.reached) =
        (finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) from
      congrArg Prod.snd physical]
  exact normalized

end Alvoki.Storage.DiskSession
