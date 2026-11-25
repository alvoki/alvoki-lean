import Alvoki.Storage.Disk.NativeMarkedSealHeap

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The keeper uses the same primitive handle open and chunk reader as
the other selected files. Its pending-cell callbacks are specific to repair. -/
def AlignedKeeperCacheCallbacks.withFileReads (callbacks : AlignedKeeperCacheCallbacks heap)
    (files : MarkedTemporaryReadCalls heap) : AlignedKeeperCacheCallbacks heap :=
  { callbacks with openRead := files.openRead, readChunk := files.readChunk }

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
  let readKeeper := (callbacks.withFileReads fileCalls).readKeeper seed.pendingRef
  let readWal := fun watermark length =>
    readSelectedWithCachedExtents directory watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal readKeeper
  let sync := (callbacks.withFileReads fileCalls).syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  let settle := fun (result : Plan × Reopened × Nat) => do
    finishBoundedMarkedOpen directory result.1 result.2.2 remove write sync rename
    pure result.2.1
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
    fileCalls.seal readKeeper requested.symm covers seen.readsKeeper
  have wal : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat length prepared.atScan =
      .ok (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
        [(layout.keeper.first, layout.keeper.bytes)], retry.image.later.visible⟩,
        reads.wal.keeper.calls.metadata.byteSize.toNat) seen.remembered := by
    unfold readWal
    rw [reachedKeeper]
    simp only [Bind.bind, EStateM.bind, finishKeeper, Pure.pure, EStateM.pure]
  obtain ⟨opened, actual, projected⟩ :=
    reads.preparesFromSelectedWal selected chronology.marker.bound decoded following valid.newer accepted ordered readWal wal
  obtain ⟨captured, samePreparation, normalized⟩ :=
    finish.recoversWithSelectedPreparation chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  have raw := prepared.reachesMarkedScan selected flat marker readWal settle bootstrap
  have repaired := seen.repairsAfterRead remove write rename
  rw [extent] at repaired
  have physical := (seen.returns remove write rename).2.2.2.2
  refine ⟨opened, ?_, ?_, congrArg Prod.fst physical⟩
  · unfold reopenMarkedBoundedWithCachedExtents
    change recoverSegmentedWalWith _ _
      (prepareBoundedMarkedFromReaders directory _ (fileCalls.readOptional directory) readWal >>= settle)
      bootstrap seed.afterPending = _
    rw [raw]
    simp only [Bind.bind, EStateM.bind, actual]
    dsimp only [settle, sync]
    simp only [Bind.bind, EStateM.bind, repaired, Pure.pure, EStateM.pure]
  · rw [show (view.descriptors seen.reached, view.files seen.reached) =
        (finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) from
      congrArg Prod.snd physical]
    exact normalized

end Alvoki.Storage.DiskSession
