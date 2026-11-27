import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeAlignedMarkedWorker
import Alvoki.Storage.Disk.Proofs.Keeper.NativePrunedAlignedKeeperCache

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedPrunedAlignedFinish calls reads vacant selected}
  {chronology : CapturedMarkedReadCensus reads finish.reader}
  {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
  {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}

/-- The aligned keeper stays pending while the checked later WAL names
are pruned. The same raw marked worker reaches the settled census and
uses the single keeper read for both replay and repair. -/
theorem PrunedAlignedKeeperCacheReport.recoversFromOpenedCache
    (seen : PrunedAlignedKeeperCacheReport finish view init entry seed (callbacks.withFileReads fileCalls) remove beforeKeeper)
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
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
      finish.recoverFromCensus chronology directory admission.cache (admission.reached, admission.held) =
        .ok opened (view.descriptors seen.reached, view.files seen.reached) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  have later := valid.newer _ List.mem_cons_self
  obtain ⟨opened, ran, projected⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered flat marker
    ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) seen.readsKeeper remove write
    ((callbacks.withFileReads fileCalls).syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef)
    rename (seen.repairsAfterRead later write rename) bootstrap
  obtain ⟨captured, samePreparation, normalized⟩ :=
    finish.recoversWithSelectedPreparation chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  have physical := (seen.returns later write rename).final
  refine ⟨opened, ran, ?_, congrArg Prod.fst physical⟩
  rw [show (view.descriptors seen.reached, view.files seen.reached) = (finish.census, finish.settled) from
      congrArg Prod.snd physical]
  exact normalized

end Alvoki.Storage.DiskSession
