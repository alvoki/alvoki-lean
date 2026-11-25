import Alvoki.Storage.Disk.NativeAlignedMarkedWorker
import Alvoki.Storage.Disk.NativeLongKeeperSettlementHeap

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Keep the native length guard and pending selection. The successful
long read scope also observes the release of its temporary descriptor. -/
def MarkedTemporaryReadCalls.readKeeperWithRelease (reader : MarkedTemporaryReadCalls heap)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (path : FilePath) (count physical : Nat) : EStateM IO.Error heap ByteArray :=
  readKeeperWith reader.openRead (fun file size => do
    let bytes ← readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (reader.readChunk file) size ByteArray.empty
    if size < physical then reader.release file
    pure bytes) remember path count physical

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {beforeKeeper : heap}

/-- The scoped keeper callback uses the same bounded open and chunk
reads, then returns on the observed post-release heap. -/
theorem NativeLongKeeperReadHeap.readsScoped (seen : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit) :
    fileCalls.readKeeperWithRelease remember (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper =
        .ok layout.keeper.bytes seen.closed := by
  have prefixRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (fileCalls.readChunk seen.raw.file) layout.keeper.bytes.size ByteArray.empty seen.raw.opened =
        .ok layout.keeper.bytes seen.raw.finished := seen.raw.readRaw
  simp [MarkedTemporaryReadCalls.readKeeperWithRelease, readKeeperWith, Bind.bind, EStateM.bind,
    Nat.le_of_lt finish.longer, reads.wal.keeperFits, finish.longer, Nat.ne_of_lt finish.longer,
    seen.raw.openedRaw, prefixRead, seen.raw.releasedRaw, Pure.pure, EStateM.pure]

variable {stream : Type} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {chronology : CapturedMarkedReadCensus reads finish.reader}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
  {callbacks : AlignedKeeperCacheCallbacks heap}
  {read : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper}
  {authorization : NativeLongKeeperAuthorizationHeap read (callbacks.withFileReads fileCalls)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {suffix : NativeLongKeeperSuffixHeap authorization remove} {stage : LongKeeperStageCallbacks heap}
  {staged : NativeLongKeeperFreshStageHeap suffix stage} {names : heap → FilePath → Option Nat}
  {synced : NativeLongKeeperStagedSyncHeap staged names}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {renamed : NativeLongKeeperRenameHeap synced rename}

/-- The held worker reads the same selected checkpoint, marker and WAL
bytes as chronological recovery. Its longer keeper read releases the
original handle, and replay leaves that heap for the replacement. The
healthy fresh-stage route returns the same recovered value and settled
files, inventory and cache. -/
theorem NativeLongKeeperSettlementHeap.recoversFromOpenedCache
    (seen : NativeLongKeeperSettlementHeap renamed)
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
    (bootstrap : EStateM IO.Error heap Reopened) :
    let keeper := callbacks.withFileReads fileCalls
    let remember := fun path file => keeper.modifyPending seed.pendingRef (pushPending path file)
    let write := stage.stage seed.pendingRef keeper.modifyPending
    let grouped := keeper.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    ∃ opened,
      recoverSegmentedWalWith
        (rejectFlatWalWith directory (optionalMetadataWith (fileCalls.stat (directory.file .wal))))
        (optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)))
        (reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
          fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
          fileCalls.seal (fileCalls.readKeeperWithRelease remember) remove write grouped rename)
        bootstrap seed.afterPending = .ok opened seen.reached ∧
      finish.recoverFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
        directory admission.cache (admission.reached, admission.held) =
          .ok opened (view.descriptors seen.reached, view.files seen.reached) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  intro keeper remember write grouped
  obtain ⟨opened, ran, projected⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered flat marker
    (fileCalls.readKeeperWithRelease remember) (read.readsScoped remember) remove write grouped rename seen.returns.ran bootstrap
  obtain ⟨captured, samePreparation, normalized⟩ :=
    finish.recoversWithSelectedPreparation chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  have physical := seen.returns.final
  refine ⟨opened, ran, ?_, congrArg Prod.fst physical⟩
  rw [show (view.descriptors seen.reached, view.files seen.reached) = (finish.census, finish.settled) from
    congrArg Prod.snd physical]
  exact normalized

end Alvoki.Storage.DiskSession
