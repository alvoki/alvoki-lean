import Alvoki.Storage.Disk.NativeMarkedTableOpen
import Alvoki.Storage.Disk.NativeLongKeeperMarkedWorker

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

section

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {normalized : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedLongKeeperFinish normalized reads vacant selected}
  {chosen : CapturedKeeperFinish normalized reads vacant selected}

private def longerChronology (chronology : CapturedMarkedReadCensus reads chosen.reader)
    (longer : chosen = .longer finish) : CapturedMarkedReadCensus reads finish.reader := by
  subst chosen
  exact chronology

private theorem longerWorker (chronology : CapturedMarkedReadCensus reads chosen.reader)
    (longer : chosen = .longer finish) :
    let captured := longerChronology chronology longer
    chosen.markedWorker chronology =
      finish.recoverFromCensus captured.metadataRelease captured.runs.released captured.sealRelease := by
  subst chosen
  rfl

end

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {report : MarkedOpenSuccessReports input directory history log recorded}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {stream : Type} {fileCalls : MarkedTemporaryReadCalls heap}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot}
  {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {names : heap → FilePath → Option Nat} {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The public marked schedule installs the longer keeper result after
its first exclusive stage create succeeds. The same lock and three cache
references belong to the returned table, and its phase is allocated from
the settled repair heap. Temporary handle release is a reported effect. -/
theorem MarkedOpenSuccessReports.opensLongerKeeperFromAdmission
    (raw : RawOpenAdmissionReport report.opening.admission view calls entry)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init raw.afterFlock)
    (finish : CapturedLongKeeperFinish report.opening.callbacks report.opening.reads report.vacant report.selected)
    (longer : report.opening.finish = .longer finish)
    (prepare : NativeMarkedCheckpointReadHeap seed (longerChronology report.opening.chronology longer) fileCalls)
    (listing : MarkedDirectoryReadReport prepare directoryCalls slotOf)
    (extents : MarkedWalExtentReports prepare listing)
    (seals : MarkedSealReadChain seed fileCalls
      (longerChronology report.opening.chronology longer).seals listing.reached beforeKeeper)
    {read : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper}
    {authorization : NativeLongKeeperAuthorizationHeap read (callbacks.withFileReads fileCalls)}
    {suffix : NativeLongKeeperSuffixHeap authorization remove} {staged : NativeLongKeeperFreshStageHeap suffix stage}
    {synced : NativeLongKeeperStagedSyncHeap staged names} {renamed : NativeLongKeeperRenameHeap synced rename}
    (settled : NativeLongKeeperSettlementHeap renamed)
    (sameLookup : fileCalls.stat = calls.lookup)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors settled.reached, view.files settled.reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed settled.reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef settled.reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase
          allocation.afterToken) :
    let lockIdentity := fun handle => (view.handle raw.afterFlock handle).2.1.description
    let keeper := callbacks.withFileReads fileCalls
    let recovery := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (reopenMarkedBoundedWithCachedExtents resolved (fileCalls.readOptional resolved)
          fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
          fileCalls.seal (fileCalls.readKeeperWithRelease (fun path file =>
            keeper.modifyPending seed.pendingRef (pushPending path file))) remove
          (stage.stage seed.pendingRef keeper.modifyPending)
          (keeper.syncPaths resolved.path seed.directoryRef seed.activeRef seed.pendingRef) rename)
        (bootstrap resolved cache)
    ∃ (installed : MarkedHeapInstallation report view init raw.afterFlock seed raw.lock lockIdentity
          phaseIdentity tokenIdentity allocatePhase allocateToken settled.reached)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      calls.runOpen input init makeCache (fun resolved lock cache => do
        let opened ← recovery resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry =
        .ok installed.table installed.allocation.afterToken := by
  intro lockIdentity keeper recovery
  have locked : lockIdentity raw.lock = report.opening.admission.owner.description :=
    congrArg (fun observed => observed.2.1.description) (raw.sameLock.trans raw.appendHandle)
  obtain ⟨opened, rawRecovered, normalized, capturedCache⟩ := settled.recoversFromOpenedCache extents seals
    report.prepared report.following report.accepted report.ordered flat marker
    (throw (IO.userError "bootstrap branch is unavailable after the marker check"))
  have matched : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors settled.reached, view.files settled.reached) := by
    rw [longerWorker report.opening.chronology longer]
    exact normalized
  obtain ⟨installed⟩ := report.installsFromRepairedHeap view init raw.afterFlock seed settled.reached
    raw.lock lockIdentity locked phaseIdentity tokenIdentity allocatePhase allocateToken ⟨opened, matched⟩
    capturedCache observe
  have returned : recovery directory installed.files seed.afterPending = .ok opened settled.reached := by
    dsimp only [recovery, keeper]
    rw [← sameLookup]
    simpa only [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure] using rawRecovered
  obtain ⟨cacheOpen, makeCache, action, source, native⟩ :=
    installed.opensFromAdmission recovery assemble constructs returned matched
  exact ⟨installed, cacheOpen, makeCache, action, source, native⟩

end Alvoki.Storage.DiskSession
