import Alvoki.Storage.Disk.NativeAlignedOpenHeap
import Alvoki.Storage.Disk.NativeRawOpenAdmission
import Alvoki.Storage.Disk.NativeAlignedMarkedWorker

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {report : MarkedOpenSuccessReports input directory history log recorded}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry reached : heap}
  {raw : RawOpenAdmissionReport report.opening.admission view calls entry}
  {seed : OpenSyncCacheAllocations report.opening.admission.opened view init raw.afterFlock}
  {lockIdentity : IO.FS.Handle → Nat} {phaseIdentity : IO.Ref (Phase Installed) → Nat}
  {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- Run admission, locking, cache creation, the held worker, and the
two table allocations with the same raw lock and synchronization record.
The held recovery still has the original unlock handler. -/
theorem MarkedHeapInstallation.opensFromAdmission
    (installed : MarkedHeapInstallation report view init raw.afterFlock seed raw.lock lockIdentity
      phaseIdentity tokenIdentity allocatePhase allocateToken reached)
    (recovery : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    {opened : Reopened}
    (returned : recovery directory installed.files seed.afterPending = .ok opened reached)
    (corresponds : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors reached, view.files reached)) :
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
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
  obtain ⟨cacheOpen, makeCache, isOpen, source, initialized⟩ := installed.cacheOpened
  have sameConstructor : assemble directory raw.lock installed.files = installed.assemble :=
    (constructs directory raw.lock installed.files).trans installed.constructor.symm
  have held := installed.installsAfterRawRecovery (recovery directory installed.files) returned corresponds
  have admitted := raw.startsHeldWorker init seed initialized (fun resolved lock cache => do
    let opened ← recovery resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token)))
  refine ⟨cacheOpen, makeCache, isOpen, source, admitted.trans ?_⟩
  rw [sameConstructor]
  simp only [MonadExceptOf.tryCatch, tryCatchThe, EStateM.tryCatch, held]

/-- The marked recovery portion of the native schedule uses the original
cache references for the keeper read and subsequent repair. -/
def RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs (calls : RawOpenAdmissionCallbacks heap)
    (fileCalls : MarkedTemporaryReadCalls heap) (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (callbacks : AlignedKeeperCacheCallbacks heap)
    (directoryRef : IO.Ref (Option IO.FS.Handle))
    (activeRef : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pendingRef : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap Reopened :=
  let keeper := callbacks.withFileReads fileCalls
  recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
    (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
    (reopenMarkedBoundedWithCachedExtents resolved (fileCalls.readOptional resolved)
      fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
      fileCalls.seal (keeper.readKeeper pendingRef) remove write
      (keeper.syncPaths resolved.path directoryRef activeRef pendingRef) rename)
    (bootstrap resolved cache)

section

variable {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {normalized : CapturedAlignedCallbacks admission}
  {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedAlignedFinish normalized reads vacant selected}
  {chosen : CapturedKeeperFinish normalized reads vacant selected}

private def alignedChronology (chronology : CapturedMarkedReadCensus reads chosen.reader)
    (aligned : chosen = .aligned finish) : CapturedMarkedReadCensus reads finish.readCustody := by
  subst chosen
  exact chronology

private theorem alignedWorker (chronology : CapturedMarkedReadCensus reads chosen.reader)
    (aligned : chosen = .aligned finish) :
    let captured := alignedChronology chronology aligned
    chosen.markedWorker chronology =
      finish.recoverFromCensus captured.metadataRelease captured.runs.released captured.sealRelease := by
  subst chosen
  rfl

end

variable {stream : Type} {fileCalls : MarkedTemporaryReadCalls heap}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot}
  {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}

/-- One healthy aligned opening in the shared native schedule. The
admitted lock, cache initialization, selected file reads and repair feed
the allocations of the returned table. Each primitive observation is
local to the heap reached by the preceding call. -/
theorem MarkedOpenSuccessReports.opensAlignedFromAdmission
    (raw : RawOpenAdmissionReport report.opening.admission view calls entry)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init raw.afterFlock)
    (finish : CapturedAlignedFinish report.opening.callbacks report.opening.reads report.vacant report.selected)
    (aligned : report.opening.finish = .aligned finish)
    (prepare : NativeMarkedCheckpointReadHeap seed (alignedChronology report.opening.chronology aligned) fileCalls)
    (listing : MarkedDirectoryReadReport prepare directoryCalls slotOf)
    (extents : MarkedWalExtentReports prepare listing)
    (seals : MarkedSealReadChain seed fileCalls
      (alignedChronology report.opening.chronology aligned).seals listing.reached beforeKeeper)
    (keeper : AlignedKeeperCacheReport finish view init raw.afterFlock seed (callbacks.withFileReads fileCalls) beforeKeeper)
    (sameLookup : fileCalls.stat = calls.lookup)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors keeper.reached, view.files keeper.reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed keeper.reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef keeper.reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase
          allocation.afterToken) :
    let lockIdentity := fun handle => (view.handle raw.afterFlock handle).2.1.description
    let recovery := calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef
      seed.activeRef seed.pendingRef remove write rename bootstrap
    ∃ (installed : MarkedHeapInstallation report view init raw.afterFlock seed raw.lock lockIdentity
          phaseIdentity tokenIdentity allocatePhase allocateToken keeper.reached)
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
  intro lockIdentity recovery
  have locked : lockIdentity raw.lock = report.opening.admission.owner.description :=
    congrArg (fun observed => observed.2.1.description) (raw.sameLock.trans raw.appendHandle)
  obtain ⟨opened, rawRecovered, normalized, capturedCache⟩ := keeper.recoversFromOpenedCache extents seals
    report.prepared report.following report.accepted report.ordered flat marker remove write rename
    (throw (IO.userError "bootstrap branch is unavailable after the marker check"))
  have matched : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors keeper.reached, view.files keeper.reached) := by
    rw [alignedWorker report.opening.chronology aligned]
    exact normalized
  obtain ⟨installed⟩ := report.installsFromRepairedHeap view init raw.afterFlock seed keeper.reached
    raw.lock lockIdentity locked phaseIdentity tokenIdentity allocatePhase allocateToken ⟨opened, matched⟩
    capturedCache observe
  have returned : recovery directory installed.files seed.afterPending = .ok opened keeper.reached := by
    dsimp only [recovery, RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs]
    rw [← sameLookup]
    simpa only [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure] using rawRecovered
  obtain ⟨cacheOpen, makeCache, action, source, native⟩ :=
    installed.opensFromAdmission recovery assemble constructs returned matched
  exact ⟨installed, cacheOpen, makeCache, action, source, native⟩

end Alvoki.Storage.DiskSession
