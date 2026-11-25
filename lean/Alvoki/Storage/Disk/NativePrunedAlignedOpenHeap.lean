import Alvoki.Storage.Disk.NativeAlignedOpenHeap
import Alvoki.Storage.Disk.NativePrunedAlignedKeeperCache

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

section

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

private theorem CapturedKeeperFinish.recoversPrunedAligned
    {selectedFinish : CapturedKeeperFinish calls reads vacant selected}
    (chronology : CapturedMarkedReadCensus reads selectedFinish.reader)
    (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (pruned : selectedFinish = .prunedAligned finish)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened, selectedFinish.markedWorker chronology directory admission.cache (admission.reached, admission.held) =
      .ok opened (finish.census, finish.settled) := by
  subst selectedFinish
  exact finish.recoversFromCensus chronology prepared following accepted ordered

end

variable {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {heap : Type} {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- After the ordered prune returns with the original directory cache and
keeper sync, allocate the phase and token in that very heap. The installed
table receives the checkpoint and WAL selected by the pruned opener. -/
theorem MarkedOpenSuccessReports.installsFromPrunedAlignedCache
    (report : MarkedOpenSuccessReports input directory history log recorded)
    (finish : CapturedPrunedAlignedFinish report.opening.callbacks report.opening.reads report.vacant report.selected)
    (pruned : report.opening.finish = .prunedAligned finish)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (entry : heap)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry)
    {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    (seen : PrunedAlignedKeeperCacheReport finish view init entry seed callbacks remove beforeKeeper)
    (lock : IO.FS.Handle) (lockIdentity : IO.FS.Handle → Nat)
    (locked : lockIdentity lock = report.opening.admission.owner.description)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors seen.reached, view.files seen.reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed seen.reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef seen.reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken) :
    ∃ installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
        allocatePhase allocateToken seen.reached,
      ∀ write rename,
        (do
          seen.schedule write rename
          installReady installed.opened.installed allocatePhase allocateToken
            (fun phase token => pure (installed.assemble phase token)) : EStateM IO.Error heap DiskTable)
          beforeKeeper = .ok installed.table installed.allocation.afterToken := by
  have later := report.prepared.newer _ List.mem_cons_self
  have files := (seen.returns later (fun _ _ => pure ()) (fun _ _ => pure ())).final
  have recovered : ∃ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors seen.reached, view.files seen.reached) := by
    rw [show (view.descriptors seen.reached, view.files seen.reached) = (finish.census, finish.settled) from
      congrArg Prod.snd files]
    exact report.opening.finish.recoversPrunedAligned report.opening.chronology finish pruned report.prepared
      report.following report.accepted report.ordered
  have cached : view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef =
      report.opening.admission.cache := congrArg Prod.fst files
  obtain ⟨installed⟩ := report.installsFromRepairedHeap view init entry seed seen.reached lock lockIdentity
    locked phaseIdentity tokenIdentity allocatePhase allocateToken recovered cached observe
  refine ⟨installed, ?_⟩
  intro write rename
  simp only [Bind.bind, EStateM.bind, (seen.returns later write rename).ran, installed.allocated]

end Alvoki.Storage.DiskSession
