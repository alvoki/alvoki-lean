import Alvoki.Storage.Disk.Proofs.Bootstrap.NativeBootstrapMarkerBeforeEffectMarkedReboot
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedRestartSessions

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Replay the reported suffix from the exact returned session with no
earlier client writes, submissions or reads. -/
def NativeOpenedSessionTrace.ReplaysFromEmpty {heap : Type} (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (start : NativeOpenedSessionPoint heap) : Prop :=
  ∀ actions, NativeOpenedSessionTrace.Reports view names bytes start actions →
    ∃ events last, NativeOpenedSessionTrace view names bytes start actions events last ∧
      start.position.current.LedgerSuffix events last.position.current ∧
      last.position.current.history = events.flatMap NativeExecutionEvent.writes ∧
      last.position.current.submissions = events.flatMap NativeExecutionEvent.submissions ∧
      last.position.current.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
      InstalledClientReplay last.position.current.submissions last.position.current.ready.reads last.position.current.history
        last.position.current.ready.state.writer.installed last.position.current.ready.state.session

theorem NativeOpenedSessionTrace.replaysFromEmpty {heap : Type} {view : OpenCloseHeapView heap FileImage}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray} (start : NativeOpenedSessionPoint heap)
    (history : start.position.current.history = []) (submissions : start.position.current.submissions = [])
    (reads : start.position.current.ready.reads = []) : NativeOpenedSessionTrace.ReplaysFromEmpty view names bytes start := by
  intro actions reports
  obtain ⟨events, last, trace, ledger, replay⟩ := NativeOpenedSessionTrace.executes start actions reports
  refine ⟨events, last, trace, ledger, ?_, ?_, ?_, replay⟩
  · simpa only [history, List.nil_append] using ledger.history
  · simpa only [submissions, List.nil_append] using ledger.submissions
  · simpa only [reads, List.nil_append] using ledger.reads

namespace RawBootstrapMarkerDirectoryStop

variable {heap : Type} {firstInput nextInput : FilePath} {directory : DiskDirectory}
  {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {firstInventory : DescriptorInventory} {firstAdmission : CensusOpenAdmissionReports firstInput directory firstInventory before}
  {view : OpenCloseHeapView heap WalSegmentRotation.State}
  {firstCalls : RawOpenAdmissionCallbacks heap} {firstInit : OpenSyncCacheCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport firstAdmission view firstCalls entry}
  {seed : OpenSyncCacheAllocations captured.opened view firstInit admitted.afterFlock}
  {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
  {physical : stop.Physical handoff}

/-- The first public open issues the final directory fsync on its own
cached handle. The terminal result is outside the returned IO errors. -/
abbrev PublicStop (admitted : RawOpenAdmissionReport firstAdmission view firstCalls entry)
    (stop : RawBootstrapMarkerDirectoryStop keeper)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) : Prop :=
  ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    openSyncFilesWith (firstInit.openDirectory directory.path) firstInit.newRef firstInit.newRef firstInit.newRef
      makeCache admitted.afterFlock = .ok cache seed.afterPending ∧
    firstCalls.runUntilBootstrapDirectory firstInput firstInit makeCache
      (fun resolved _ => calls.untilMarkerDirectory resolved seed.directoryRef seed.activeRef seed.pendingRef)
      marked install entry = .error (directory.path, seed.handle) stop.afterRename

theorem stopsPublicSchedule (physical : stop.Physical handoff)
    (owner : firstAdmission.owner = fileCalls.slot)
    (lockHandle : (view.handle stop.afterRename admitted.lock).2.1 = firstAdmission.owner)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (firstCalls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) =
      firstCalls.lookup (directory.file (.walSegment 0)))
    (flat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    PublicStop admitted stop marked install := by
  obtain ⟨cacheOpen, makeCache, cache, action, source, initialized, _, _, stopped, _, _⟩ :=
    stopsPublicOpen admitted stop physical owner lockHandle metadata keeperLookup flat absent marked install
  exact ⟨cacheOpen, makeCache, cache, action, source, initialized, stopped⟩

variable
  {nextView : OpenCloseHeapView heap FileImage} {nextCalls : RawOpenAdmissionCallbacks heap}
  {nextInit : OpenSyncCacheCallbacks heap} {stream : Type}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

namespace MarkedRebootSelection.Returned

variable {rebooted : heap} {selection : MarkedRebootSelection physical rebooted}
  {opening : MarkedRebootSelection.OpenObservation (input := nextInput) selection}
  {raw : RawHealthyMarkedOpenEffects opening nextView nextCalls nextInit rebooted
    phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename}
  {fallback : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened}
  {assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

def sessionPoint (returned : selection.Returned opening raw fallback assemble get set ptrEq) :
    NativeOpenedSessionPoint heap := ⟨returned.handle, returned.start⟩

/-- The ledger begins at the exact handle returned by the marked reopen.
The selected reboot does not contribute any client writes or reads. -/
theorem replaysFromEmpty (returned : selection.Returned opening raw fallback assemble get set ptrEq)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    NativeOpenedSessionTrace.ReplaysFromEmpty nextView names bytes returned.sessionPoint :=
  NativeOpenedSessionTrace.replaysFromEmpty returned.sessionPoint returned.history returned.submissions returned.reads

end MarkedRebootSelection.Returned

namespace EffectiveReboot

/-- The first open stops on the original cached fsync without an
ordinary result. Its reported effective reboot supplies the very
empty table that starts the next finite opened-session execution. -/
theorem executesOpenedSessions (reboot : EffectiveReboot physical) (valid : BootstrapValid before.image)
    (owner : firstAdmission.owner = fileCalls.slot)
    (lockHandle : (view.handle stop.afterRename admitted.lock).2.1 = firstAdmission.owner)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (firstCalls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) =
      firstCalls.lookup (directory.file (.walSegment 0)))
    (flat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (firstMarked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (firstInstall : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (opening : let selection := (reboot.selects valid).toMarkedRebootSelection
      MarkedReadyOpenObservations nextInput directory (view.descriptors reboot.rebooted)
      (selection.markedInput) (selection.layout) (selection.checkpointImage)
      selection.vacant (selection.noCheckpoint))
    (same : (reboot.selects valid).toMarkedRebootSelection.SameReboot opening)
    (next : RawHealthyMarkedOpenEffects opening nextView nextCalls nextInit reboot.rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename)
    (fallback : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (phaseEffects : OpenPhaseCellEffects nextView.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    PublicStop admitted stop firstMarked firstInstall ∧
    reboot.Selected ∧ (reboot.selects valid).toMarkedRebootSelection.SelectedReads opening ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (start : NativeOpenedSessionPoint heap),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      next.openTable fallback assemble makeCache = .ok start.handle.table start.position.reached ∧
      nextView.phase start.position.reached start.handle.phase = some (.ready ⟨.empty, 0, 0, 0⟩) ∧
      start.position.current.history = [] ∧ start.position.current.submissions = [] ∧
      start.position.current.ready.reads = [] ∧ start.position.pins = [] ∧
      NativeOpenedSessionTrace.ReplaysFromEmpty nextView names bytes start := by
  have interrupted := stopsPublicSchedule (admitted := admitted) physical owner lockHandle metadata keeperLookup
    flat absent firstMarked firstInstall
  obtain ⟨returned⟩ :=
    (reboot.selects valid).toMarkedRebootSelection.opensEmptyTable opening same next fallback assemble constructs get set phaseEffects ptrEq
  exact ⟨interrupted, reboot.selects valid, returned.selectedReads, returned.cacheOpen, returned.makeCache,
    returned.sessionPoint, returned.cacheAction, returned.cacheSource, returned.sourceOpen, returned.phase,
    returned.history, returned.submissions, returned.reads, returned.pins, returned.replaysFromEmpty names bytes⟩

end EffectiveReboot

namespace BeforeEffectMarkedReboot

/-- A stop without a final directory effect can select the renamed zero
marker. The next marked open is the start of the same finite client
trace used after an effective barrier. Both routes reuse the empty
keeper that was already present at the first open. -/
theorem executesOpenedSessions (reboot : BeforeEffectMarkedReboot physical) (valid : BootstrapValid before.image)
    (owner : firstAdmission.owner = fileCalls.slot)
    (lockHandle : (view.handle stop.afterRename admitted.lock).2.1 = firstAdmission.owner)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (firstCalls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) =
      firstCalls.lookup (directory.file (.walSegment 0)))
    (flat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (firstMarked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (firstInstall : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (opening : MarkedRebootSelection.OpenObservation (input := nextInput) (reboot.selects valid).marked)
    (same : (reboot.selects valid).marked.SameReboot opening)
    (next : RawHealthyMarkedOpenEffects opening nextView nextCalls nextInit reboot.rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename)
    (fallback : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (phaseEffects : OpenPhaseCellEffects nextView.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    PublicStop admitted stop firstMarked firstInstall ∧ reboot.Selected ∧
    ∃ returned : (reboot.selects valid).marked.Returned opening next fallback assemble get set ptrEq,
      NativeOpenedSessionTrace.ReplaysFromEmpty nextView names bytes returned.sessionPoint := by
  have interrupted := stopsPublicSchedule (admitted := admitted) physical owner lockHandle metadata keeperLookup
    flat absent firstMarked firstInstall
  obtain ⟨selected, ⟨returned⟩⟩ := reboot.opensEmptyTable valid opening same next fallback assemble constructs get set phaseEffects ptrEq
  exact ⟨interrupted, selected, returned, returned.replaysFromEmpty names bytes⟩

end BeforeEffectMarkedReboot
end RawBootstrapMarkerDirectoryStop
end Alvoki.Storage.DiskSession
