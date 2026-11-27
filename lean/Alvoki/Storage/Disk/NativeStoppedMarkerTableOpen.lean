import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativePendingMarkerDirectoryOpenPhase
import Alvoki.Storage.Disk.NativePendingGroupedSyncOpenPhase
import Alvoki.Storage.Disk.Proofs.Write.NativePendingMarkerStageWriteOpenPhase
import Alvoki.Storage.Disk.NativeExecutionTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {state : NativeReadyState} {input : FilePath}
  {prepared : NativeReadyWritePreparation state} {stop : NativeMarkerPublicationStop prepared}
  {crash : NativeMarkerPublicationCrash stop} {plan : crash.Plan}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {rebooted : heap} {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The raw callbacks use one selected reader of the same reported
marker publication survivor. The measured keeper selects the matching
healthy repair, including replacement of a keeper with a longer tail. -/
structure RawStoppedMarkerReopenEffects
    (reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (rebooted : heap) (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (stage : LongKeeperStageCallbacks heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    extends RawHealthyMarkedOpenEffects reader.opening view calls init rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename where
  survivorNames : ∀ path, path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
    checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
    names rebooted path = crash.raw.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
    ∀ object, crash.raw.names path = some object → bytes rebooted object = crash.raw.contents object

variable {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

noncomputable abbrev RawStoppedMarkerReopenEffects.openTable
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename) :=
  seen.toRawHealthyMarkedOpenEffects.openTable

def NativeMarkerPublicationCrashReads.RepairForTail
    (reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected) : Prop :=
  match reader.opening.finish with
  | .aligned _ => plan.layout.tail.size = 0
  | .prunedAligned _ => False
  | .longer _ => 0 < plan.layout.tail.size

/-- The measured keeper extent selects the healthy repair for the same
surviving bytes. The empty suffix uses the aligned path, and any
excess bytes require keeper replacement. -/
theorem NativeMarkerPublicationCrashReads.usesRepairForTail
    (reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected) :
    reader.RepairForTail (plan := plan) := by
  unfold NativeMarkerPublicationCrashReads.RepairForTail
  have extent := reader.opening.reads.wal.keeper.observesFile.extent
  change reader.opening.reads.wal.keeper.calls.metadata.byteSize.toNat =
    (plan.layout.keeper.bytes ++ plan.layout.tail).size at extent
  rw [ByteArray.size_append] at extent
  have size : plan.layout.boundedPlan.keeperSize = plan.layout.keeper.bytes.size := plan.layout.target.trimmedSize.symm
  have noLater : plan.layout.boundedPlan.newer = [] := plan.noLater
  have repair := reader.opening.finish.usesMeasuredRepair
  cases outcome : reader.opening.finish with
  | aligned _ =>
    rw [outcome] at repair
    obtain ⟨aligned, _⟩ := repair
    omega
  | prunedAligned _ =>
    rw [outcome] at repair
    exact repair.2 noLater
  | longer _ =>
    rw [outcome] at repair
    have longer : plan.layout.boundedPlan.keeperSize < reader.opening.reads.wal.keeper.calls.metadata.byteSize.toNat := repair
    omega

private def NativeMarkerPublicationCrashReads.markedReport (reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected)
    (valid : state.Valid) (pending : PendingClientReplay log reads plan.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy plan.history.length) :
    MarkedOpenSuccessReports input state.session.directory plan.history log reads where
  inventory := crash.raw.reboot
  retry := crash.retry
  layout := plan.layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := plan.selected
  vacant := crash.vacant
  opening := reader.opening
  prepared := plan.repair
  following := reader.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  accepted := plan.accepted
  ordered := plan.ordered
  wal := crash.wal plan.history
  walLayout := plan.walLayout
  walValid := plan.walValid
  spans := valid.retained.spans
  active := plan.repair.pair
  keeper := plan.first
  kept := plan.kept
  pending := pending
  bounded := bounded

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stop : NativeMarkerPublicationStop prepared}
  {crash : NativeMarkerPublicationCrash stop} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- The exact raw table and client state obtained from the chosen
survivor of a stopped WAL marker publication. -/
def RawStoppedMarkerReopenEffects.Returned
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable) : Prop :=
    let state := current.current.ready.state
    (view.descriptors rebooted, view.files rebooted) = (crash.raw.reboot, crash.retry) ∧
    (view.descriptors rebooted).slots = [] ∧ crash.retry.image.later.visible = [] ∧
    plan.layout.tail.size = (if crash.usesNewMarker then 0 else crash.keeperTail.size) ∧
    reader.RepairForTail (plan := plan) ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    names rebooted prepared.markerPath = some (if crash.usesNewMarker then
      state.census.inode stop.stageAllocation.markerSlot.description else
      stop.stageAllocation.stageView.modelObject stop.oldMarkerChild) ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
      reader.toNativeWriteCrashReads.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (retained : List WAL.Write)
      (next : NativeReadPosition (current.current.history ++ retained) (current.current.submissions ++ [.uncertainBatch prepared.batch]))
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativeMarkerPublicationCrashContinuation current.current.ready crash input retained next ∧
      NativeExecutionStep current.current (.interruptedMarkerRecovered stop.request input prepared.batch retained) start.current ∧
      seen.openTable bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history ++ retained, current.current.submissions ++ [.uncertainBatch prepared.batch], next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache

/-- The same selected bytes and measured repair feed the raw opener
after each supported interruption of marker publication. -/
theorem RawStoppedMarkerReopenEffects.returns
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    seen.Returned current bootstrap assemble := by
  unfold RawStoppedMarkerReopenEffects.Returned
  obtain ⟨retained, next, reopened, chosen, workerReturned, nextReturned, cache, owner, slot⟩ :=
    current.current.ready.recoversInterruptedMarkerFrom crash plan reader
  have pendingReplay := next.readPrefix.refines.2.2
  have bounded := next.readPrefix.readsBounded
  rw [reopened.reads, ← chosen] at pendingReplay bounded
  let marked := reader.markedReport current.current.ready.readPrefix.refines.1 pendingReplay bounded
  obtain ⟨_, installed, cacheOpen, makeCache, cacheAction, cacheSource, _, ran⟩ :=
    marked.opensHealthyFromAdmission seen.raw seen.seed seen.checkpoint seen.listing seen.extents seen.seals seen.keeper
      seen.sameLookup seen.flat seen.marked bootstrap assemble constructs seen.allocations
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, getEq, setEq, compareEq, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen chosen next workerReturned.symm nextReturned cache owner slot phaseEffects opened.ptrEq
  have valid := current.current.ready.readPrefix.refines.1
  refine ⟨Prod.ext seen.raw.entryCensus seen.raw.entryFiles, ?_, plan.noLater, plan.tailSize valid,
    reader.usesRepairForTail (plan := plan), ?_, ?_, ?_, ?_, retained, next, cacheOpen, makeCache,
    handle, start, cacheAction, cacheSource, reopened, ?_, ?_, currentEq, lock, files.symm ▸ installed.cacheReferences,
    files.symm ▸ installed.cacheDirectory, contents, getEq, setEq, compareEq, token, pins, sameFiles, sameCensus, sameCache⟩
  · rw [seen.raw.entryCensus]
    rfl
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact (seen.survivorNames _ (.inr (.inl rfl))).trans
      ((reader.opening.reads.sameObjects.2.1.symm).trans reader.lock).symm
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact (seen.survivorNames _ (.inl rfl)).trans
      ((reader.opening.reads.sameObjects.1.symm).trans reader.directory).symm
  · exact (seen.survivorNames _ (.inr (.inr (.inr (.inl (.inl rfl)))))).trans crash.markerObject
  · intro path payload pathSelected ⟨file, bound, returnedBytes⟩
    exact ⟨file, (seen.survivorNames path (.inr (.inr pathSelected))).trans bound,
      (seen.survivorBytes path pathSelected file.object bound).trans returnedBytes⟩
  · rw [currentEq]
    exact .recoverInterruptedMarker current.current crash retained next reopened
  · rw [rawTable, reachedHeap]
    exact ran

end

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stopped : NativeWriteMarkerRenameStop prepared}
  {crash : NativeMarkerPublicationCrash (.rename stopped)} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- The stopped marker rename and the raw reopen use the same selected
survivor. The write has no response. -/
theorem NativeOpenedPosition.opensAfterStoppedMarkerRename
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerRename current.current.ready stopped ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      stopped.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error (prepared.stagedPath, prepared.markerPath) (poisoned, stopped.synced.appendCache, stopped.reached)) ∧
    seen.Returned current bootstrap assemble := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, _, _, stoppedAtRename⟩ := current.stopsWriteAtMarkerRename stopped
  exact ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, stoppedAtRename⟩,
    seen.returns current samePhase bootstrap assemble constructs⟩

end

section

variable {stopped : NativeWriteMarkerDirectoryStop prepared}
  {oldMarker : RunChildLookup stopped.renamed.root "WAL.commit" stopped.renamed.stageView}
  {freshMarkerInode : stopped.renamed.stageView.modelObject stopped.renamed.openedMarker.child ≠
    stopped.renamed.stageView.modelObject oldMarker.child}
  {crash : NativeMarkerPublicationCrash (.directorySync stopped oldMarker freshMarkerInode)}

/-- An effective final directory fsync settles the new marker even
when the syscall never returns. Its survivor selects the whole batch. -/
theorem NativeMarkerPublicationCrash.newMarkerAfterDirectoryEffect (valid : state.Valid)
    (effect : stopped.applied = true) : crash.usesNewMarker = true := by
  have survived := crash.survived
  change crash.pair ∈ stopped.files.directory.crashImages at survived
  rw [(stopped.choices valid).2.1, effect] at survived
  change crash.pair ∈ [stopped.newPair] at survived
  have newPair := List.mem_singleton.mp survived
  have whole := congrArg DirectoryPublication.Bindings.walBoundary newPair
  change crash.pair.walBoundary = some prepared.marker at whole
  have marker : crash.pair.walBoundary =
      some (WAL.Boundary.encode (WAL.encode (state.writer.history ++ prepared.batch)).size.toUInt64) := by
    rw [(prepared.extended valid).1]
    exact whole
  have history := crash.selects valid (.inr rfl) marker
  cases selected : crash.usesNewMarker with
  | false =>
    simp only [selected, Bool.false_eq_true, ite_false, List.append_nil] at history
    have count := congrArg List.length history
    simp only [List.length_append, (prepareBatch_spec prepared.prepared).1, Nat.add_eq_left] at count
    exact False.elim (prepared.nonempty (List.length_eq_zero_iff.mp count))
  | true => rfl

end

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stopped : NativeWriteMarkerDirectoryStop prepared}
  {oldMarker : RunChildLookup stopped.renamed.root "WAL.commit" stopped.renamed.stageView}
  {freshMarkerInode : stopped.renamed.stageView.modelObject stopped.renamed.openedMarker.child ≠
    stopped.renamed.stageView.modelObject oldMarker.child}
  {crash : NativeMarkerPublicationCrash (.directorySync stopped oldMarker freshMarkerInode)} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- The returned rename and stopped final sync belong to the original
opened write. The reported survivor supplies the exact next table. -/
theorem NativeOpenedPosition.opensAfterStoppedMarkerDirectory
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerDirectory current.current.ready stopped ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      stopped.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error state.session.directory.path (poisoned, stopped.renamed.appendCache, stopped.reached)) ∧
    (stopped.applied = true → crash.usesNewMarker = true) ∧ seen.Returned current bootstrap assemble := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, _, _, stoppedAtSync⟩ := current.stopsWriteAtMarkerDirectory stopped
  exact ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, stoppedAtSync⟩,
    NativeMarkerPublicationCrash.newMarkerAfterDirectoryEffect (crash := crash) current.current.ready.readPrefix.refines.1,
    seen.returns current samePhase bootstrap assemble constructs⟩

end

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stopped : NativeWriteStagedMarkerSyncStop prepared}
  {crash : NativeMarkerPublicationCrash (.stagedSync stopped)} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- The same stopped second file fsync supplies the reboot and raw
table. The earlier marker preserves exactly the prior committed history. -/
theorem NativeOpenedPosition.opensAfterStoppedStagedMarkerSync
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingStagedMarkerSync current.current.ready stopped ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ replace, stopped.onOpenPhase opened replace (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.stagedPath (poisoned, stopped.staging.appendCache, stopped.reached)) ∧
    crash.usesNewMarker = false ∧ seen.Returned current bootstrap assemble := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, _, interrupted⟩ := current.stopsWriteAtStagedMarkerSync stopped
  have old := crash.oldMarkerAfterStagedSync current.current.ready.readPrefix.refines.1
  exact ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, interrupted⟩, old,
    seen.returns current samePhase bootstrap assemble constructs⟩

end

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stopped : NativeWriteKeeperSyncStop prepared}
  {crash : NativeMarkerPublicationCrash (.keeperSync stopped)} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- A stop at the first grouped fsync keeps the original marker. One
reported survivor of that same effect supplies the raw reopened table. -/
theorem NativeOpenedPosition.opensAfterStoppedKeeperSync
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingKeeperSync current.current.ready stopped ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ replace, stopped.onOpenPhase opened replace (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.keeperPath (poisoned, stopped.staging.groupCache, stopped.reached)) ∧
    crash.usesNewMarker = false ∧ plan.layout.tail = crash.keeperTail ∧
    (stopped.effect = .complete → crash.keeperTail = WAL.encode prepared.batch) ∧ seen.Returned current bootstrap assemble := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, _, interrupted⟩ := current.stopsWriteAtKeeperSync stopped
  have valid := current.current.ready.readPrefix.refines.1
  have old := crash.oldMarkerAfterKeeperSync valid
  have tail := plan.tailBytes valid
  rw [old] at tail
  refine ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, interrupted⟩, old, tail, ?_,
    seen.returns current samePhase bootstrap assemble constructs⟩
  intro complete
  apply crash.completeKeeperTail
  change (stopped.cut.interrupt prepared.marker prepared.staged).crashTails = _
  unfold NativeWriteKeeperSyncStop.cut
  rw [complete]
  rfl

end

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stopped : NativeMarkerStageWriteStop prepared}
  {crash : NativeMarkerPublicationCrash (.stageWrite stopped)} {plan : crash.Plan}
  {reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected}

/-- The original stage data write stops on its fresh descriptor. The
prior marker and one reported keeper tail supply the raw reopened table. -/
theorem NativeOpenedPosition.opensAfterStoppedMarkerStageWrite
    (seen : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerStageWrite current.current.ready stopped ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ flush sync replace, stopped.onOpenPhase opened flush sync replace
        (current.reached, state.cache, state.census, prepared.initial) =
          .error (prepared.stagedPath, prepared.marker) (poisoned, stopped.allocated.appendCache, stopped.reached)) ∧
    crash.usesNewMarker = false ∧ plan.layout.tail = crash.keeperTail ∧ seen.Returned current bootstrap assemble := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, interrupted⟩ := current.stopsWriteAtMarkerStageWrite stopped
  have valid := current.current.ready.readPrefix.refines.1
  have old := crash.oldMarkerAfterStageWrite valid
  have tail := plan.tailBytes valid
  rw [old] at tail
  exact ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, interrupted⟩, old, tail,
    seen.returns current samePhase bootstrap assemble constructs⟩

end

end Alvoki.Storage.DiskSession
