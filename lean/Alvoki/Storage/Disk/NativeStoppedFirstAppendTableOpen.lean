import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativePendingFirstAppendOpenPhase
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {state : NativeReadyState} {input : FilePath}
  {prepared : NativeReadyWritePreparation state} {stop : NativeFirstAppendStop prepared}
  {crash : NativeFirstAppendCrash stop} {plan : crash.Plan}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {rebooted : heap} {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The stopped append's one reboot report supplies the selected
checkpoint, unchanged marker and exact surviving keeper bytes. -/
structure RawStoppedFirstAppendReopenEffects
    (reader : NativeFirstAppendCrashReads crash input plan.layout plan.selected)
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
    checkpointSurvivorPath state.session.directory state.writer crash.retry.image.directory.active.manifest path →
    names rebooted path = crash.raw.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer
    crash.retry.image.directory.active.manifest path → ∀ inode,
    crash.raw.names path = some inode → bytes rebooted inode = crash.raw.contents inode

private def NativeFirstAppendCrashReads.markedReport (reader : NativeFirstAppendCrashReads crash input plan.layout plan.selected)
    (valid : state.Valid) (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := crash.raw.reboot
  retry := crash.retry
  layout := plan.layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := plan.selected
  vacant := crash.vacant
  opening := reader.opening
  prepared := plan.recovery.prepared
  following := reader.opening.reads.walReads.selectedAfterWatermark plan.recovery.offsets plan.recovery.descriptors
  accepted := (congrArg DirectoryPublication.Bindings.manifest plan.pair).symm ▸ valid.retained.resumed.accepted
  ordered := valid.retained.resumed.ordered
  wal := state.writer.wal
  walLayout := valid.retained.layout
  walValid := valid.retained.valid
  spans := valid.retained.spans
  active := valid.retained.walPair.trans (congrArg Target.pair plan.recovery.target).symm
  keeper := plan.recovery.first
  kept := plan.recovery.kept.trans valid.retained.sealedFiles
  pending := pending
  bounded := bounded

section

variable (current : NativeOpenedPosition opened)
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stop : NativeFirstAppendStop prepared}
  {crash : NativeFirstAppendCrash stop} {plan : crash.Plan}
  {reader : NativeFirstAppendCrashReads crash input plan.layout plan.selected}

/-- A reported power loss during the opened write's first data append
leaves the prior marker. The same surviving keeper and checkpoint bytes
feed the raw marked opener and preserve all earlier reads. -/
theorem NativeOpenedPosition.opensAfterStoppedFirstAppend
    (seen : RawStoppedFirstAppendReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (samePhase : view.phase = opened.contents)
    (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
    (stageMarker : FilePath → ByteArray → FirstAppendInterrupted Unit)
    (sync : Array FilePath → FirstAppendInterrupted Unit) (renameMarker : FilePath → FilePath → FirstAppendInterrupted Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingFirstAppend current.current.ready stop ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      stop.onOpenPhase opened flush stageMarker sync renameMarker (current.reached, state.cache, state.census, prepared.initial) =
        .error stop.logical.appendCall (poisoned, state.cache, stop.cutFiles)) ∧
    (view.descriptors rebooted, view.files rebooted) = (crash.raw.reboot, crash.retry) ∧
    (view.descriptors rebooted).slots = [] ∧ crash.retry.image.later.visible = [] ∧
    reader.opening.finish.UsesMeasuredRepair ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    names rebooted prepared.markerPath = some (stop.view.modelObject stop.marker.child) ∧
    names rebooted prepared.keeperPath = some (stop.view.modelObject stop.keeper.child) ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer
      crash.retry.image.directory.active.manifest path → reader.toNativeWriteCrashReads.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (next : NativeReadPosition current.current.history (current.current.submissions ++ [.uncertainBatch prepared.batch]))
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativeFirstAppendCrashContinuation current.current.ready crash input next ∧
      NativeExecutionStep current.current (.interruptedAppendCrashRecovered stop.request input prepared.batch) start.current ∧
      seen.toRawHealthyMarkedOpenEffects.openTable bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions ++ [.uncertainBatch prepared.batch], next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨source, pending, poisoned, _, _, poison, _, stoppedAtAppend⟩ :=
    current.stopsWriteAtFirstAppend stop flush stageMarker sync renameMarker
  obtain ⟨next, reopened, worker, nextReturned, cache, owner, slot⟩ :=
    current.current.ready.recoversFirstAppendPowerLossFrom crash plan reader
  obtain ⟨valid, history, _⟩ := current.current.ready.readPrefix.refines
  let submissions := current.current.submissions ++ [.uncertainBatch prepared.batch]
  let reads := current.current.ready.reads
  have pendingReplay : PendingClientReplay submissions reads state.writer.history :=
    Eq.mpr (congrArg (PendingClientReplay submissions reads) history) pending.replay
  have bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length :=
    Eq.mpr (congrArg (fun rows : List WAL.Write => ∀ read ∈ reads, read.BoundedBy rows.length) history) pending.bounded
  let marked := reader.markedReport (plan := plan) valid pendingReplay bounded
  obtain ⟨measured, installed, cacheOpen, makeCache, cacheAction, cacheSource, _, ran⟩ :=
    marked.opensHealthyFromAdmission seen.raw seen.seed seen.checkpoint seen.listing seen.extents seen.seals seen.keeper
      seen.sameLookup seen.flat seen.marked bootstrap assemble constructs seen.allocations
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, getEq, setEq, compareEq, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen history next worker.symm nextReturned cache owner slot phaseEffects opened.ptrEq
  refine ⟨source, pending, ⟨poisoned, samePhase.symm ▸ poison, stoppedAtAppend⟩,
    Prod.ext seen.raw.entryCensus seen.raw.entryFiles, ?_, rfl, measured, ?_, ?_, ?_, ?_, ?_, next, cacheOpen, makeCache,
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
  · exact (seen.survivorNames _ (.inr (.inr (.inr (.inl (.inl rfl)))))).trans crash.marker
  · have keeperPath : prepared.keeperPath = state.session.directory.file (.walSegment state.writer.wal.active.first) :=
      congrArg (fun start => state.session.directory.file (.walSegment start))
        (valid.retained.resumed.keeper.trans valid.retained.active)
    exact (seen.survivorNames _ (.inr (.inr (.inr (.inl (.inr (.inl keeperPath))))))).trans crash.keeper
  · intro path payload pathSelected ⟨file, bound, returnedBytes⟩
    exact ⟨file, (seen.survivorNames path (.inr (.inr pathSelected))).trans bound,
      (seen.survivorBytes path pathSelected file.object bound).trans returnedBytes⟩
  · rw [currentEq]
    exact .recoverInterruptedAppendCrash current.current crash next reopened
  · rw [rawTable, reachedHeap]
    exact ran

end

end Alvoki.Storage.DiskSession
