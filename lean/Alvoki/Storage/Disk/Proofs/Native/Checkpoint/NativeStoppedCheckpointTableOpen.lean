import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointWatermark
import Alvoki.Storage.Disk.NativePendingCheckpointOpenPhase
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativePendingCheckpointRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap stream : Type} {state : NativeReadyState} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {rebooted : heap} {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- One concrete reboot heap has the stopped barrier's chosen name and
byte map. The healthy raw open uses the same chosen reader throughout. -/
structure RawStoppedCheckpointReopenEffects (observed : NativePendingCheckpointCrashObservation state input)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (rebooted : heap) (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    extends RawAlignedCheckpointReopenEffects observed.reopen.opening observed.reopen.chronology view calls init rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream where
  survivorNames : ∀ path, path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
    checkpointSurvivorPath state.session.directory state.writer observed.crash.pair.manifest path →
    names rebooted path = observed.crash.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer observed.crash.pair.manifest path →
    ∀ inode, observed.crash.names path = some inode → bytes rebooted inode = observed.crash.contents inode

private noncomputable def NativePendingCheckpointCrashObservation.markedReport
    (observed : NativePendingCheckpointCrashObservation state input) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := observed.crash.reboot
  retry := observed.crash.retry
  layout := observed.plan.layout
  published := observed.stop.physical.publication
  checkpoint := observed.plan.checkpoint
  selected := observed.plan.selected
  vacant := observed.crash.vacant
  opening := ⟨observed.reopen.opening.admission, observed.reopen.opening.callbacks, observed.reopen.opening.reads,
    .aligned observed.reopen.opening.finish, observed.reopen.chronology, observed.reopen.opening.marker,
    observed.reopen.opening.markerFound⟩
  prepared := observed.plan.prepared
  following := observed.reopen.opening.reads.walReads.selectedAfterWatermark observed.plan.offsets observed.plan.descriptors
  accepted := observed.plan.accepted
  ordered := valid.retained.resumed.ordered
  wal := observed.crash.rebootWal
  walLayout := (observed.crash.rebootWalSupport valid).1
  walValid := (observed.crash.rebootWalSupport valid).2
  spans := valid.retained.spans
  active := observed.plan.prepared.pair
  keeper := congrArg WalSegment.first observed.plan.keeper
  kept := congrArg FileImage.kept (observed.crash.reachedFiles valid)
  pending := pending
  bounded := bounded

variable {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
  {observed : NativePendingCheckpointCrashObservation current.current.ready.state input}

/-- A final directory sync can stop in flight. The exact public open of
its reported survivor supplies the next table and one common trace step. -/
theorem NativeOpenedPosition.opensAfterStoppedCheckpoint
    (seen : RawStoppedCheckpointReopenEffects observed view calls init names bytes rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (samePhase : view.phase = opened.contents)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    (∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      observed.stop.onOpenPhase opened (current.reached, observed.stop.barrier.entry.image) =
        .error state.session.directory.path (poisoned, state.cache, observed.stop.reached)) ∧
    (view.descriptors rebooted, view.files rebooted) = (observed.crash.reboot, observed.crash.retry) ∧
    (view.descriptors rebooted).slots = [] ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    observed.reopen.SelectedReads ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer observed.crash.pair.manifest path →
      observed.reopen.ReadsSurvivor path payload → ∃ read : observed.reopen.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions) (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativePendingCheckpointReopened current.current.ready observed next ∧
      observed.reopen.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      NativeExecutionStep current.current (.interruptedCheckpointRecovered input observed.crash.pair.manifest) start.current ∧
      state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      seen.toRawAlignedCheckpointReopenEffects.openTable remove write rename bootstrap assemble makeCache =
        .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨source, _, _, poisoned, _, _, poison, _, interrupted⟩ := current.stopsCheckpointOnOpenPhase observed.stop
  obtain ⟨valid, rows, replay⟩ := current.current.ready.readPrefix.refines
  have pending : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := rows.symm ▸ replay
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length :=
    rows.symm ▸ current.current.ready.readPrefix.readsBounded
  let marked := observed.markedReport valid pending bounded
  obtain ⟨next, reopened, sameReturn, nextReturned, owner, slot, cache⟩ :=
    current.current.ready.recoversStoppedCheckpointWithReader observed
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, _, ran⟩ := marked.opensAlignedFromAdmission seen.raw seen.seed
    observed.reopen.opening.finish rfl seen.checkpoint seen.listing seen.extents seen.seals seen.keeper seen.sameLookup
    seen.flat seen.marked remove write rename bootstrap assemble constructs seen.allocations
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, getEq, setEq, compareEq, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen rows next sameReturn nextReturned cache owner slot phaseEffects opened.ptrEq
  refine ⟨source, ⟨poisoned, ?_, interrupted⟩, Prod.ext seen.raw.entryCensus seen.raw.entryFiles,
    ?_, ?_, ?_, observed.reopen.readsSelected valid, ?_, next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource,
    reopened, sameReturn, nextReturned, ?_, reopened.toNativeCheckpointRebootContinuation.checkpointWatermark.1,
    ?_, currentEq, lock, files.symm ▸ installed.cacheReferences, files.symm ▸ installed.cacheDirectory, contents,
    getEq, setEq, compareEq, token, pins, sameFiles, sameCensus, sameCache⟩
  · rw [samePhase]
    exact poison
  · rw [seen.raw.entryCensus]
    rfl
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact (seen.survivorNames _ (.inr (.inl rfl))).trans
      ((observed.reopen.opening.reads.sameObjects.2.1.symm).trans observed.reopen.lockObject).symm
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact (seen.survivorNames _ (.inl rfl)).trans
      ((observed.reopen.opening.reads.sameObjects.1.symm).trans observed.reopen.directoryObject).symm
  · intro path payload selected ⟨file, bound, durable⟩
    exact ⟨file, (seen.survivorNames path (.inr (.inr selected))).trans bound,
      (seen.survivorBytes path selected file.object bound).trans durable⟩
  · rw [currentEq]
    exact .recoverInterruptedCheckpoint current.current observed next reopened
  · rw [rawTable, reachedHeap]
    exact ran

end Alvoki.Storage.DiskSession
