import Alvoki.Storage.Disk.NativeCheckpointStopContinuation
import Alvoki.Storage.Disk.NativeRawUncertainWrite

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

variable {heap : Type} (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap)
  (directory : DiskDirectory) (fsync : CheckpointFsync heap)
  (next : Installed) (manifest : ByteArray) (index : Nat)
  {before after : CheckpointWorld heap}

/-- A successful run write and its following sync use one cached handle.
The resolver consumes the remembered entry without changing the raw heap. -/
theorem CheckpointPrimitiveCalls.returnedRunPair
    {atSync : CheckpointWorld heap}
    (wrote : (primitives.checkpointStepUntilStop directory fsync next manifest (.writeRun index)).run before =
      .ok (.ok ()) atSync)
    (synced : (primitives.checkpointStepUntilStop directory fsync next manifest (.syncRun index)).run atSync =
      .ok (.ok ()) after) :
    let path := directory.file (.run next.generation index)
    ∃ (run : Compaction.CheckedRun) (handle : CheckpointOpenHandle),
      next.table.runs.toArray[index]? = some run ∧
      primitives.cached.writeRun path run.run.bytes before.2 = .ok handle atSync.2 ∧
      atSync.1 = before.1.remember path handle ∧
      fsync handle atSync.2 = .ok (.ok ()) after.2 ∧
      after.1 = before.1.consume path := by
  intro path
  obtain ⟨run, handle, selected, wrote, remembered⟩ :=
    primitives.runWriteReturned directory fsync next manifest index wrote
  have issued : (primitives.syncUntilStop directory.path fsync #[path]).run atSync = .ok (.ok ()) after := synced
  obtain ⟨consumed, completed⟩ :=
    primitives.returnedRememberedFile fsync (file_ne_directory _ _) remembered issued
  exact ⟨run, handle, selected, wrote, remembered, completed, consumed⟩

/-- Carry an invariant across actual adjacent run writes and file syncs. -/
private theorem returnedRunPairsPreserve {image : Type}
    (perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit)
    (count : Nat) (invariant : Nat → image → Prop) {entry reached : image}
    (initial : invariant 0 entry)
    (preserves : ∀ index < count, ∀ before written after,
      (perform (.writeRun index)).run before = .ok (.ok ()) written →
      (perform (.syncRun index)).run written = .ok (.ok ()) after →
      invariant index before → invariant (index + 1) after)
    (returned : ((runSteps count).forM perform).run entry = .ok (.ok ()) reached) :
    invariant count reached := by
  have prefixKeeps (finished : Nat) (within : finished ≤ count) (after : image)
      (returned : ((runSteps finished).forM perform).run entry = .ok (.ok ()) after) :
      invariant finished after := by
    induction finished generalizing after with
    | zero =>
      simp only [runSteps, List.range_zero, List.flatMap_nil] at returned
      have same : entry = after := (EStateM.Result.ok.inj returned).2
      exact same ▸ initial
    | succ index earlier =>
      have ordered : runSteps (index + 1) = (runSteps index ++ [.writeRun index]) ++ [.syncRun index] := by
        simp [runSteps, List.range_succ, List.append_assoc]
      rw [ordered] at returned
      obtain ⟨written, beforeSync, synced⟩ :=
        returnedLastStep perform (runSteps index ++ [.writeRun index]) (.syncRun index) returned
      obtain ⟨before, prior, wrote⟩ := returnedLastStep perform (runSteps index) (.writeRun index) beforeSync
      exact preserves index (by omega) before written after wrote synced (earlier (by omega) before prior)
  exact prefixKeeps count (Nat.le_refl _) reached returned

section RunDurability

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : Step} {reason : FilePath} {stoppedAt : CheckpointWorld heap}

/-- The returned run pairs leave durable bytes at visible run names.
A later directory barrier still has to settle those names. -/
theorem NativeCheckpointSourcePrefix.returnedRunsStoreBytes
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (count : Nat)
    (effects : CheckpointRunPrefixEffects stop count inodes runs observe)
    (writtenPayload : ∀ index < count, ∀ before after payload handle,
      primitives.cached.writeRun (current.current.ready.state.session.directory.file (.run stop.next.generation index))
        payload before = .ok handle after →
      (inodes after).visible (handle.1.inode handle.2.1.description) = payload)
    {afterRuns : CheckpointWorld heap}
    (returned : ((runSteps count).forM (primitives.checkpointStepUntilStop
      current.current.ready.state.session.directory fsync stop.next stop.manifest)).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterRuns) :
    ∀ index < count, ∀ run : Compaction.CheckedRun, stop.next.table.runs.toArray[index]? = some run →
      (observe afterRuns.2).storageObservation.files.Stored
        (current.current.ready.state.session.directory.file (.run stop.next.generation index)) run.run.bytes := by
  let directory := current.current.ready.state.session.directory
  let path (index : Nat) := directory.file (.run stop.next.generation index)
  let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
  let stored (finished : Nat) (world : CheckpointWorld heap) : Prop :=
    ∀ index < finished, ∀ run : Compaction.CheckedRun, stop.next.table.runs.toArray[index]? = some run →
      (observe world.2).storageObservation.files.Stored (path index) run.run.bytes
  refine returnedRunPairsPreserve perform count stored (by simp [stored]) ?_ returned
  intro n bound before atSync after ranWrite ranSync previousRuns
  obtain ⟨selectedRun, handle, selected, wrote, remembered, synced, consumed⟩ :=
    primitives.returnedRunPair directory fsync stop.next stop.manifest n ranWrite ranSync
  have resolved : atSync.1.resolve directory.path (path n) primitives.openRead atSync.2 =
      .ok handle (after.1, atSync.2) := by
    rw [remembered, Cache.resolveRemembered (file_ne_directory _ _) handle primitives.openRead, consumed]
  obtain ⟨writeFrames, privateBinding⟩ :=
    effects.write n bound before.2 atSync.2 selectedRun.run.bytes handle wrote
  obtain ⟨_, binding, syncPrivate, inodeSync, names, survives⟩ :=
    effects.sync n bound atSync after handle atSync.2 resolved synced
  have payload := writtenPayload n bound before.2 atSync.2 selectedRun.run.bytes handle wrote
  have inodeEffect := (observe atSync.2).fileSyncEffect (observe after.2) inodeSync names survives
  intro index smaller run expected
  by_cases same : index = n
  · subst index
    have sameRun := Option.some.inj (selected.symm.trans expected)
    subst run
    exact RegularFileSyncEffect.stored (payload ▸ inodeEffect) binding
  · have earlier : index < n := by omega
    have separate : path index ≠ path n := runPath_ne directory (fun equal => same (congrArg Prod.snd equal))
    have frames := writeFrames.preservesCheckpointFootprint (fun _ _ => rfl)
      privateBinding (footprint := (· = path index)) (fun _ equal => equal.symm ▸ separate)
    have afterWrite := frames.visible.stored rfl (previousRuns index earlier run expected)
    have afterSync := inodeEffect.frames (footprint := (· = path index)) (by
      intro held kept other bound alias
      exact separate (kept.symm.trans (syncPrivate held (alias ▸ bound))))
    exact afterSync.visible.stored rfl afterWrite

/-- Split the returned run prefix at its directory barrier. The
resolver and fsync receipt use the heaps reached by that prefix. -/
theorem NativeCheckpointSourcePrefix.returnedRunsBarrier
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    {afterBarrier : CheckpointWorld heap}
    (throughBarrier : let directory := current.current.ready.state.session.directory
      let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterBarrier) :
    let directory := current.current.ready.state.session.directory
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ (afterRuns : CheckpointWorld heap) (handle : CheckpointOpenHandle) (atSync : heap),
      ((runSteps stop.next.table.runs.length).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterRuns ∧
      afterRuns.1.resolve directory.path directory.path primitives.openRead afterRuns.2 =
        .ok handle (afterBarrier.1, atSync) ∧
      fsync handle atSync = .ok (.ok ()) afterBarrier.2 := by
  intro directory perform
  obtain ⟨afterRuns, runCalls, barrier⟩ :=
    returnedLastStep perform (runSteps stop.next.table.runs.length) .syncRunsDirectory throughBarrier
  have actual : (primitives.syncUntilStop directory.path fsync #[directory.path]).run afterRuns =
      .ok (.ok ()) afterBarrier := barrier
  obtain ⟨handle, atSync, picked, returnedFsync⟩ := primitives.returnedFsync fsync directory.path directory.path actual
  exact ⟨afterRuns, handle, atSync, runCalls, picked, returnedFsync⟩

/-- The cached directory selection cannot open a different description
or change the raw syscall heap on a successful resolution. -/
private theorem resolveDirectoryReceipt {directory : FilePath} {before selected : CheckpointWorld heap}
    {handle : CheckpointOpenHandle} {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap}
    (resolved : before.1.resolve directory directory primitives.openRead before.2 = .ok handle selected) :
    before.1.directory = some handle ∧ selected = before := by
  simp only [Cache.resolve, beq_self_eq_true, ↓reduceIte] at resolved
  cases cached : before.1.directory with
  | none => rw [cached] at resolved; cases resolved
  | some original =>
    rw [cached] at resolved
    obtain ⟨rfl, same⟩ := EStateM.Result.ok.inj resolved
    exact ⟨rfl, same.symm⟩

/-- At the successful runs barrier, child names in scope settle together.
Settlement of the directory's own name comes from a predecessor map. -/
structure CheckpointRunsDirectoryEffect (root : FilePath) (children : FilePath → Prop)
    (entry after : CheckpointStorageObservation) : Prop where
  bytes : after.files.bytes = entry.files.bytes
  visible : after.files.names = entry.files.names
  survivors : ∀ names ∈ after.crashNames, ∃ prior ∈ entry.crashNames,
    names root = prior root ∧ ∀ path, children path → names path = entry.files.names path

theorem CheckpointRunsDirectoryEffect.weaken {root : FilePath} {wide scope : FilePath → Prop}
    {entry after : CheckpointStorageObservation} (effect : CheckpointRunsDirectoryEffect root wide entry after)
    (included : ∀ path, scope path → wide path) : CheckpointRunsDirectoryEffect root scope entry after := by
  refine ⟨effect.bytes, effect.visible, ?_⟩
  intro names survives
  obtain ⟨prior, previous, root, children⟩ := effect.survivors names survives
  exact ⟨prior, previous, root, fun path kept => children path (included path kept)⟩

/-- The missing child-name observation at the runs barrier concerns the
bounded WAL window, including absent names. It adds no file-byte premise. -/
abbrev CheckpointRunDirectoryWalNames (directory : DiskDirectory) (fsync : CheckpointFsync heap)
    (storage : heap → CheckpointStorageObservation) (lower upper : Nat) : Prop :=
  ∀ (handle : CheckpointOpenHandle) (issued after : CheckpointWorld heap),
    issued.1.directory = some handle → fsync handle issued.2 = .ok (.ok ()) after.2 →
    ∀ names ∈ (storage after.2).crashNames, ∀ start, lower ≤ start → start ≤ upper →
      (names (directory.file (.walSegment start))).isSome =
        ((storage issued.2).files.names (directory.file (.walSegment start))).isSome

/-- Run writes and the corresponding returned file syncs preserve the
same WAL window through the actual returned runs-directory barrier. -/
theorem NativeCheckpointSourcePrefix.walNamesBeforeStagedManifest
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap))
    {lower upper : Nat} {children : FilePath → Prop}
    (phaseNames : opened.set opened.phase .poisoned current.reached = .ok () stop.poisoned →
      WalNamePresenceFrame current.current.ready.state.session.directory lower upper
        (observe current.reached).storageObservation (observe stop.poisoned).storageObservation)
    (effects : CheckpointRunPrefixEffects stop stop.next.table.runs.length inodes runs observe)
    (barrier : ∀ (handle : CheckpointOpenHandle) (issued after : CheckpointWorld heap),
      issued.1.directory = some handle → fsync handle issued.2 = .ok (.ok ()) after.2 →
      CheckpointRunsDirectoryEffect current.current.ready.state.session.directory.path children
        (observe issued.2).storageObservation (observe after.2).storageObservation)
    (walNames : CheckpointRunDirectoryWalNames current.current.ready.state.session.directory fsync
      (fun atHeap => (observe atHeap).storageObservation) lower upper)
    {afterBarrier : CheckpointWorld heap}
    (returned : let directory := current.current.ready.state.session.directory
      let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterBarrier) :
    WalNamePresenceFrame current.current.ready.state.session.directory lower upper
      (observe current.reached).storageObservation (observe afterBarrier.2).storageObservation := by
  let directory := current.current.ready.state.session.directory
  let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
  let storage := fun atHeap => (observe atHeap).storageObservation
  obtain ⟨afterRuns, handle, atSync, runCalls, resolved, synced⟩ := stop.returnedRunsBarrier returned
  let invariant (_ : Nat) (world : CheckpointWorld heap) :=
    WalNamePresenceFrame directory lower upper (storage current.reached) (storage world.2)
  have throughRuns : invariant stop.next.table.runs.length afterRuns := by
    refine returnedRunPairsPreserve perform stop.next.table.runs.length invariant (phaseNames stop.setsPoisoned) ?_ runCalls
    intro index within before written after wrote synced prior
    obtain ⟨run, descriptor, _, writtenRun, remembered, syncedRun, consumed⟩ :=
      primitives.returnedRunPair directory fsync stop.next stop.manifest index wrote synced
    have resolvedRun : written.1.resolve directory.path (directory.file (.run stop.next.generation index))
        primitives.openRead written.2 = .ok descriptor (after.1, written.2) := by
      rw [remembered, Cache.resolveRemembered (file_ne_directory _ _) descriptor primitives.openRead, consumed]
    obtain ⟨writeFrame, privateBinding⟩ := effects.write index within before.2 written.2 run.run.bytes descriptor writtenRun
    obtain ⟨_, _, _, bytes, visible, surviving⟩ := effects.sync index within written after descriptor written.2
      resolvedRun syncedRun
    have writeNames : WalNamePresenceFrame directory lower upper (storage before.2) (storage written.2) := by
      apply WalNamePresenceFrame.ofStorageFrame
        (writeFrame.preservesCheckpointFootprint (fun _ _ => rfl) privateBinding
          (footprint := fun path => path ≠ directory.file (.run stop.next.generation index)) (fun _ apart => apart))
      intro start _ _ equal
      obtain ⟨_, impossible⟩ := directory.walSegment_exclusive equal.symm
      cases impossible
    have syncNames : WalNamePresenceFrame directory lower upper (storage written.2) (storage after.2) :=
      .ofFileSync ((observe written.2).fileSyncEffect (observe after.2) bytes visible surviving)
    exact prior.trans (writeNames.trans syncNames)
  obtain ⟨cached, unchanged⟩ := resolveDirectoryReceipt resolved
  have sameHeap := congrArg Prod.snd unchanged
  have literal : fsync handle afterRuns.2 = .ok (.ok ()) afterBarrier.2 := sameHeap ▸ synced
  have effect := barrier handle afterRuns afterBarrier cached literal
  exact throughRuns.trans ⟨fun start _ _ => congrArg Option.isSome (congrFun effect.visible (directory.file (.walSegment start))),
    fun names chosen => ⟨(storage afterRuns.2).files.names, .inl rfl,
      walNames handle afterRuns afterBarrier cached literal names chosen⟩⟩

/-- The completed first directory barrier settles the new run names.
Their bytes already survived the preceding successful file syncs.
The directory's own name is governed by its parent's durability law. -/
theorem NativeCheckpointSourcePrefix.newRunsSettledAtBarrier
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    {afterBarrier : CheckpointWorld heap}
    (through : let perform := primitives.checkpointStepUntilStop current.current.ready.state.session.directory fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterBarrier)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (effects : CheckpointRunPrefixEffects stop stop.next.table.runs.length inodes runs observe)
    (writtenPayload : ∀ index < stop.next.table.runs.length, ∀ before after payload handle,
      primitives.cached.writeRun (current.current.ready.state.session.directory.file (.run stop.next.generation index))
        payload before = .ok handle after →
      (inodes after).visible (handle.1.inode handle.2.1.description) = payload)
    (directoryEffect : ∀ handle (atIssue after : CheckpointWorld heap),
      atIssue.1.directory = some handle → fsync handle atIssue.2 = .ok (.ok ()) after.2 →
      let dir := current.current.ready.state.session.directory
      CheckpointRunsDirectoryEffect dir.path
        (fun path => ∃ index < stop.next.table.runs.length, path = dir.file (.run stop.next.generation index))
        (observe atIssue.2).storageObservation (observe after.2).storageObservation) :
    let directory := current.current.ready.state.session.directory
    ∀ index < stop.next.table.runs.length, ∀ run : Compaction.CheckedRun,
        stop.next.table.runs.toArray[index]? = some run →
        let path := directory.file (.run stop.next.generation index)
        ∃ inode, (observe afterBarrier.2).visible path = some inode ∧
          (inodes afterBarrier.2).crashBytes inode = [run.run.bytes] ∧
          ∀ names ∈ (observe afterBarrier.2).crashBindings, names path = some inode := by
  intro directory
  obtain ⟨afterRuns, handle, atSync, runCalls, resolved, synced⟩ := stop.returnedRunsBarrier through
  have stored := stop.returnedRunsStoreBytes inodes runs observe _ effects writtenPayload runCalls
  obtain ⟨cached, sameWorld⟩ := resolveDirectoryReceipt resolved
  have sameHeap : atSync = afterRuns.2 := congrArg Prod.snd sameWorld
  have effect := directoryEffect handle afterRuns afterBarrier cached (sameHeap ▸ synced)
  intro index within run expected path
  obtain ⟨inode, bound, durable⟩ := stored index within run expected
  have named : (observe afterBarrier.2).visible path = some inode := by
    exact (congrFun effect.visible path).trans bound
  refine ⟨inode, named, ?_, ?_⟩
  · exact (congrFun effect.bytes inode).trans durable
  · intro names admitted
    obtain ⟨_, _, _, settled⟩ := effect.survivors names admitted
    exact (settled path ⟨index, within, rfl⟩).trans bound

/-- The previous selected files remain settled at the successful
runs-directory barrier reached before staging the manifest. -/
theorem NativeCheckpointSourcePrefix.priorStorageBeforeStaging
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.poisoned).storageObservation)
    (effects : CheckpointRunPrefixEffects stop stop.next.table.runs.length inodes runs observe)
    (directoryEffect : ∀ handle (atIssue after : CheckpointWorld heap),
      atIssue.1.directory = some handle → fsync handle atIssue.2 = .ok (.ok ()) after.2 →
      let state := current.current.ready.state
      let root := state.session.directory.path
      CheckpointRunsDirectoryEffect root (fun path => state.crashPath path ∧ path ≠ root)
        (observe atIssue.2).storageObservation (observe after.2).storageObservation) :
    let dir := current.current.ready.state.session.directory
    let perform := primitives.checkpointStepUntilStop dir fsync stop.next stop.manifest
    ∀ beforeWrite : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite →
      NativeReadyStorage current.current.ready.state (observe beforeWrite.2).storageObservation := by
  intro dir perform beforeWrite through
  obtain ⟨afterRuns, handle, atSync, runCalls, resolved, synced⟩ := stop.returnedRunsBarrier through
  obtain ⟨cached, reached⟩ := resolveDirectoryReceipt resolved
  have rawHeap := congrArg Prod.snd reached
  have atRuns := initial.frame (phaseStorage.trans (stop.returnedRunFramesAt inodes runs observe effects runCalls))
  obtain ⟨bytes, visible, names⟩ := directoryEffect handle afterRuns beforeWrite cached (rawHeap ▸ synced)
  apply atRuns.frame
  constructor
  · intro path _
    exact ⟨congrFun visible path, fun inode _ => congrFun bytes inode⟩
  · intro bindings survives
    obtain ⟨prior, earlier, root, children⟩ := names bindings survives
    refine ⟨prior, earlier, fun path selected => ?_⟩
    by_cases sameRoot : path = dir.path
    · simpa only [sameRoot] using root
    · exact (children path ⟨selected, sameRoot⟩).trans (atRuns.settled prior earlier path selected).symm

/-- The previous selected checkpoint and WAL remain durable at the
staged-MANIFEST fsync stop. Carry the entry storage through the actual
run prefix, directory barrier, stage write and stopped file sync.
The scratch inode's surviving bytes are independent of this guarantee. -/
theorem NativeCheckpointSourceStop.manifestSyncPreservesSelected
    {view : OpenCloseHeapView heap WalSegmentRepair.FileImage}
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncStaged) reason stoppedAt)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    {atFsync : heap}
    (pending : CheckpointPendingSyncAt calls view cache.pending fsync
      (current.current.ready.state.session.directory.file .stagedManifest) stop.atIssue.2 atFsync)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.poisoned).storageObservation)
    (runEffects : ReturnedCheckpointRunEffects stop stop.next.table.runs.length inodes runs observe)
    (runBarrier : ∀ handle (atIssue after : CheckpointWorld heap),
      atIssue.1.directory = some handle → fsync handle atIssue.2 = .ok (.ok ()) after.2 →
      let state := current.current.ready.state
      let root := state.session.directory.path
      CheckpointRunsDirectoryEffect root (fun path => state.crashPath path ∧ path ≠ root)
        (observe atIssue.2).storageObservation (observe after.2).storageObservation)
    (stageWrite : ∀ before handle,
      let stage := current.current.ready.state.session.directory.file .stagedManifest
      primitives.cached.writeStaged stage stop.manifest before = .ok handle stop.atIssue.2 →
      let inode := handle.1.inode handle.2.1.description
      RunWriteInodeFrame stage inode (inodes stop.atIssue.2) (observe before) (observe stop.atIssue.2) ∧
        ∀ other, (observe before).visible other = some inode → other = stage)
    (consume : (observe stop.atIssue.2).storageObservation.Frames current.current.ready.state.crashPath
      (observe atFsync).storageObservation)
    (choices : List ByteArray)
    (effect : ∀ literal, calls.fsync literal atFsync = .error reason stoppedAt.2 →
      let inode := (view.descriptors atFsync).inode (view.handle atFsync literal).2.1.description
      let state := current.current.ready.state
      (observe atFsync).visible (state.session.directory.file .stagedManifest) = some inode ∧
      (∀ path, state.crashPath path → (observe atFsync).visible path ≠ some inode) ∧
      RegularFileSyncEffect inode choices (observe atFsync).storageObservation (observe stoppedAt.2).storageObservation) :
    NativeReadyStorage current.current.ready.state (observe stoppedAt.2).storageObservation := by
  let state := current.current.ready.state
  have separate : ∀ path, state.crashPath path → path ≠ state.session.directory.file .stagedManifest :=
    fun _ => state.crashPath_ne_stagedManifest
  obtain ⟨beforeWrite, handle, through, wrote, _, _, _⟩ := stop.manifestSyncUsesWrittenHandle
  have stable := stop.toNativeCheckpointSourcePrefix.priorStorageBeforeStaging
    inodes runs observe initial phaseStorage runEffects runBarrier beforeWrite through
  obtain ⟨writeFrame, privateBinding⟩ := stageWrite beforeWrite.2 handle wrote
  have staging := writeFrame.preservesCheckpointFootprint (fun _ _ => rfl) privateBinding separate
  obtain ⟨literal, _, _, target, _, stopped, _⟩ := stop.manifestSyncIssuesRawSync calls cache projected pending
  obtain ⟨named, outside, syncEffect⟩ := effect literal stopped
  have frame := target.fileEffectFrames (observe atFsync).storageObservation (observe stoppedAt.2).storageObservation
    (state.session.directory.file .stagedManifest) named outside syncEffect
  exact stable.frame (staging.trans (consume.trans frame.2))

/-- Observe the fresh description returned by a temporary write and
the drop of that same descriptor on the successful file-sync path.
Ownership is scoped to the managed directory's lock. -/
structure CheckpointTemporaryFileCustody
    (view : OpenCloseHeapView heap WalSegmentRepair.FileImage) (directory : DiskDirectory)
    (write : FilePath → ByteArray → EStateM IO.Error heap CheckpointOpenHandle)
    (fsync : CheckpointFsync heap) (path : FilePath) (payload : ByteArray) : Prop where
  allocated : ∀ {before flushed handle}, write path payload before = .ok handle flushed →
    ∃ free : ∀ old ∈ (view.descriptors before).slots, old.address ≠ handle.2.1.address,
      (view.descriptors before).references handle.2.1.description = [] ∧
      handle.1 = (view.descriptors before).insert handle.2.1 free ∧
      view.descriptors flushed = handle.1 ∧
      (view.files flushed).owners (directory.file .lock) = (view.files before).owners (directory.file .lock)
  dropped : ∀ {before flushed after handle},
    write path payload before = .ok handle flushed → fsync handle flushed = .ok (.ok ()) after →
    view.descriptors after = (view.descriptors flushed).afterDrops [handle.2.1.closeEvent] ∧
    (view.files after).owners (directory.file .lock) = (view.files flushed).owners (directory.file .lock)

private theorem CheckpointTemporaryFileCustody.restores
    {view : OpenCloseHeapView heap WalSegmentRepair.FileImage} {directory : DiskDirectory}
    {write : FilePath → ByteArray → EStateM IO.Error heap CheckpointOpenHandle}
    {fsync : CheckpointFsync heap} {path : FilePath} {payload : ByteArray} {before flushed after : heap}
    {handle : CheckpointOpenHandle}
    (effects : CheckpointTemporaryFileCustody view directory write fsync path payload)
    (written : write path payload before = .ok handle flushed)
    (synced : fsync handle flushed = .ok (.ok ()) after) :
    view.descriptors after = view.descriptors before ∧
    (view.files after).owners (directory.file .lock) = (view.files before).owners (directory.file .lock) ∧
    handle.2.1 ∈ (view.descriptors flushed).slots ∧
    (∀ old ∈ (view.descriptors before).slots, old ∈ (view.descriptors flushed).slots) ∧
    (view.descriptors after).references handle.2.1.description = [] := by
  obtain ⟨free, fresh, captured, allocated, writeKeeps⟩ := effects.allocated written
  obtain ⟨dropped, syncKeeps⟩ := effects.dropped written synced
  have restored := dropped.trans (by rw [allocated, captured, checkpointTemporaryClose])
  have live : handle.2.1 ∈ (view.descriptors flushed).slots := by
    rw [allocated, captured]
    exact List.mem_cons_self
  refine ⟨restored, syncKeeps.trans writeKeeps, live, ?_, restored.symm ▸ fresh⟩
  intro old owned
  rw [allocated, captured]
  exact List.mem_cons_of_mem _ owned

private theorem consumeEmptyPending (cache : CensusDirectoryCache) (path : FilePath)
    (empty : cache.pending = []) : cache.consume path = cache := by
  cases cache
  simp_all [Cache.consume]

/-- The ordinary MANIFEST rename error keeps the original census and lock.
Each temporary file is released by its own returned sync. The directory
sync uses the existing cache, and the rename keeps the poisoned cell. -/
theorem NativeCheckpointSourceError.manifestRenameRetainsCustody
    {cause : IO.Error} {view : OpenCloseHeapView heap WalSegmentRepair.FileImage}
    (failed : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause stoppedAt)
    (entryCensus : view.descriptors current.reached = current.current.ready.state.census)
    (entryOwner : (view.files current.reached).owners.Owns current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor)
    (phaseWrites : ∀ after, opened.set opened.phase .poisoned current.reached = .ok () after →
      view.descriptors after = view.descriptors current.reached ∧
      (view.files after).owners (current.current.ready.state.session.directory.file .lock) =
        (view.files current.reached).owners (current.current.ready.state.session.directory.file .lock))
    (runFiles : ∀ index < failed.next.table.runs.length, ∀ run : Compaction.CheckedRun,
      failed.next.table.runs.toArray[index]? = some run →
      let dir := current.current.ready.state.session.directory
      CheckpointTemporaryFileCustody view dir primitives.cached.writeRun fsync
        (dir.file (.run failed.next.generation index)) run.run.bytes)
    (manifestFile : let dir := current.current.ready.state.session.directory
      CheckpointTemporaryFileCustody view dir primitives.cached.writeStaged fsync
        (dir.file .stagedManifest) failed.manifest)
    (directorySync : ∀ handle (before after : CheckpointWorld heap), before.1.directory = some handle →
      fsync handle before.2 = .ok (.ok ()) after.2 →
      view.descriptors after.2 = view.descriptors before.2 ∧
      (view.files after.2).owners (current.current.ready.state.session.directory.file .lock) =
        (view.files before.2).owners (current.current.ready.state.session.directory.file .lock))
    (prefixKeepsPhase : failed.toNativeCheckpointSourcePrefix.KeepsPhase)
    (renameFrames : let dir := current.current.ready.state.session.directory
      primitives.rename (dir.file .stagedManifest) (dir.file .manifest) failed.atIssue.2 = .error cause stoppedAt.2 →
      view.descriptors stoppedAt.2 = view.descriptors failed.atIssue.2 ∧
      (view.files stoppedAt.2).owners (dir.file .lock) = (view.files failed.atIssue.2).owners (dir.file .lock) ∧
      opened.contents stoppedAt.2 opened.phase = opened.contents failed.atIssue.2 opened.phase) :
    let state := current.current.ready.state
    let dir := state.session.directory
    opened.table.UsesOpenCheckpointSchedule dir opened.files opened.phase ∧
    (runCheckpointOnOpenPhaseUntilSyncStop dir opened.phase opened.get opened.set primitives fsync).run
      (state.cache, current.reached) = .ok (.error cause) stoppedAt ∧
    opened.contents failed.atIssue.2 opened.phase = some .poisoned ∧
    opened.contents stoppedAt.2 opened.phase = some .poisoned ∧
    stoppedAt.1.directory = state.cache.directory ∧
    (state.cache.pending = [] → stoppedAt.1 = state.cache) ∧
    view.descriptors stoppedAt.2 = state.census ∧
    state.owner ∈ (view.descriptors stoppedAt.2).slots ∧ state.directorySlot ∈ (view.descriptors stoppedAt.2).slots ∧
    (view.files stoppedAt.2).owners.Owns dir state.session.descriptor ∧
    ∃ (beforeStage afterWrite : heap) (handle : CheckpointOpenHandle),
      primitives.cached.writeStaged (dir.file .stagedManifest) failed.manifest beforeStage = .ok handle afterWrite ∧
      fsync handle afterWrite = .ok (.ok ()) failed.atIssue.2 ∧
      handle.2.1 ∈ (view.descriptors afterWrite).slots ∧
      state.directorySlot ∈ (view.descriptors afterWrite).slots ∧
      (view.descriptors stoppedAt.2).references handle.2.1.description = [] := by
  intro state dir
  let prior := failed.toNativeCheckpointSourcePrefix
  let lock := dir.file .lock
  let invariant (_ : Nat) (world : CheckpointWorld heap) : Prop :=
    view.descriptors world.2 = state.census ∧
    (view.files world.2).owners lock = (view.files current.reached).owners lock ∧
    world.1.directory = state.cache.directory ∧
    (state.cache.pending = [] → world.1 = state.cache)
  obtain ⟨failedRename, renameCache, beforeStage, afterWrite, stagedHandle, through, wroteStage, _, syncedStage, consumedStage⟩ :=
    failed.manifestRenameFailed
  obtain ⟨afterRuns, directoryHandle, atSync, returnedRuns, resolved, syncedRunsDirectory⟩ :=
    prior.returnedRunsBarrier through
  obtain ⟨cached, sameWorld⟩ := resolveDirectoryReceipt resolved
  obtain ⟨poisonCensus, poisonOwner⟩ := phaseWrites failed.poisoned failed.setsPoisoned
  have runsKeep : invariant failed.next.table.runs.length afterRuns := by
    refine returnedRunPairsPreserve _ _ invariant ⟨poisonCensus.trans entryCensus, poisonOwner, rfl, fun _ => rfl⟩ ?_
      returnedRuns
    intro index within before flushed after wrote synced earlier
    obtain ⟨run, handle, found, wroteFile, _, syncedFile, consumed⟩ :=
      primitives.returnedRunPair dir fsync failed.next failed.manifest index wrote synced
    obtain ⟨census, owner, _, _⟩ := (runFiles index within run found).restores wroteFile syncedFile
    refine ⟨census.trans earlier.1, owner.trans earlier.2.1, ?_, ?_⟩
    · rw [consumed]
      exact earlier.2.2.1
    · intro empty
      rw [consumed, earlier.2.2.2 empty, consumeEmptyPending _ _ empty]
  have sameCache := congrArg Prod.fst sameWorld
  have sameHeap := congrArg Prod.snd sameWorld
  obtain ⟨directoryCensus, directoryOwner⟩ := directorySync directoryHandle afterRuns beforeStage cached
    (sameHeap ▸ syncedRunsDirectory)
  obtain ⟨stageCensus, stageOwner, stagedLive, othersLive, stagedClosed⟩ := manifestFile.restores wroteStage syncedStage
  obtain ⟨renamedCensus, renamedOwner, renamePhase⟩ := renameFrames failedRename
  have reachedCensus : view.descriptors stoppedAt.2 = state.census :=
    renamedCensus.trans (stageCensus.trans (directoryCensus.trans runsKeep.1))
  have reachedOwner := renamedOwner.trans (stageOwner.trans (directoryOwner.trans runsKeep.2.1))
  have valid := current.current.ready.readPrefix.refines.1
  have cachedThroughStage : state.directorySlot ∈ (view.descriptors afterWrite.2).slots :=
    othersLive _ ((directoryCensus.trans runsKeep.1).symm ▸ valid.directoryLive)
  refine ⟨failed.source, failed.failedCall, prior.phaseAtIssue prefixKeepsPhase, failed.phaseAtError prefixKeepsPhase renamePhase,
    ?_, ?_, reachedCensus, reachedCensus.symm ▸ valid.ownerLive, reachedCensus.symm ▸ valid.directoryLive,
    ?_, beforeStage.2, afterWrite.2, stagedHandle, wroteStage, syncedStage, stagedLive, cachedThroughStage,
    renamedCensus.symm ▸ stagedClosed⟩
  · rw [renameCache, consumedStage, sameCache]
    exact runsKeep.2.2.1
  · intro empty
    rw [renameCache, consumedStage, sameCache, runsKeep.2.2.2 empty, consumeEmptyPending _ _ empty]
  · exact reachedOwner.trans entryOwner

end RunDurability

end Alvoki.Storage.DiskSession
