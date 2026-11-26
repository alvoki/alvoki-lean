import Alvoki.Storage.Disk.NativeCheckpointStopContinuation

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

section RunDurability

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : Step} {reason : FilePath} {stoppedAt : CheckpointWorld heap}

/-- The returned run pairs leave durable bytes at visible run names.
A later directory barrier still has to settle those names. -/
theorem NativeCheckpointSourceStop.returnedRunsStoreBytes
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason stoppedAt)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (count : Nat)
    (effects : ReturnedCheckpointRunEffects stop count inodes runs observe)
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
  let initial : CheckpointWorld heap := (current.current.ready.state.cache, stop.poisoned)
  have aux (n : Nat) (within : n ≤ count) (after : CheckpointWorld heap)
      (returned : ((runSteps n).forM perform).run initial = .ok (.ok ()) after) :
      ∀ index < n, ∀ run : Compaction.CheckedRun, stop.next.table.runs.toArray[index]? = some run →
        (observe after.2).storageObservation.files.Stored (path index) run.run.bytes := by
    induction n generalizing after with
    | zero => simp
    | succ n ih =>
      have order : runSteps (n + 1) = (runSteps n ++ [.writeRun n]) ++ [.syncRun n] := by
        simp [runSteps, List.range_succ, List.append_assoc]
      rw [order] at returned
      obtain ⟨atSync, beforeSync, ranSync⟩ :=
        returnedLastStep perform (runSteps n ++ [.writeRun n]) (.syncRun n) returned
      obtain ⟨before, previous, ranWrite⟩ := returnedLastStep perform (runSteps n) (.writeRun n) beforeSync
      obtain ⟨selectedRun, handle, selected, wrote, remembered, synced, consumed⟩ :=
        primitives.returnedRunPair directory fsync stop.next stop.manifest n ranWrite ranSync
      have resolved : atSync.1.resolve directory.path (path n) primitives.openRead atSync.2 =
          .ok handle (after.1, atSync.2) := by
        rw [remembered, Cache.resolveRemembered (file_ne_directory _ _) handle primitives.openRead, consumed]
      have bound : n < count := by omega
      obtain ⟨writeFrames, privateBinding⟩ :=
        effects.write n bound before.2 atSync.2 selectedRun.run.bytes handle wrote
      obtain ⟨_, binding, syncPrivate, inodeSync, names, survives⟩ :=
        effects.sync n bound atSync after handle atSync.2 resolved synced
      have payload := writtenPayload n bound before.2 atSync.2 selectedRun.run.bytes handle wrote
      have inodeEffect := (observe atSync.2).fileSyncEffect (observe after.2) inodeSync names survives
      have previousRuns := ih (by omega) before previous
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
  exact aux count (Nat.le_refl _) afterRuns returned

/-- The final manifest barrier reaches past the successful run directory
barrier. Extract its returned prefix and actual successful fsync. -/
theorem NativeCheckpointSourceStop.manifestDirectoryReturnedRunsBarrier
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason stoppedAt) :
    let directory := current.current.ready.state.session.directory
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ (afterRuns afterBarrier : CheckpointWorld heap) (handle : CheckpointOpenHandle) (atSync : heap),
      ((runSteps stop.next.table.runs.length).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterRuns ∧
      afterRuns.1.resolve directory.path directory.path primitives.openRead afterRuns.2 =
        .ok handle (afterBarrier.1, atSync) ∧
      fsync handle atSync = .ok (.ok ()) afterBarrier.2 ∧
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterBarrier := by
  intro directory perform
  let runs := runSteps stop.next.table.runs.length
  obtain ⟨_, _, _, returned, _⟩ := stop.manifestDirectoryFollowsRename
  have length : runs ++ [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged] =
      ((runs ++ [Step.syncRunsDirectory]) ++ [.manifest .writeStaged]) ++ [.manifest .syncStaged] := by
    simp [List.append_assoc]
  rw [length] at returned
  obtain ⟨beforeManifestSync, throughWrite, _⟩ :=
    returnedLastStep perform ((runs ++ [Step.syncRunsDirectory]) ++ [.manifest .writeStaged])
      (.manifest .syncStaged) returned
  obtain ⟨afterBarrier, throughBarrier, _⟩ :=
    returnedLastStep perform (runs ++ [Step.syncRunsDirectory]) (.manifest .writeStaged) throughWrite
  obtain ⟨afterRuns, runCalls, barrier⟩ := returnedLastStep perform runs .syncRunsDirectory throughBarrier
  have actual : (primitives.syncUntilStop directory.path fsync #[directory.path]).run afterRuns =
      .ok (.ok ()) afterBarrier := barrier
  obtain ⟨handle, atSync, picked, returnedFsync⟩ := primitives.returnedFsync fsync directory.path directory.path actual
  exact ⟨afterRuns, afterBarrier, handle, atSync, runCalls, picked, returnedFsync, throughBarrier⟩

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

/-- The completed first directory barrier settles the new run names.
Their bytes already survived the preceding successful file syncs.
The directory's own name is governed by its parent's durability law. -/
theorem NativeCheckpointSourceStop.newRunsSettledBeforeManifest
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason stoppedAt)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (effects : ReturnedCheckpointRunEffects stop stop.next.table.runs.length inodes runs observe)
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
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ afterBarrier : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) afterBarrier ∧
      ∀ index < stop.next.table.runs.length, ∀ run : Compaction.CheckedRun,
        stop.next.table.runs.toArray[index]? = some run →
        let path := directory.file (.run stop.next.generation index)
        ∃ inode, (observe afterBarrier.2).visible path = some inode ∧
          (inodes afterBarrier.2).crashBytes inode = [run.run.bytes] ∧
          ∀ names ∈ (observe afterBarrier.2).crashBindings, names path = some inode := by
  intro directory perform
  obtain ⟨afterRuns, afterBarrier, handle, atSync, runCalls, resolved, synced, through⟩ :=
    stop.manifestDirectoryReturnedRunsBarrier
  have stored := stop.returnedRunsStoreBytes inodes runs observe _ effects writtenPayload runCalls
  obtain ⟨cached, sameWorld⟩ := resolveDirectoryReceipt resolved
  have sameHeap : atSync = afterRuns.2 := congrArg Prod.snd sameWorld
  have effect := directoryEffect handle afterRuns afterBarrier cached (sameHeap ▸ synced)
  refine ⟨afterBarrier, through, ?_⟩
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
runs-directory barrier in the final checkpoint's returned prefix. -/
theorem NativeCheckpointSourceStop.priorStorageBeforeStaging
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason stoppedAt)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.poisoned).storageObservation)
    (effects : ReturnedCheckpointRunEffects stop stop.next.table.runs.length inodes runs observe)
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
  obtain ⟨afterRuns, afterBarrier, handle, atSync, runCalls, resolved, synced, returned⟩ :=
    stop.manifestDirectoryReturnedRunsBarrier
  have same := (EStateM.Result.ok.inj (returned.symm.trans through)).2
  subst beforeWrite
  obtain ⟨cached, reached⟩ := resolveDirectoryReceipt resolved
  have rawHeap := congrArg Prod.snd reached
  have atRuns := initial.frame (phaseStorage.trans (stop.returnedRunFramesAt inodes runs observe effects runCalls))
  obtain ⟨bytes, visible, names⟩ := directoryEffect handle afterRuns afterBarrier cached (rawHeap ▸ synced)
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

end RunDurability

end Alvoki.Storage.DiskSession
