import Alvoki.Storage.Disk.NativeCheckpointRunDurability
import Alvoki.Storage.Disk.CheckpointManifestDirectoryCut

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}

local notation "directory" => current.current.ready.state.session.directory

/-- Staging changes a private inode. The returned file sync settles that
inode's bytes while framing all paths other than the staged name. -/
structure CheckpointManifestStageEffects
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView (directory) (inodes atHeap) (runs atHeap)) : Prop where
  wrote : ∀ before after handle,
    let path := (directory).file .stagedManifest
    primitives.cached.writeStaged path stop.manifest before = .ok handle after →
    let inode := handle.1.inode handle.2.1.description
    RunWriteInodeFrame path inode (inodes after) (observe before) (observe after) ∧
    (∀ other, (observe before).visible other = some inode → other = path) ∧
    (inodes after).visible inode = stop.manifest
  synced : ∀ handle beforeWrite before after,
    let path := (directory).file .stagedManifest
    primitives.cached.writeStaged path stop.manifest beforeWrite = .ok handle before →
    fsync handle before = .ok (.ok ()) after →
    let inode := handle.1.inode handle.2.1.description
    (observe before).visible path = some inode ∧
    (∀ other, (observe before).visible other = some inode → other = path) ∧
    inodes after = (inodes before).completeFileSync inode ∧
    (observe after).visible = (observe before).visible ∧
    (observe after).crashBindings = (observe before).crashBindings

/-- The staged inode and its bytes precede the literal returned rename.
The same storage frame carries any scoped old and new run names. -/
theorem NativeCheckpointSourceStop.stagedManifestPreservesFiles
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView (directory) (inodes atHeap) (runs atHeap))
    (effects : CheckpointManifestStageEffects stop inodes runs observe) :
    let dir := directory
    let stage := dir.file .stagedManifest
    let perform := primitives.checkpointStepUntilStop dir fsync stop.next stop.manifest
    ∃ (beforeWrite beforeRename : CheckpointWorld heap) (inode : Nat)
      (handle : CheckpointOpenHandle) (atSync : heap),
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      (observe beforeRename.2).visible stage = some inode ∧
      (inodes beforeRename.2).crashBytes inode = [stop.manifest] ∧
      (observe beforeWrite.2).storageObservation.Frames (· ≠ stage) (observe beforeRename.2).storageObservation ∧
      primitives.rename stage (dir.file .manifest) beforeRename.2 = .ok () stop.atIssue.2 ∧
      stop.atIssue.1.resolve dir.path dir.path primitives.openRead stop.atIssue.2 = .ok handle (reached.1, atSync) ∧
      fsync handle atSync = .error reason reached.2 := by
  intro dir stage perform
  obtain ⟨beforeRename, root, atSync, earlierSteps, renamed, _, resolved, stopped⟩ := stop.manifestDirectoryFollowsRename
  obtain ⟨beforeWrite, afterWrite, handle, earlier, wrote, _, synced, _⟩ :=
    stop.manifestRenameFollowsStagedSync earlierSteps
  obtain ⟨frame, privateWrite, payload⟩ := effects.wrote beforeWrite.2 afterWrite.2 handle wrote
  obtain ⟨bound, privateSync, bytes, visible, survivors⟩ := effects.synced handle beforeWrite.2 afterWrite.2 beforeRename.2 wrote synced
  have storageEffect := (observe afterWrite.2).fileSyncEffect (observe beforeRename.2) bytes visible survivors
  let inode := handle.1.inode handle.2.1.description
  have stagedBytes : (inodes beforeRename.2).crashBytes inode = [stop.manifest] := by
    simpa [inode, payload, RunDirectoryInodeView.storageObservation] using storageEffect.bytes inode
  have syncedFrame := storageEffect.frames (footprint := (· ≠ stage)) (by
    intro path outside other named alias
    exact outside (privateSync path (alias ▸ named)))
  exact ⟨beforeWrite, beforeRename, inode, root, atSync, earlier,
    (congrFun visible stage).trans bound, stagedBytes,
    (frame.preservesCheckpointFootprint (fun _ _ => rfl) privateWrite (fun _ outside => outside)).trans syncedFrame,
    renamed, resolved, stopped⟩

/-- The returned same-directory rename has one correlated predecessor
map. It preserves the scoped bindings and all inode payloads. -/
structure CheckpointManifestRenameEffect (dir : DiskDirectory) (staged : Nat)
    (scope : FilePath → Prop) (entry after : CheckpointStorageObservation) : Prop where
  canonical : after.files.names (dir.file .manifest) = some staged
  visible : ∀ path, scope path → after.files.names path = entry.files.names path
  survivors : ∀ names ∈ after.crashNames, ∃ prior ∈ entry.crashNames,
    (names (dir.file .manifest) = some staged ∨ names (dir.file .manifest) = prior (dir.file .manifest)) ∧
    ∀ path, scope path → names path = prior path
  bytes : after.files.bytes = entry.files.bytes

/-- The final fsync can settle the canonical name as one child of the
directory. Its scoped frame keeps the scoped names on a joint map. -/
structure CheckpointManifestDirectoryEffect (dir : DiskDirectory) (effective : Bool)
    (scope : FilePath → Prop) (entry after : CheckpointStorageObservation) : Prop where
  survivors : ∀ names ∈ after.crashNames, ∃ prior ∈ entry.crashNames,
    (names (dir.file .manifest) = if effective then entry.files.names (dir.file .manifest)
      else prior (dir.file .manifest)) ∧
    ∀ path, scope path → names path = prior path
  visible : ∀ path, scope path → after.files.names path = entry.files.names path
  bytes : after.files.bytes = entry.files.bytes

/-- At this source stop a chosen map supplies either the actually staged
manifest or the prior settled manifest. The same map frames the other
scoped paths from before the staged write. -/
theorem NativeCheckpointSourceStop.selectsFinalManifest
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView (directory) (inodes atHeap) (runs atHeap))
    (stageEffects : CheckpointManifestStageEffects stop inodes runs observe)
    (oldStorage : ∀ beforeWrite : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM
        (primitives.checkpointStepUntilStop (directory) fsync stop.next stop.manifest)).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite →
      NativeReadyStorage current.current.ready.state (observe beforeWrite.2).storageObservation)
    (scope : FilePath → Prop) (outsideStage : ∀ path, scope path → path ≠ (directory).file .stagedManifest)
    (renameEffect : ∀ (before : heap) staged,
      (observe before).visible ((directory).file .stagedManifest) = some staged →
      primitives.rename ((directory).file .stagedManifest) ((directory).file .manifest) before = .ok () stop.atIssue.2 →
      CheckpointManifestRenameEffect (directory) staged scope
        (observe before).storageObservation (observe stop.atIssue.2).storageObservation)
    (effective : Bool)
    (directoryEffect : ∀ (handle : CheckpointOpenHandle) atSync,
      stop.atIssue.1.resolve (directory).path (directory).path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atSync) →
      fsync handle atSync = .error reason reached.2 →
      CheckpointManifestDirectoryEffect (directory) effective scope
        (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (directory).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    let dir := directory
    let perform := primitives.checkpointStepUntilStop dir fsync stop.next stop.manifest
    let writer := current.current.ready.state.writer
    let plan := VersionedRunSet.integrity
      ⟨checkpointHeader stop.next.table stop.next.generation, stop.next.table.runs.map (·.run.bytes)⟩
    ∃ (beforeWrite : CheckpointWorld heap) (published : Image),
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      (observe beforeWrite.2).storageObservation.Frames scope (observe reached.2).storageObservation ∧
      writer.published.executeVersioned plan
        ((runSteps stop.next.table.runs.length).length + 4 + (if effective then 1 else 0)) = some published ∧
      (names (dir.file .manifest)).map contents ∈ published.manifest.crashImages ∧
      (∀ path, scope path → ∀ payload,
        (observe beforeWrite.2).storageObservation.files.Stored path payload →
        (∀ prior ∈ (observe beforeWrite.2).crashBindings, prior path = (observe beforeWrite.2).visible path) →
        (names path).map contents = some payload) ∧
      (∀ index, published.durable stop.next.generation index = plan.files[index]?) ∧
      ∀ generation, generation ≠ stop.next.generation → ∀ index,
        published.durable generation index = writer.published.durable generation index := by
  intro dir perform writer plan
  let canonical := dir.file .manifest
  obtain ⟨beforeWrite, beforeRename, staged, handle, atSync, through, stagedName, stagedBytes, staging,
    renamed, resolved, stopped⟩ := stop.stagedManifestPreservesFiles inodes runs observe stageEffects
  have replaced := renameEffect beforeRename.2 staged stagedName renamed
  have synced := directoryEffect handle atSync resolved stopped
  have renamedFrame : (observe beforeRename.2).storageObservation.Frames scope
      (observe stop.atIssue.2).storageObservation := by
    refine ⟨fun path keep => ⟨replaced.visible path keep, fun inode _ => congrFun replaced.bytes inode⟩, ?_⟩
    intro after survives
    obtain ⟨prior, before, _, retained⟩ := replaced.survivors after survives
    exact ⟨prior, before, retained⟩
  have syncedFrame : (observe stop.atIssue.2).storageObservation.Frames scope
      (observe reached.2).storageObservation := by
    refine ⟨fun path keep => ⟨synced.visible path keep, fun inode _ => congrFun synced.bytes inode⟩, ?_⟩
    intro after survives
    obtain ⟨prior, before, _, retained⟩ := synced.survivors after survives
    exact ⟨prior, before, retained⟩
  have durableBytes (inode : Nat) : (inodes reached.2).crashBytes inode = (inodes beforeRename.2).crashBytes inode :=
    (congrFun synced.bytes inode).trans (congrFun replaced.bytes inode)
  have newManifest (bound : names canonical = some staged) :
      (names canonical).map contents = some stop.manifest := by
    have exactBytes : contents staged = stop.manifest := by
      have payload := sampled canonical (.inl rfl) staged bound
      rw [durableBytes, stagedBytes] at payload
      exact List.mem_singleton.mp payload
    rw [bound, Option.map_some, exactBytes]
  have choice : (names canonical).map contents = some stop.manifest ∨
      (effective = false ∧ (names canonical).map contents = writer.target.pair.manifest) := by
    obtain ⟨afterRename, possible, selected, _⟩ := synced.survivors names chosen
    cases applied : effective
    · simp only [applied, Bool.false_eq_true, ite_false] at selected
      obtain ⟨prior, earlier, oldOrNew, _⟩ := replaced.survivors afterRename possible
      rcases oldOrNew with new | old
      · exact .inl (newManifest (selected.trans new))
      · refine .inr ⟨rfl, ?_⟩
        have oldReady := oldStorage beforeWrite through
        have canonicalSelected : current.current.ready.state.crashPath canonical := .inr (.inr (.inl rfl))
        have notStaged := current.current.ready.state.crashPath_ne_stagedManifest canonicalSelected
        have manifestFrame := staging.weaken (scope := (· = canonical))
          (fun path named => named.symm ▸ notStaged)
        have priorSettled := manifestFrame.settledFrom
          (fun names member path named => by
            subst path
            exact oldReady.settled names member canonical canonicalSelected)
          prior earlier canonical rfl
        have oldManifest := oldReady.manifest
        have held := staging.visible canonical notStaged
        have selectedOld := selected.trans (old.trans priorSettled)
        cases priorManifest : current.current.ready.state.writer.target.pair.manifest with
        | none =>
          simp only [priorManifest] at oldManifest
          rw [selectedOld, held.1, oldManifest]
          rfl
        | some bytes =>
          simp only [priorManifest] at oldManifest
          obtain ⟨inode, bound, stored⟩ := oldManifest
          have actual := selectedOld.trans (held.1.trans bound)
          have payload := sampled canonical (.inl rfl) inode actual
          have oldBytes : (inodes beforeRename.2).crashBytes inode = [bytes] := (held.2 inode bound).trans stored
          rw [durableBytes, oldBytes] at payload
          rw [actual, Option.map_some, List.mem_singleton.mp payload]
    · simp only [applied, ite_true] at selected
      exact .inl (newManifest (selected.trans replaced.canonical))
  have valid := current.current.ready.readPrefix.refines.1
  have prepared : CheckpointPreflight (.ready writer.installed) (.ok (stop.next, stop.manifest)) :=
    valid.phase ▸ stop.prepared
  obtain ⟨published, executed, _, choices, written, prior⟩ :=
    prepared.finalDirectoryPublication valid.retained effective
  have frame := (staging.weaken outsideStage).trans (renamedFrame.trans syncedFrame)
  refine ⟨beforeWrite, published, through, frame, executed, ?_, ?_, written, prior⟩
  · rw [choices]
    rcases choice with new | ⟨notEffective, old⟩
    · rw [new]
      cases effective <;> simp
    · rw [notEffective, old]
      have manifest := congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair
      simp only [Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false]
      exact .inr manifest.symm
  · obtain ⟨earlier, admitted, keeps⟩ := frame.survivors names chosen
    intro path selected payload stored settled
    obtain ⟨inode, bound, durable⟩ := stored
    have selectedName := (keeps path selected).trans ((settled earlier admitted).trans bound)
    have selectedBytes : (inodes reached.2).crashBytes inode = [payload] :=
      ((frame.visible path selected).2 inode bound).trans durable
    have sampledBytes := sampled path (.inr selected) inode selectedName
    rw [selectedBytes] at sampledBytes
    rw [selectedName, Option.map_some, List.mem_singleton.mp sampledBytes]

end Alvoki.Storage.DiskSession
