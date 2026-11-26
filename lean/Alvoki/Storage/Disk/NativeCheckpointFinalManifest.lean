import Alvoki.Storage.Disk.NativeCheckpointRunDurability
import Alvoki.Storage.Disk.CheckpointManifestDirectoryCut
import Alvoki.Storage.Disk.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}

local notation "dbDir" => current.current.ready.state.session.directory

/-- Staging changes a private inode. The returned file sync settles that
inode's bytes while framing all paths other than the staged name. -/
structure CheckpointManifestStageEffects
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap)) : Prop where
  wrote : ∀ before after handle,
    let path := (dbDir).file .stagedManifest
    primitives.cached.writeStaged path stop.manifest before = .ok handle after →
    let inode := handle.1.inode handle.2.1.description
    RunWriteInodeFrame path inode (inodes after) (observe before) (observe after) ∧
    (∀ other, (observe before).visible other = some inode → other = path) ∧
    (inodes after).visible inode = stop.manifest
  synced : ∀ handle beforeWrite before after,
    let path := (dbDir).file .stagedManifest
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
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (effects : CheckpointManifestStageEffects stop inodes runs observe) :
    let dir := dbDir
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
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (stageEffects : CheckpointManifestStageEffects stop inodes runs observe)
    (oldStorage : ∀ beforeWrite : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM
        (primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest)).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite →
      NativeReadyStorage current.current.ready.state (observe beforeWrite.2).storageObservation)
    (scope : FilePath → Prop) (outsideStage : ∀ path, scope path → path ≠ (dbDir).file .stagedManifest)
    (renameEffect : ∀ (before : heap) staged,
      (observe before).visible ((dbDir).file .stagedManifest) = some staged →
      primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest) before = .ok () stop.atIssue.2 →
      CheckpointManifestRenameEffect dbDir staged scope
        (observe before).storageObservation (observe stop.atIssue.2).storageObservation)
    (effective : Bool)
    (directoryEffect : ∀ (handle : CheckpointOpenHandle) atSync,
      stop.atIssue.1.resolve (dbDir).path (dbDir).path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atSync) →
      fsync handle atSync = .error reason reached.2 →
      CheckpointManifestDirectoryEffect dbDir effective scope
        (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    let dir := dbDir
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
      ((names (dir.file .manifest)).map contents = some stop.manifest ∨
        (effective = false ∧ (names (dir.file .manifest)).map contents = writer.target.pair.manifest)) ∧
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
  refine ⟨beforeWrite, published, through, frame, executed, ?_, choice, ?_, written, prior⟩
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

/-- Compare the sampled run map only at the indices selected by the
one sampled manifest. Each generation uses its own exact bytes. -/
theorem CheckpointPreflight.sampledRunsAgree {dir : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {next : Installed} {manifest : ByteArray} {binding : Option ByteArray}
    {published : Image} {actual : RunFiles}
    (prepared : CheckpointPreflight (.ready before.installed) (.ok (next, manifest)))
    (ready : before.RetainedReady dir writer)
    (chosen : binding = some manifest ∨ binding = before.target.pair.manifest)
    (newModel : ∀ index,
      published.durable next.generation index = (next.table.runs.map (·.run.bytes))[index]?)
    (oldModel : ∀ generation, generation ≠ next.generation → ∀ index,
      published.durable generation index = before.published.durable generation index)
    (newReads : ∀ index < next.table.runs.length,
      actual next.generation index = (next.table.runs.map (·.run.bytes))[index]?)
    (oldReads : ∀ bytes metadata, before.target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
      actual metadata.header.generation index = before.published.durable metadata.header.generation index) :
    SelectedRunsAgree binding actual published.durable := by
  intro bytes metadata selected decoded index inside
  have generation : next.generation.toNat = before.installed.generation.toNat + 1 := by
    cases prepared with
    | prepared _ fits _ => exact UInt64.toNat_ofNat_of_lt' fits.1
  rcases chosen with new | old
  · have payload := Option.some.inj (selected.symm.trans new)
    subst bytes
    obtain ⟨_, _, fitsCount, _⟩ := prepared.preparedFacts
    obtain ⟨_, refined, _⟩ := ready.resumed.canonical
    obtain ⟨_, _, decodedChecked⟩ := prepared.preparedManifestEncoding refined ready.resumed.bounds
    let checked := Manifest.IntegrityCheckpoint.fromRuns
      (checkpointHeader next.table next.generation) (next.table.runs.map (·.run.bytes))
    have same := Except.ok.inj (decoded.symm.trans decodedChecked)
    subst metadata
    have runCount : checked.header.runCount.toNat = next.table.runs.length :=
      UInt64.toNat_ofNat_of_lt' fitsCount
    change index < checked.header.runCount.toNat at inside
    have inRuns : index < next.table.runs.length := by simpa only [runCount] using inside
    change actual next.generation index = published.durable next.generation index
    exact (newReads index inRuns).trans (newModel index).symm
  · have priorSelected := old.symm.trans selected
    have prior := CheckpointPowerCut.selectedGeneration ready.resumed.selected
    rw [← ready.resumed.generation, priorSelected, Option.mapM, decoded] at prior
    have oldGeneration : metadata.header.generation = before.installed.generation := Except.ok.inj prior
    have different : metadata.header.generation ≠ next.generation := by
      intro same
      have equal := congrArg UInt64.toNat (same.symm.trans oldGeneration)
      omega
    exact (oldReads bytes metadata priorSelected decoded index inside).trans (oldModel _ different index).symm

/-- Instantiate both run-map branches with the same scoped sampler.
The prior and new runs come from one returned directory-barrier heap. -/
theorem CheckpointPreflight.sampledSettledRunsAgree
    {state : NativeReadyState} {next : Installed} {manifest : ByteArray} {binding : Option ByteArray}
    {published : Image} {barrier : CheckpointStorageObservation}
    (prepared : CheckpointPreflight (.ready state.writer.installed) (.ok (next, manifest)))
    (ready : state.Valid) (oldStorage : NativeReadyStorage state barrier)
    (chosen : binding = some manifest ∨ binding = state.writer.target.pair.manifest)
    (newModel : ∀ index,
      published.durable next.generation index = (next.table.runs.map (·.run.bytes))[index]?)
    (oldModel : ∀ generation, generation ≠ next.generation → ∀ index,
      published.durable generation index = state.writer.published.durable generation index)
    (newStorage : ∀ index < next.table.runs.length, ∀ run : Compaction.CheckedRun,
      next.table.runs.toArray[index]? = some run →
      let path := state.session.directory.file (.run next.generation index)
      barrier.files.Stored path run.run.bytes ∧
      ∀ names ∈ barrier.crashNames, names path = barrier.files.names path)
    (scope : FilePath → Prop)
    (includesNew : ∀ index < next.table.runs.length, scope (state.session.directory.file (.run next.generation index)))
    (includesOld : ∀ bytes metadata, state.writer.target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
      scope (state.session.directory.file (.run metadata.header.generation index)))
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (sample : ∀ path, scope path → ∀ payload, barrier.files.Stored path payload →
      (∀ prior ∈ barrier.crashNames, prior path = barrier.files.names path) →
      (names path).map contents = some payload) :
    SelectedRunsAgree binding
      (fun generation index => (names (state.session.directory.file (.run generation index))).map contents)
      published.durable := by
  let dir := state.session.directory
  let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
  apply prepared.sampledRunsAgree (actual := actual) ready.retained chosen newModel oldModel
  · intro index within
    let run := next.table.runs[index]
    have selected : next.table.runs.toArray[index]? = some run := by
      simp [List.getElem?_eq_getElem within, run]
    obtain ⟨stored, named⟩ := newStorage index within run selected
    have observed := sample _ (includesNew index within) _ stored named
    change (names (dir.file (.run next.generation index))).map contents =
      (next.table.runs.map (·.run.bytes))[index]?
    rw [List.getElem?_map, ← List.getElem?_toArray, selected]
    exact observed
  · intro bytes metadata selected decoded index within
    obtain ⟨payload, exactPayload⟩ := ready.retained.resumed.selected.runExists selected decoded within
    have stored := oldStorage.runs bytes metadata selected decoded index within payload exactPayload
    have sampled := sample _ (includesOld bytes metadata selected decoded index within) _ stored (by
      intro prior admitted
      exact oldStorage.settled prior admitted _ (.inr (.inr (.inr (.inr
        ⟨bytes, metadata, index, selected, decoded, within, rfl⟩)))))
    exact sampled.trans exactPayload.symm

private theorem walPath_ne_manifest {state : NativeReadyState} {path : FilePath}
    (wal : checkpointWalPath state.session.directory state.writer path) :
    path ≠ state.session.directory.file .manifest := by
  let dir := state.session.directory
  have segment (start : Nat) : dir.file (.walSegment start) ≠ dir.file .manifest := by
    intro same
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive same.symm
    cases impossible
  rcases wal with rfl | rfl | ⟨saved, _, rfl⟩
  · intro same
    have basenames := (String.append_right_inj (dir.path.toString ++ "/")).mp (congrArg FilePath.toString same)
    exact (by decide : "WAL.commit" ≠ "MANIFEST") basenames
  · exact segment _
  · exact segment saved.first

/-- Read the marker and selected run bytes from the very same crash map as
the final manifest. Checked replay applies to this physical run map. -/
theorem NativeCheckpointSourceStop.replaysSampledFinalCheckpoint
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.poisoned).storageObservation)
    (runEffects : ReturnedCheckpointRunEffects stop stop.next.table.runs.length inodes runs observe)
    (writtenPayload : ∀ index < stop.next.table.runs.length, ∀ before after payload handle,
      primitives.cached.writeRun ((dbDir).file (.run stop.next.generation index))
        payload before = .ok handle after →
      (inodes after).visible (handle.1.inode handle.2.1.description) = payload)
    (runBarrier : ∀ handle (atIssue after : CheckpointWorld heap),
      atIssue.1.directory = some handle → fsync handle atIssue.2 = .ok (.ok ()) after.2 →
      let state := current.current.ready.state
      CheckpointRunsDirectoryEffect (dbDir).path
        (fun path => (state.crashPath path ∧ path ≠ (dbDir).path) ∨
          ∃ index < stop.next.table.runs.length, path = (dbDir).file (.run stop.next.generation index))
        (observe atIssue.2).storageObservation (observe after.2).storageObservation)
    (stageEffects : CheckpointManifestStageEffects stop inodes runs observe)
    (scope : FilePath → Prop) (outsideStage : ∀ path, scope path → path ≠ (dbDir).file .stagedManifest)
    (retained : ∀ path, current.current.ready.state.crashPath path → path ≠ (dbDir).file .manifest → scope path)
    (newRuns : ∀ index < stop.next.table.runs.length, scope ((dbDir).file (.run stop.next.generation index)))
    (renameEffect : ∀ (before : heap) staged,
      (observe before).visible ((dbDir).file .stagedManifest) = some staged →
      primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest) before = .ok () stop.atIssue.2 →
      CheckpointManifestRenameEffect dbDir staged scope
        (observe before).storageObservation (observe stop.atIssue.2).storageObservation)
    (effective : Bool)
    (directoryEffect : ∀ (handle : CheckpointOpenHandle) atSync,
      stop.atIssue.1.resolve (dbDir).path (dbDir).path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atSync) →
      fsync handle atSync = .error reason reached.2 →
      CheckpointManifestDirectoryEffect dbDir effective scope
        (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    let dir := dbDir
    let writer := current.current.ready.state.writer
    let pair : DirectoryPublication.Bindings :=
      ⟨(names (dir.file .manifest)).map contents, (names (dir.file .walBoundary)).map contents⟩
    let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
    let files : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
    let wal : WalSegmentImage := { writer.wal with directory := .settled pair }
    let retry := wal.checkpointReopenFiles wal.directory none
    RebootDirectoryBindings current.current.ready.state names ∧
    files.Stored (dir.file .walBoundary) (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64) ∧
    (∀ segment ∈ writer.wal.segments, files.Stored (dir.file (.walSegment segment.first)) segment.bytes) ∧
    ∃ (published : Image) (layout : CanonicalKeeperLayout retry writer.history),
      pair ∈ (published.segmentedCheckpointView writer.wal).directory.crashImages ∧
      wal.ReadLayout writer.history ∧ wal.Valid writer.history ∧ layout.keeper = wal.active ∧
      layout.tail = ByteArray.empty ∧
      layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark ∧
      selectWalSegmentReads (wal.segments.map (·.first)) layout.range.watermark =
        some (layout.first, (wal.readDescriptors layout.range.watermark).map (·.first)) ∧
      WalSegmentRepair.Prepared retry layout.target layout.plan ∧
      SelectedRunsAgree pair.manifest actual published.durable ∧
      ({ published with durable := actual } : Image).AcceptsVersioned writer.history.length.toUInt64
        (CheckpointRepresentsPrefix writer.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = writer.history.length ∧
        ∃ checkpoint table model, SelectedIntegrityCheckpoint actual pair.manifest checkpoint ∧
          (((checkpoint.getD (.empty, 0)).2 = writer.installed.generation ∧
              pair.manifest = writer.wal.directory.active.manifest) ∨
            ((checkpoint.getD (.empty, 0)).2 = stop.next.generation ∧ pair.manifest = some stop.manifest)) ∧
          recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode writer.history) = .ok table ∧
          table.committed.toNat = writer.history.length ∧ table.Refines model ∧
          RepresentsWalHistory writer.history model := by
  intro dir writer pair actual files wal retry
  let state := current.current.ready.state
  have valid := current.current.ready.readPrefix.refines.1
  have prepared : CheckpointPreflight (.ready writer.installed) (.ok (stop.next, stop.manifest)) :=
    valid.phase ▸ stop.prepared
  have oldStorage := stop.priorStorageBeforeStaging inodes runs observe initial phaseStorage runEffects
    (fun handle entry after cached synced => (runBarrier handle entry after cached synced).weaken (fun _ => .inl))
  obtain ⟨beforeWrite, published, through, frame, executed, manifest, choice, sample, newModel, oldModel⟩ :=
    stop.selectsFinalManifest inodes runs observe stageEffects oldStorage scope outsideStage renameEffect
      effective directoryEffect names chosen contents sampled
  obtain ⟨barrier, throughBarrier, runStorage⟩ := stop.newRunsSettledBeforeManifest inodes runs observe runEffects
    writtenPayload
    (fun handle entry after cached synced => (runBarrier handle entry after cached synced).weaken (fun _ => .inr))
  have same := (EStateM.Result.ok.inj (throughBarrier.symm.trans through)).2
  subst barrier
  have stable := oldStorage beforeWrite through
  have includeWal : ∀ path, checkpointWalPath dir writer path → scope path :=
    fun path walPath => retained path (.inr (.inr (.inr (.inl walPath)))) (walPath_ne_manifest walPath)
  have rootInScope : scope dir.path :=
    retained _ (.inl rfl) (file_ne_directory dir .manifest).symm
  have lockInScope : scope (dir.file .lock) := retained _ (.inr (.inl rfl)) (by
    intro same
    have basenames := (String.append_right_inj (dir.path.toString ++ "/")).mp (congrArg FilePath.toString same)
    exact (by decide : "LOCK" ≠ "MANIFEST") basenames)
  have bindings := stable.rebootDirectoryBindings frame names chosen rootInScope lockInScope
  obtain ⟨markerStored, keeperStored, sealsStored⟩ :=
    stable.samplesWal frame includeWal names chosen contents (fun path kept => sampled path (.inr (includeWal path kept)))
  have segmentStored : ∀ segment ∈ writer.wal.segments, files.Stored (dir.file (.walSegment segment.first)) segment.bytes := by
    intro segment appears
    rcases List.mem_append.mp appears with sealed | last
    · exact sealsStored segment sealed
    · obtain rfl := List.mem_singleton.mp last
      exact keeperStored
  have marker : pair.walBoundary =
      some (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, bytes⟩ := markerStored
    change names (dir.file .walBoundary) = some inode at bound
    change [contents inode] = _ at bytes
    change (names (dir.file .walBoundary)).map contents = _
    rw [bound, Option.map_some, (List.cons.inj bytes).1]
  have markerModel := congrArg Publication.Image.active valid.retained.resumed.markerImage
  change writer.files.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64) at markerModel
  rw [valid.retained.directoryFiles] at markerModel
  have markerMatches : pair.walBoundary = writer.wal.directory.active.walBoundary :=
    marker.trans markerModel.symm
  have survives : pair ∈ (published.segmentedCheckpointView writer.wal).directory.crashImages := by
    apply List.mem_map.mpr
    refine ⟨pair.manifest, manifest, ?_⟩
    change (⟨pair.manifest, writer.wal.directory.active.walBoundary⟩ : DirectoryPublication.Bindings) = pair
    rw [← markerMatches]
  have oldRuns (bytes : ByteArray) (metadata : Manifest.IntegrityCheckpoint)
      (selected : writer.target.pair.manifest = some bytes)
      (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
      (index : Nat) (within : index < metadata.header.runCount.toNat) :
      scope (dir.file (.run metadata.header.generation index)) :=
    retained _ (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, selected, decoded, within, rfl⟩))))
      (runFile_ne_manifest dir metadata.header.generation index)
  have agrees : SelectedRunsAgree pair.manifest actual published.durable :=
    prepared.sampledSettledRunsAgree valid stable (choice.imp_right fun old => old.2) newModel oldModel
      (fun index within run found => by
        obtain ⟨inode, bound, stored, settled⟩ := runStorage index within run found
        exact ⟨⟨inode, bound, stored⟩, fun map allowed => (settled map allowed).trans bound.symm⟩)
      scope newRuns oldRuns names contents sample
  obtain ⟨layout, wellFormed, replay⟩ := prepared.publicationReplays valid.retained executed
  obtain ⟨_, accepted, range, decoded, upto, checkpoint, table, model, selected, generation, recovered,
    clock, refines, history⟩ := replay pair (List.mem_cons_of_mem _ survives)
  obtain ⟨walLayout, walValid, alignedLayout, _, keeper, aligned, descriptors, offsets, openPlan⟩ :=
    layout.checkpointCrashReopen wellFormed survives decoded upto
  refine ⟨bindings, markerStored, segmentStored, published, alignedLayout, survives, walLayout, walValid, keeper,
    aligned, descriptors, offsets, openPlan, agrees, ?_, range, decoded, upto, checkpoint, table, model,
    SelectedIntegrityCheckpoint.withRunMap selected agrees.symm, generation, recovered, clock, refines, history⟩
  exact agrees.acceptsVersioned decoded accepted

end Alvoki.Storage.DiskSession
