import Alvoki.Storage.Disk.NativeCheckpointRunDurability
import Alvoki.Storage.Disk.CheckpointManifestDirectoryCut
import Alvoki.Storage.Disk.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : Step} {reason : FilePath} {cause : IO.Error} {reached : CheckpointWorld heap}

local notation "dbDir" => current.current.ready.state.session.directory

/-- Staging changes a private inode. The returned file sync settles that
inode's bytes while framing all paths other than the staged name. -/
structure CheckpointManifestStageEffects
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
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

/-- The returned staged write and its fsync settle the staged inode's
bytes and frame every other path before either rename outcome. -/
theorem NativeCheckpointSourcePrefix.stageManifestBeforeRename
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    {beforeRename : CheckpointWorld heap}
    (through : let perform := primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++
        [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeRename)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (effects : CheckpointManifestStageEffects stop inodes runs observe) :
    let dir := dbDir
    let stage := dir.file .stagedManifest
    let perform := primitives.checkpointStepUntilStop dir fsync stop.next stop.manifest
    ∃ (beforeWrite : CheckpointWorld heap) (inode : Nat),
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      (observe beforeRename.2).visible stage = some inode ∧
      (inodes beforeRename.2).crashBytes inode = [stop.manifest] ∧
      (observe beforeWrite.2).storageObservation.Frames (· ≠ stage) (observe beforeRename.2).storageObservation := by
  intro dir stage perform
  obtain ⟨beforeWrite, afterWrite, handle, earlier, wrote, _, synced, _⟩ :=
    stop.manifestRenameFollowsStagedSync through
  obtain ⟨frame, privateWrite, payload⟩ := effects.wrote beforeWrite.2 afterWrite.2 handle wrote
  obtain ⟨bound, privateSync, bytes, visible, survivors⟩ := effects.synced handle beforeWrite.2 afterWrite.2 beforeRename.2 wrote synced
  have storageEffect := (observe afterWrite.2).fileSyncEffect (observe beforeRename.2) bytes visible survivors
  let inode := handle.1.inode handle.2.1.description
  have stagedBytes : (inodes beforeRename.2).crashBytes inode = [stop.manifest] := by
    simpa [inode, payload, RunDirectoryInodeView.storageObservation] using storageEffect.bytes inode
  have syncedFrame := storageEffect.frames (footprint := (· ≠ stage)) (by
    intro path outside other named alias
    exact outside (privateSync path (alias ▸ named)))
  exact ⟨beforeWrite, inode, earlier, (congrFun visible stage).trans bound, stagedBytes,
    (frame.preservesCheckpointFootprint (fun _ _ => rfl) privateWrite (fun _ outside => outside)).trans syncedFrame⟩

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

/-- The sampled canonical manifest and every framed path come from the
same chosen survivor. File-sync and namespace effects are kept separate. -/
private structure CheckpointManifestChoiceEffect (dir : DiskDirectory) (staged : Nat)
    (mayReplace settled : Bool) (scope : FilePath → Prop) (before after : CheckpointStorageObservation) : Prop where
  visible : before.files.Frames scope after.files
  survivors : ∀ names ∈ after.crashNames, ∃ prior ∈ before.crashNames,
    ((mayReplace = true ∧ names (dir.file .manifest) = some staged) ∨
      (settled = false ∧ names (dir.file .manifest) = prior (dir.file .manifest))) ∧
    ∀ path, scope path → names path = prior path
  oldBytes : ∀ inode, before.files.names (dir.file .manifest) = some inode →
    after.files.bytes inode = before.files.bytes inode
  newBytes : mayReplace = true → after.files.bytes staged = before.files.bytes staged

private theorem CheckpointManifestRenameEffect.followedByDirectory
    {dir : DiskDirectory} {staged : Nat} {scope : FilePath → Prop}
    {before renamed after : CheckpointStorageObservation} {effective : Bool}
    (rename : CheckpointManifestRenameEffect dir staged scope before renamed)
    (barrier : CheckpointManifestDirectoryEffect dir effective scope renamed after) :
    CheckpointManifestChoiceEffect dir staged true effective scope before after := by
  have bytes := barrier.bytes.trans rename.bytes
  refine ⟨fun path kept => ⟨(barrier.visible path kept).trans (rename.visible path kept),
    fun inode _ => congrFun bytes inode⟩, ?_, fun inode _ => congrFun bytes inode, fun _ => congrFun bytes staged⟩
  intro names survives
  obtain ⟨middle, possible, binding, kept⟩ := barrier.survivors names survives
  obtain ⟨prior, admitted, renameChoice, preserved⟩ := rename.survivors middle possible
  refine ⟨prior, admitted, ?_, fun path inScope => (kept path inScope).trans (preserved path inScope)⟩
  cases effective with
  | true => exact .inl ⟨rfl, binding.trans rename.canonical⟩
  | false =>
    rcases renameChoice with new | old
    · exact .inl ⟨rfl, binding.trans new⟩
    · exact .inr ⟨rfl, binding.trans old⟩

private abbrev NativeCheckpointSourcePrefix.ManifestSelection
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (reached : CheckpointWorld heap) (scope : FilePath → Prop)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (mayReplace settled : Bool) : Prop :=
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
        ((runSteps stop.next.table.runs.length).length + 4 + (if settled then 1 else 0)) = some published ∧
      (names (dir.file .manifest)).map contents ∈ published.manifest.crashImages ∧
      ((mayReplace = true ∧ (names (dir.file .manifest)).map contents = some stop.manifest) ∨
        (settled = false ∧ (names (dir.file .manifest)).map contents = writer.target.pair.manifest)) ∧
      (∀ path, scope path → ∀ payload,
        (observe beforeWrite.2).storageObservation.files.Stored path payload →
        (∀ prior ∈ (observe beforeWrite.2).crashBindings, prior path = (observe beforeWrite.2).visible path) →
        (names path).map contents = some payload) ∧
      (∀ index, published.durable stop.next.generation index = plan.files[index]?) ∧
      ∀ generation, generation ≠ stop.next.generation → ∀ index,
        published.durable generation index = writer.published.durable generation index

/-- Select the manifest on one sampled map using the same staged bytes
and preserved run/WAL paths for both publication exits. -/
private theorem NativeCheckpointSourcePrefix.selectsSampledManifest
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    {beforeRename : CheckpointWorld heap}
    (throughStage : let perform := primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++
        [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeRename)
    (stageEffects : CheckpointManifestStageEffects stop inodes runs observe)
    (oldStorage : ∀ beforeWrite : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM
        (primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest)).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite →
      NativeReadyStorage current.current.ready.state (observe beforeWrite.2).storageObservation)
    (scope : FilePath → Prop) (outsideStage : ∀ path, scope path → path ≠ (dbDir).file .stagedManifest)
    (mayReplace settled : Bool)
    (publicationEffect : ∀ staged, (observe beforeRename.2).visible ((dbDir).file .stagedManifest) = some staged →
      CheckpointManifestChoiceEffect dbDir staged mayReplace settled scope
        (observe beforeRename.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    stop.ManifestSelection inodes observe reached scope names contents mayReplace settled := by
  unfold NativeCheckpointSourcePrefix.ManifestSelection
  intro dir perform writer plan
  let canonical := dir.file .manifest
  obtain ⟨beforeWrite, staged, through, stagedName, stagedBytes, staging⟩ :=
    stop.stageManifestBeforeRename throughStage inodes runs observe stageEffects
  have publication := publicationEffect staged stagedName
  have publishedFrame : (observe beforeRename.2).storageObservation.Frames scope
      (observe reached.2).storageObservation := by
    refine ⟨publication.visible, ?_⟩
    intro after survives
    obtain ⟨prior, before, _, retained⟩ := publication.survivors after survives
    exact ⟨prior, before, retained⟩
  have choice : (mayReplace = true ∧ (names canonical).map contents = some stop.manifest) ∨
      (settled = false ∧ (names canonical).map contents = writer.target.pair.manifest) := by
    obtain ⟨prior, earlier, selected, _⟩ := publication.survivors names chosen
    rcases selected with ⟨applied, new⟩ | ⟨notSettled, old⟩
    · refine .inl ⟨applied, ?_⟩
      have payload := sampled canonical (.inl rfl) staged new
      rw [show (inodes reached.2).crashBytes staged = (inodes beforeRename.2).crashBytes staged from
        publication.newBytes applied, stagedBytes] at payload
      rw [new, Option.map_some, List.mem_singleton.mp payload]
    · refine .inr ⟨notSettled, ?_⟩
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
      have selectedOld := old.trans priorSettled
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
        have durable : (inodes reached.2).crashBytes inode = [bytes] :=
          (publication.oldBytes inode (held.1.trans bound)).trans ((held.2 inode bound).trans stored)
        rw [durable] at payload
        rw [actual, Option.map_some, List.mem_singleton.mp payload]
  have valid := current.current.ready.readPrefix.refines.1
  have prepared : CheckpointPreflight (.ready writer.installed) (.ok (stop.next, stop.manifest)) :=
    valid.phase ▸ stop.prepared
  obtain ⟨published, executed, _, choices, written, prior⟩ :=
    prepared.finalDirectoryPublication valid.retained settled
  have frame := (staging.weaken outsideStage).trans publishedFrame
  refine ⟨beforeWrite, published, through, frame, executed, ?_, choice, ?_, written, prior⟩
  · rw [choices]
    rcases choice with ⟨_, new⟩ | ⟨notEffective, old⟩
    · rw [new]
      cases settled <;> simp
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

/-- At this source stop a chosen map supplies either the actually staged
manifest or the prior settled manifest. The same map frames the other
scoped paths from before the staged write. -/
theorem NativeCheckpointSourceStop.selectsFinalManifest
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (stageEffects : CheckpointManifestStageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
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
    (directoryEffect : CheckpointManifestDirectoryEffect dbDir effective scope
      (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    stop.toNativeCheckpointSourcePrefix.ManifestSelection inodes observe reached scope names contents true effective := by
  obtain ⟨beforeRename, _, _, throughStage, renamed, _⟩ :=
    stop.manifestDirectoryFollowsRename
  exact stop.toNativeCheckpointSourcePrefix.selectsSampledManifest inodes runs observe throughStage stageEffects
      oldStorage scope outsideStage true effective
      (fun staged bound => (renameEffect beforeRename.2 staged bound renamed).followedByDirectory
        directoryEffect) names chosen contents sampled
/-- A before-effect rename error frames the canonical manifest and other
protected paths on one predecessor map. An after-effect error has the
local effect of an atomic rename. Both admit separate crash choices
outside the protected footprint. -/
abbrev NativeCheckpointSourceError.ManifestRenameEffect
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (scope : FilePath → Prop) (effective : Bool) : Prop :=
  ∀ staged, (observe stop.atIssue.2).visible ((dbDir).file .stagedManifest) = some staged →
    primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest)
      stop.atIssue.2 = .error cause reached.2 →
    if effective then
      CheckpointManifestRenameEffect dbDir staged scope
        (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation
    else (observe stop.atIssue.2).storageObservation.Frames
      (fun path => path = (dbDir).file .manifest ∨ scope path) (observe reached.2).storageObservation

/-- A returned rename error may leave the old name unchanged or may
have already published the staged inode. No directory sync occurred.
Before the effect the sampled map selects the previous checkpoint. -/
theorem NativeCheckpointSourceError.selectsManifestAtRenameError
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (stageEffects : CheckpointManifestStageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
    (oldStorage : ∀ beforeWrite : CheckpointWorld heap,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM
        (primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest)).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite →
      NativeReadyStorage current.current.ready.state (observe beforeWrite.2).storageObservation)
    (scope : FilePath → Prop) (outsideStage : ∀ path, scope path → path ≠ (dbDir).file .stagedManifest)
    (effective : Bool)
    (renameEffect : stop.ManifestRenameEffect inodes observe scope effective)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    stop.toNativeCheckpointSourcePrefix.ManifestSelection inodes observe reached scope names contents effective false := by
  have throughStage := stop.returnedPrefix
  rw [prefixBeforeManifestRename stop.ordered] at throughStage
  obtain ⟨failed, _⟩ := stop.manifestRenameFailed
  have observedRename := fun staged bound => renameEffect staged bound failed
  have selection (staged) (bound : (observe stop.atIssue.2).visible ((dbDir).file .stagedManifest) = some staged) :
      CheckpointManifestChoiceEffect dbDir staged effective false scope
        (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation := by
    have effect := observedRename staged bound
    cases effective with
    | false =>
      refine ⟨fun path kept => effect.visible path (.inr kept), ?_,
        (effect.visible _ (.inl rfl)).2, fun impossible => Bool.noConfusion impossible⟩
      intro after survives
      obtain ⟨prior, possible, kept⟩ := effect.survivors after survives
      exact ⟨prior, possible, .inr ⟨rfl, kept _ (.inl rfl)⟩, fun path inScope => kept path (.inr inScope)⟩
    | true =>
      have applied : CheckpointManifestRenameEffect dbDir staged scope
          (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation := effect
      refine ⟨fun path kept => ⟨applied.visible path kept, fun inode _ => congrFun applied.bytes inode⟩, ?_,
        fun inode _ => congrFun applied.bytes inode, fun _ => congrFun applied.bytes staged⟩
      intro after survives
      obtain ⟨prior, possible, selected, frames⟩ := applied.survivors after survives
      exact ⟨prior, possible, selected.imp (fun new => ⟨rfl, new⟩) (fun old => ⟨rfl, old⟩), frames⟩
  exact stop.toNativeCheckpointSourcePrefix.selectsSampledManifest inodes runs observe throughStage stageEffects
      oldStorage scope outsideStage effective false selection names chosen contents sampled
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

/-- Local run, directory and stage effects shared before publication
chooses either the old or new manifest. The reached writer supplies the
protected storage these effects carry forward. -/
structure CheckpointPublicationStorageEffects
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap)) where
  phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.poisoned).storageObservation
  runEffects : CheckpointRunPrefixEffects stop stop.next.table.runs.length inodes runs observe
  writtenPayload : ∀ index < stop.next.table.runs.length, ∀ before after payload handle,
      primitives.cached.writeRun ((dbDir).file (.run stop.next.generation index))
        payload before = .ok handle after →
      (inodes after).visible (handle.1.inode handle.2.1.description) = payload
  runBarrier : ∀ handle (atIssue after : CheckpointWorld heap),
      atIssue.1.directory = some handle → fsync handle atIssue.2 = .ok (.ok ()) after.2 →
      let state := current.current.ready.state
      CheckpointRunsDirectoryEffect (dbDir).path
        (fun path => (state.crashPath path ∧ path ≠ (dbDir).path) ∨
          ∃ index < stop.next.table.runs.length, path = (dbDir).file (.run stop.next.generation index))
        (observe atIssue.2).storageObservation (observe after.2).storageObservation
  stageEffects : CheckpointManifestStageEffects stop inodes runs observe
  scope : FilePath → Prop
  outsideStage : ∀ path, scope path → path ≠ (dbDir).file .stagedManifest
  retained : ∀ path, current.current.ready.state.crashPath path → path ≠ (dbDir).file .manifest → scope path
  newRuns : ∀ index < stop.next.table.runs.length, scope ((dbDir).file (.run stop.next.generation index))
/-- The returned manifest rename fixes the visible namespace at the final
directory barrier. The barrier has its own durability effect. -/
structure RenamedCheckpointStorageEffects
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    extends CheckpointPublicationStorageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe where
  renameEffect : ∀ (before : heap) staged,
      (observe before).visible ((dbDir).file .stagedManifest) = some staged →
      primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest) before = .ok () stop.atIssue.2 →
      CheckpointManifestRenameEffect dbDir staged scope
        (observe before).storageObservation (observe stop.atIssue.2).storageObservation

/-- The sampled files carry the marker, aligned WAL, selected run map
and complete logical replay needed by the actual opener. -/
abbrev NativeCheckpointSourcePrefix.SampledReplay
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray) : Prop :=
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
          RepresentsWalHistory writer.history model

private theorem NativeCheckpointSourcePrefix.replaysSampledManifest
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (storage : CheckpointPublicationStorageEffects stop inodes runs observe)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    {mayReplace settled : Bool}
    (manifestSelection : stop.ManifestSelection inodes observe reached storage.scope names contents mayReplace settled) :
    stop.SampledReplay names contents := by
  unfold NativeCheckpointSourcePrefix.SampledReplay
  intro dir writer pair actual files wal retry
  let state := current.current.ready.state
  have valid := current.current.ready.readPrefix.refines.1
  have prepared : CheckpointPreflight (.ready writer.installed) (.ok (stop.next, stop.manifest)) :=
    valid.phase ▸ stop.prepared
  have oldStorage := stop.priorStorageBeforeStaging inodes runs observe initial storage.phaseStorage storage.runEffects
    (fun handle entry after cached synced => (storage.runBarrier handle entry after cached synced).weaken (fun _ => .inl))
  obtain ⟨beforeWrite, published, through, frame, executed, manifest, choice, sample, newModel, oldModel⟩ :=
    manifestSelection
  have runStorage := stop.newRunsSettledAtBarrier through inodes runs observe storage.runEffects
    storage.writtenPayload
    (fun handle entry after cached synced => (storage.runBarrier handle entry after cached synced).weaken (fun _ => .inr))
  have stable := oldStorage beforeWrite through
  have includeWal : ∀ path, checkpointWalPath dir writer path → storage.scope path :=
    fun path walPath => storage.retained path (.inr (.inr (.inr (.inl walPath)))) (walPath_ne_manifest walPath)
  have rootInScope : storage.scope dir.path :=
    storage.retained _ (.inl rfl) (file_ne_directory dir .manifest).symm
  have lockInScope : storage.scope (dir.file .lock) := storage.retained _ (.inr (.inl rfl)) (by
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
      storage.scope (dir.file (.run metadata.header.generation index)) :=
    storage.retained _ (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, selected, decoded, within, rfl⟩))))
      (runFile_ne_manifest dir metadata.header.generation index)
  have agrees : SelectedRunsAgree pair.manifest actual published.durable :=
    prepared.sampledSettledRunsAgree valid stable (choice.imp And.right And.right) newModel oldModel
      (fun index within run found => by
        obtain ⟨inode, bound, stored, settled⟩ := runStorage index within run found
        exact ⟨⟨inode, bound, stored⟩, fun map allowed => (settled map allowed).trans bound.symm⟩)
      storage.scope storage.newRuns oldRuns names contents sample
  obtain ⟨layout, wellFormed, replay⟩ := prepared.publicationReplays valid.retained executed
  obtain ⟨_, accepted, range, decoded, upto, checkpoint, table, model, selected, generation, recovered,
    clock, refines, history⟩ := replay pair (List.mem_cons_of_mem _ survives)
  obtain ⟨walLayout, walValid, alignedLayout, _, keeper, aligned, descriptors, offsets, openPlan⟩ :=
    layout.checkpointCrashReopen wellFormed survives decoded upto
  refine ⟨bindings, markerStored, segmentStored, published, alignedLayout, survives, walLayout, walValid, keeper,
    aligned, descriptors, offsets, openPlan, agrees, ?_, range, decoded, upto, checkpoint, table, model,
    SelectedIntegrityCheckpoint.withRunMap selected agrees.symm, generation, recovered, clock, refines, history⟩
  exact agrees.acceptsVersioned decoded accepted
/-- Read the marker and selected run bytes from the very same crash map as
the final manifest. Checked replay applies to this physical run map. -/
theorem NativeCheckpointSourceStop.replaysSampledFinalCheckpoint
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (storage : RenamedCheckpointStorageEffects stop inodes runs observe) (effective : Bool)
    (directoryEffect : CheckpointManifestDirectoryEffect dbDir effective storage.scope
      (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    stop.toNativeCheckpointSourcePrefix.SampledReplay names contents := by
  let prior := stop.toNativeCheckpointSourcePrefix
  let common := storage.toCheckpointPublicationStorageEffects
  have oldStorage := prior.priorStorageBeforeStaging inodes runs observe initial common.phaseStorage common.runEffects
    (fun handle entry after cached synced => (common.runBarrier handle entry after cached synced).weaken (fun _ => .inl))
  have manifest := stop.selectsFinalManifest inodes runs observe common.stageEffects oldStorage common.scope
    common.outsideStage storage.renameEffect effective directoryEffect names chosen contents sampled
  exact prior.replaysSampledManifest inodes runs observe initial common names chosen contents sampled manifest

/-- The physical rename effect determines which canonical manifest
bytes this crash sample can select. A before-effect error can only
select the previous manifest, including its absence. -/
abbrev NativeCheckpointSourceError.SelectsManifest
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (effective : Bool) (names : FilePath → Option Nat) (contents : Nat → ByteArray) : Prop :=
  let selected := (names ((dbDir).file .manifest)).map contents
  (effective = true ∧ selected = some stop.manifest) ∨ selected = current.current.ready.state.writer.target.pair.manifest

/-- The earlier returned rename error yields the same exact recovery
files as a final barrier stop. Only its local namespace effect differs. -/
theorem NativeCheckpointSourceError.replaysSampledRenameError
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (storage : CheckpointPublicationStorageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
    (effective : Bool)
    (renameEffect : stop.ManifestRenameEffect inodes observe storage.scope effective)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) :
    stop.SelectsManifest effective names contents ∧ stop.toNativeCheckpointSourcePrefix.SampledReplay names contents := by
  let prior := stop.toNativeCheckpointSourcePrefix
  have oldStorage := prior.priorStorageBeforeStaging inodes runs observe initial storage.phaseStorage storage.runEffects
    (fun handle entry after cached synced => (storage.runBarrier handle entry after cached synced).weaken (fun _ => .inl))
  have manifest := stop.selectsManifestAtRenameError inodes runs observe storage.stageEffects oldStorage storage.scope
    storage.outsideStage effective renameEffect names chosen contents sampled
  have choice : stop.SelectsManifest effective names contents := by
    obtain ⟨_, _, _, _, _, _, selected, _⟩ := manifest
    exact selected.imp_right And.right
  exact ⟨choice, prior.replaysSampledManifest inodes runs observe initial storage names chosen contents sampled manifest⟩

/-- The successful manifest staging keeps the earlier WAL catalog,
including unbound offset names, before either rename outcome. -/
private theorem NativeCheckpointSourcePrefix.walNamesThroughStaging
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : CheckpointPublicationStorageEffects stop inodes runs observe)
    {lower upper : Nat} {beforeRename : CheckpointWorld heap}
    (phaseNames : opened.set opened.phase .poisoned current.reached = .ok () stop.poisoned →
      WalNamePresenceFrame dbDir lower upper (observe current.reached).storageObservation (observe stop.poisoned).storageObservation)
    (runNames : CheckpointRunDirectoryWalNames dbDir fsync (fun atHeap => (observe atHeap).storageObservation) lower upper)
    (through : let perform := primitives.checkpointStepUntilStop dbDir fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++
        [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeRename) :
    WalNamePresenceFrame dbDir lower upper (observe current.reached).storageObservation
      (observe beforeRename.2).storageObservation := by
  obtain ⟨_, _, beforeStaging, _, _, stored⟩ :=
    stop.stageManifestBeforeRename through inodes runs observe storage.stageEffects
  have beforeStage := stop.walNamesBeforeStagedManifest inodes runs observe phaseNames storage.runEffects
    storage.runBarrier runNames beforeStaging
  refine beforeStage.trans (.ofStorageFrame stored ?_)
  intro start _ _ collision
  obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive collision.symm
  cases impossible

/-- Recover the bounded WAL window from the same survivor map as the
manifest at the final directory fsync stop. -/
theorem NativeCheckpointSourceStop.sampledFinalWalWindow
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : CheckpointPublicationStorageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
    {lower upper : Nat}
    (initial : current.current.ready.state.writer.wal.SettledNamespaceWindow dbDir lower upper
      (observe current.reached).storageObservation)
    (phaseNames : opened.set opened.phase .poisoned current.reached = .ok () stop.poisoned →
      WalNamePresenceFrame dbDir lower upper (observe current.reached).storageObservation (observe stop.poisoned).storageObservation)
    (runNames : CheckpointRunDirectoryWalNames dbDir fsync (fun atHeap => (observe atHeap).storageObservation) lower upper)
    (renameNames : ∀ before, primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest) before =
      .ok () stop.atIssue.2 → WalNamePresenceFrame dbDir lower upper (observe before).storageObservation
        (observe stop.atIssue.2).storageObservation)
    (directoryNames : ∀ (handle : CheckpointOpenHandle) atSync,
      stop.atIssue.1.resolve (dbDir).path (dbDir).path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atSync) → fsync handle atSync = .error reason reached.2 →
      WalNamePresenceFrame dbDir lower upper (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings) :
    current.current.ready.state.writer.wal.NamespaceWindow dbDir lower upper names := by
  obtain ⟨beforeRename, handle, atSync, through, renamed, _, resolved, stopped⟩ := stop.manifestDirectoryFollowsRename
  have prefixFrame := stop.toNativeCheckpointSourcePrefix.walNamesThroughStaging
    inodes runs observe storage phaseNames runNames through
  have reachedFrame := (prefixFrame.trans (renameNames beforeRename.2 renamed)).trans
    (directoryNames handle atSync resolved stopped)
  exact (reachedFrame.preservesNamespaceWindow initial).2 names chosen

/-- A returned manifest rename error preserves the bounded WAL window
on the exact map used for the next open, independently of its manifest choice. -/
theorem NativeCheckpointSourceError.sampledRenameErrorWalWindow
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : CheckpointPublicationStorageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
    {lower upper : Nat}
    (initial : current.current.ready.state.writer.wal.SettledNamespaceWindow dbDir lower upper
      (observe current.reached).storageObservation)
    (phaseNames : opened.set opened.phase .poisoned current.reached = .ok () stop.poisoned →
      WalNamePresenceFrame dbDir lower upper (observe current.reached).storageObservation (observe stop.poisoned).storageObservation)
    (runNames : CheckpointRunDirectoryWalNames dbDir fsync (fun atHeap => (observe atHeap).storageObservation) lower upper)
    (renameNames : primitives.rename ((dbDir).file .stagedManifest) ((dbDir).file .manifest) stop.atIssue.2 =
      .error cause reached.2 → WalNamePresenceFrame dbDir lower upper (observe stop.atIssue.2).storageObservation
        (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings) :
    current.current.ready.state.writer.wal.NamespaceWindow dbDir lower upper names := by
  have through := stop.returnedPrefix
  rw [prefixBeforeManifestRename stop.ordered] at through
  obtain ⟨failed, _⟩ := stop.manifestRenameFailed
  have prefixFrame := stop.toNativeCheckpointSourcePrefix.walNamesThroughStaging
    inodes runs observe storage phaseNames runNames through
  exact ((prefixFrame.trans (renameNames failed)).preservesNamespaceWindow initial).2 names chosen

end Alvoki.Storage.DiskSession
