import Alvoki.Storage.Disk.CheckpointRunBarrierReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- Both early manifest actions precede publication at the live name. -/
inductive CheckpointManifestStage where
  | write
  | sync

private def CheckpointManifestStage.completed : CheckpointManifestStage → List Step
  | .write => []
  | .sync => [.manifest .writeStaged]

private def CheckpointManifestStage.current : CheckpointManifestStage → Step
  | .write => .manifest .writeStaged
  | .sync => .manifest .syncStaged

private def CheckpointManifestStage.manifest (point : CheckpointManifestStage) (prior : Publication.Image)
    (bytes : ByteArray) (effective : Bool) : Publication.Image :=
  match point with
  | .write => if effective then { prior with staged := some (bytes, false) } else prior
  | .sync => { prior with staged := some (bytes, effective) }

private theorem CheckpointManifestStage.keepsChoices (point : CheckpointManifestStage)
    (prior : Publication.Image) (bytes : ByteArray) (effective : Bool) :
    (point.manifest prior bytes effective).crashImages = prior.crashImages := by
  cases point <;> cases effective <;> rfl

private theorem execute_atStage (initial : Image) (next : VersionedRunSet) (written : Image)
    (runs : initial.execute next.runSet (runSteps next.files.length ++ [.syncRunsDirectory]) = some written)
    (sameManifest : written.manifest = initial.manifest) (point : CheckpointManifestStage) (effective : Bool)
    {count : Nat} (counted : next.files.length = count) {bytes : ByteArray} (encoded : next.manifest.encode = bytes) :
    initial.executeVersioned next
      ((runSteps count).length + 1 + (point.completed.length + if effective then 1 else 0)) =
        some { written with manifest := point.manifest initial.manifest bytes effective } := by
  subst count
  let barrier := runSteps next.files.length ++ [Step.syncRunsDirectory]
  have length : barrier.length = (runSteps next.files.length).length + 1 := by simp [barrier]
  rw [← length, Image.executeVersioned]
  change (do
    let step ← initial.execute next.runSet (barrier.take (barrier.length + (point.completed.length +
      if effective then 1 else 0)))
    let manifest ← step.manifest.execute next.manifest.encode (Publication.steps.take
      (barrier.length + (point.completed.length + if effective then 1 else 0) - barrier.length))
    return { step with manifest }) = _
  rw [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  change initial.execute next.runSet barrier >>= _ = _
  rw [runs]
  simp only [Bind.bind, Option.bind]
  rw [sameManifest, encoded]
  cases point <;> cases effective <;> rfl

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage
private abbrev Stage := FilePath → ByteArray → EStateM IO.Error WalInodeImage Handle

/-- A stage write is the first manifest callback. Reaching the file sync
requires that this same callback returned a handle for the written bytes.
The interruption report records whether that file sync took effect. -/
inductive ManifestStageReached (stage : Stage) (path : FilePath) (bytes : ByteArray) (directorySettled : State)
    (bindings : WalInodeImage → FilePath → Option Nat) (interrupted : WalInodeImage) (effective : Bool) :
    CheckpointManifestStage → State → Type where
  | write : ManifestStageReached stage path bytes directorySettled bindings interrupted effective .write directorySettled
  | sync (handle : Handle) (written : WalInodeImage)
      (returned : stage path bytes directorySettled.2 = .ok handle written)
      (live : handle.2 ∈ handle.1.slots)
      (bound : bindings written path = some (handle.1.inode handle.2.description))
      (contents : written.visible (handle.1.inode handle.2.description) = bytes)
      (effect : interrupted = if effective then written.completeFileSync (handle.1.inode handle.2.description) else written) :
      ManifestStageReached stage path bytes directorySettled bindings interrupted effective .sync
        (directorySettled.1.remember path handle, written)

private theorem stagedManifest_ne_directory (directory : DiskDirectory) :
    directory.file .stagedManifest ≠ directory.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ "MANIFEST.next").length = directory.path.toString.length at length
  simp only [String.length_append] at length
  have slash : "/".length = 1 := rfl
  omega

/-- The issued callback is the reserved stage write or the direct sync
of the captured stage handle in the pending cache. -/
def CheckpointManifestStage.Issues (point : CheckpointManifestStage) (path : FilePath) (bytes : ByteArray)
    (stage : Stage) (fsync : Handle → EStateM IO.Error WalInodeImage Unit)
    (directorySettled atCut : State) (bindings : WalInodeImage → FilePath → Option Nat)
    (interrupted : WalInodeImage) (effective : Bool) (current : EStateM IO.Error State Unit) : Prop :=
  match point with
  | .write => current atCut = stageFreshWithCache path bytes stage atCut
  | .sync => ∃ handle written,
    let inode := handle.1.inode handle.2.description
    atCut = (directorySettled.1.remember path handle, written) ∧
    handle.2 ∈ handle.1.slots ∧ bindings written path = some inode ∧ written.visible inode = bytes ∧
    interrupted = (if effective then written.completeFileSync inode else written) ∧
    current atCut = SyncPathGroup.run (m := EStateM IO.Error State)
      (fun _ _ => withCache (directorySettled.1.consume path) (fsync handle written)) #[path] atCut

/-- The stable manifest and the settled run bindings at an issued stage
write or staged-file sync. Scratch contents never enter selection. -/
structure CheckpointManifestStageCut {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (published : Image) (runs : RunUnlinkImage)
    (manifestCandidates : List (Option ByteArray)) : Prop where
  current : cut.current = .manifest .writeStaged ∨ cut.current = .manifest .syncStaged
  executed : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published
  manifestChoices : published.manifest.crashImages = [before.wal.directory.active.manifest]
  physicalChoice : ∀ bytes ∈ manifestCandidates, bytes = before.wal.directory.active.manifest
  olderRuns : ∀ older, older ≠ SegmentedCheckpointReport.generation before → ∀ index,
    published.durable older index = before.published.durable older index
  runChoices : runs.crashImages = [runs.visible]

/-- The actual prefix reaches the manifest write or staged-file sync
after every run-file barrier and a successful run-directory barrier.
Physical crash choices at the live manifest still identify the old inode.
A partially written scratch is permitted during the issued write. -/
theorem CheckpointPowerCut.atManifestStage {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (point : CheckpointManifestStage)
    (writeRun : FilePath → ByteArray → EStateM IO.Error State Unit) (stage : Stage)
    (openRead : FilePath → EStateM IO.Error WalInodeImage Handle)
    (fsync : Handle → EStateM IO.Error WalInodeImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error State Unit)
    (atRun : Nat → State) (directoryHandle : Handle) (directorySettled atCut : State) (interrupted : WalInodeImage)
    (runs : WalInodeImage → RunUnlinkImage) (bindings : WalInodeImage → FilePath → Option Nat)
    (crashBindings : List (Option Nat)) :
    let count := cut.checkpoint.table.runs.length
    let generation := SegmentedCheckpointReport.generation before
    let path := directory.file .stagedManifest
    let live := directory.file .manifest
    let prior := bindings directorySettled.2 live
    let perform := performCheckpointFileStep directory generation cut.checkpoint.table.runs.toArray
      path cut.checkpoint.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun (fun name bytes => stageFreshWithCache name bytes stage)
      (SyncPathGroup.run (SyncHandleRouting.sync directory.path openRead fsync)) rename
    cut.completed = runSteps count ++ [.syncRunsDirectory] ++ point.completed →
    (∀ index < count, (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
      .ok () (atRun (index + 1))) →
    (atRun count).1.directory = some directoryHandle →
    fsync directoryHandle (atRun count).2 = .ok () directorySettled.2 →
    directorySettled.1 = (atRun count).1 →
    ManifestStageReached stage path cut.checkpoint.manifest directorySettled bindings interrupted cut.tookEffect point atCut →
    runs directorySettled.2 = (runs (atRun count).2).syncDirectory →
    runs interrupted = runs directorySettled.2 →
    (∀ index < count, (runs (atRun count).2).visible generation index = cut.checkpoint.plan.files[index]?) →
    prior.map directorySettled.2.visible = before.wal.directory.active.manifest →
    (∀ chosen ∈ crashBindings, chosen = prior) →
    (∀ old, prior = some old → interrupted.crashBytes old = [directorySettled.2.visible old]) →
    cut.current = point.current ∧
    (cut.completed.forM perform) (atRun 0) = .ok () atCut ∧
    point.Issues path cut.checkpoint.manifest stage fsync directorySettled atCut bindings interrupted cut.tookEffect
      (perform cut.current) ∧
    ∃ published, CheckpointManifestStageCut cut published (runs interrupted)
      (crashBindings.flatMap (manifestCrashBytes interrupted)) ∧
      ∀ index < count, (runs interrupted).guaranteed generation index = published.durable generation index := by
  intro count generation path live prior perform completed pairs directoryCaptured syncedDirectory cacheRetained
    reached directoryNames runNames syncedRuns oldVisible choices oldBytes
  have current : cut.current = point.current := by
    have schedule := cut.schedule
    rw [completed] at schedule
    change runSteps count ++ [.syncRunsDirectory] ++ Publication.steps.map Step.manifest =
      (runSteps count ++ [.syncRunsDirectory] ++ point.completed) ++ cut.current :: cut.remaining at schedule
    have rest : [.syncRunsDirectory] ++ Publication.steps.map Step.manifest =
        [.syncRunsDirectory] ++ point.completed ++ cut.current :: cut.remaining := by
      apply List.append_cancel_left (as := runSteps count)
      simpa only [List.append_assoc] using schedule
    have next := congrArg (fun (steps : List Step) => steps[point.completed.length + 1]?) rest
    cases point <;> simpa [CheckpointManifestStage.current, CheckpointManifestStage.completed, Publication.steps] using next.symm
  have prefixRan := runSteps_returned perform count atRun pairs
  have directoryReturned : perform .syncRunsDirectory (atRun count) = .ok () directorySettled := by
    have routed : SyncHandleRouting.sync directory.path openRead fsync directory.path (atRun count) =
        withCache (atRun count).1 (fsync directoryHandle (atRun count).2) := by
      simp [SyncHandleRouting.sync, Cache.resolve, directoryCaptured]
    change SyncPathGroup.run (SyncHandleRouting.sync directory.path openRead fsync)
      #[directory.path] (atRun count) = _
    rw [SyncPathGroup.run_single (SyncHandleRouting.sync directory.path openRead fsync), routed, syncedDirectory]
    exact congrArg (EStateM.Result.ok ()) (Prod.ext cacheRetained.symm rfl)
  have completion : (cut.completed.forM perform) (atRun 0) = .ok () atCut := by
    rw [completed, List.append_assoc, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    simp only [Bind.bind, EStateM.bind, prefixRan]
    cases reached with
    | write =>
      simp [CheckpointManifestStage.completed, List.forM_eq_forM, List.forM_cons, List.forM_nil, Bind.bind,
        EStateM.bind, directoryReturned, Pure.pure, EStateM.pure]
    | sync handle written returned =>
      have wrote : perform (.manifest .writeStaged) directorySettled =
          .ok () (directorySettled.1.remember path handle, written) := by
        change stageFreshWithCache path cut.checkpoint.manifest stage directorySettled = _
        simp only [stageFreshWithCache, returned]
      simp [CheckpointManifestStage.completed, List.forM_eq_forM, List.forM_cons, List.forM_nil, Bind.bind,
        EStateM.bind, directoryReturned, wrote, Pure.pure, EStateM.pure]
  have issued : point.Issues path cut.checkpoint.manifest stage fsync directorySettled atCut bindings interrupted cut.tookEffect
      (perform cut.current) := by
    cases reached with
    | write =>
      change perform cut.current directorySettled = stageFreshWithCache path cut.checkpoint.manifest stage directorySettled
      rw [current]
      rfl
    | sync handle written _ liveSlot bound contents effect =>
      let cached (_ : FilePath) : EStateM IO.Error State Unit :=
        fun _ => withCache (directorySettled.1.consume path) (fsync handle written)
      refine ⟨handle, written, rfl, liveSlot, bound, contents, effect, ?_⟩
      rw [current]
      change SyncPathGroup.run (SyncHandleRouting.sync directory.path openRead fsync) #[path]
          (directorySettled.1.remember path handle, written) =
        SyncPathGroup.run cached #[path] (directorySettled.1.remember path handle, written)
      have separate : path ≠ directory.path := stagedManifest_ne_directory directory
      have routed : SyncHandleRouting.sync directory.path openRead fsync path
          (directorySettled.1.remember path handle, written) =
        cached path (directorySettled.1.remember path handle, written) := by
        rw [syncRemembered (cache := directorySettled.1) separate handle openRead fsync written]
        dsimp only [cached]
        cases fsync handle written <;> rfl
      rw [SyncPathGroup.run_single (SyncHandleRouting.sync directory.path openRead fsync), SyncPathGroup.run_single cached, routed]
  have physicalChoice : ∀ bytes ∈ crashBindings.flatMap (manifestCrashBytes interrupted),
      bytes = before.wal.directory.active.manifest := by
    intro bytes survives
    obtain ⟨chosen, member, payload⟩ := List.mem_flatMap.mp survives
    have selected := choices chosen member
    subst chosen
    cases binding : prior with
    | none =>
      simpa [manifestCrashBytes, binding, show before.wal.directory.active.manifest = none from
        by simpa [binding] using oldVisible.symm] using payload
    | some old =>
      have exact : some (directorySettled.2.visible old) = before.wal.directory.active.manifest := by
        simpa [binding] using oldVisible
      simpa [manifestCrashBytes, binding, oldBytes old binding, exact] using payload
  obtain ⟨written, ran, sameManifest, durable, older⟩ := checkpoint_runs_complete before.published cut.checkpoint.plan.runSet
  have countEq : cut.checkpoint.plan.files.length = count := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  have encoded : cut.checkpoint.plan.manifest.encode = cut.checkpoint.manifest := by
    have encoded := cut.encoded
    by_cases fits : (cut.checkpoint.table.runs.map (·.run.bytes)).all
        (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact Except.ok.inj ((encodeCheckpointIntegrityManifest_exact generation
        (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))).symm.trans encoded)
    · simp [encodeCheckpointIntegrityManifest, fits, Bind.bind, Except.bind] at encoded
  have cutIndex : cut.checkpoint.cut =
      (runSteps count).length + 1 + (point.completed.length + if cut.tookEffect then 1 else 0) := by
    rw [cut.reachedCount.1, completed]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  let published := { written with manifest := point.manifest before.published.manifest cut.checkpoint.manifest cut.tookEffect }
  have oldManifest : before.published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  have cutPoint : cut.current = .manifest .writeStaged ∨ cut.current = .manifest .syncStaged := by
    rw [current]
    cases point <;> simp [CheckpointManifestStage.current]
  have executed : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published := by
    rw [cutIndex]
    exact execute_atStage before.published cut.checkpoint.plan written ran sameManifest point cut.tookEffect countEq encoded
  have settled : runs interrupted = (runs (atRun count).2).syncDirectory := runNames.trans directoryNames
  refine ⟨current, completion, issued, published, ⟨cutPoint, executed, (point.keepsChoices _ _ _).trans oldManifest, physicalChoice, older, ?_⟩, ?_⟩
  · simp [settled, RunUnlinkImage.syncDirectory, RunUnlinkImage.settled]
  · intro index within
    rw [settled]
    have exactly := congrArg Image.durable
      (RunUnlinkImage.project_settled (runs (atRun count).2).visible (.settled none))
    exact (congrFun (congrFun exactly generation) index).trans ((syncedRuns index within).trans (durable index).symm)


/-- A surviving map at a manifest stage cut is the settled run map.
The old manifest keeps selecting its original run bytes even after the
new run names became durable. The reported held reopen preserves the
submission log and returns exactly the prior checkpoint and WAL replay. -/
theorem CheckpointManifestStageCut.reopens {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} {cut : CheckpointPowerCut directory before}
    {published : Image} {runs : RunUnlinkImage} {manifestCandidates : List (Option ByteArray)}
    (observed : CheckpointManifestStageCut cut published runs manifestCandidates)
    (ready : before.RetainedReady directory writer) (manifest : Option ByteArray) (survivor : RunFiles)
    (manifestSurvives : manifest ∈ manifestCandidates) (survives : survivor ∈ runs.crashImages)
    (oldAgrees : SelectedRunsAgree before.wal.directory.active.manifest runs.visible before.published.durable)
    (retry : LockedFileState WalSegmentRepair.FileImage) :
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash
        ⟨manifest, before.wal.directory.active.walBoundary⟩ (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published { published with durable := survivor } →
    cut.HeldReopen input writer retry published manifest survivor ∧
      ∀ checkpoint, SelectedIntegrityCheckpoint survivor manifest checkpoint → checkpoint = before.checkpoint := by
  have oldManifest := observed.physicalChoice manifest manifestSurvives
  subst manifest
  have same : survivor = runs.visible := by simpa [observed.runChoices] using survives
  subst survivor
  have selected : before.wal.directory.active.manifest ∈ published.manifest.crashImages := by
    rw [observed.manifestChoices]
    exact List.mem_singleton_self _
  exact cut.reopensPriorCheckpoint ready published observed.executed selected observed.olderRuns _ oldAgrees retry

end Alvoki.Storage.DiskSession
