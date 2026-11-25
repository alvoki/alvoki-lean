import Alvoki.Storage.Disk.CheckpointManifestRenameCut

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev ManifestHandle := DescriptorInventory × DescriptorSlot
private abbrev ManifestState := Cache ManifestHandle × WalInodeImage

private def manifestInode (handle : ManifestHandle) : Nat := handle.1.inode handle.2.description

/-- The versioned checkpoint's concrete dispatch with reported callbacks. -/
structure CheckpointManifestDirectoryCalls where
  writeRun : FilePath → ByteArray → EStateM IO.Error ManifestState Unit
  stage : FilePath → ByteArray → EStateM IO.Error WalInodeImage ManifestHandle
  openRead : FilePath → EStateM IO.Error WalInodeImage ManifestHandle
  fsync : ManifestHandle → EStateM IO.Error WalInodeImage Unit
  rename : FilePath → FilePath → EStateM IO.Error ManifestState Unit

noncomputable def CheckpointManifestDirectoryCalls.perform {directory : DiskDirectory} {before : SegmentedWriterState}
    (calls : CheckpointManifestDirectoryCalls) (cut : CheckpointPowerCut directory before) :
    Step → EStateM IO.Error ManifestState Unit :=
  performCheckpointFileStep directory (SegmentedCheckpointReport.generation before) cut.checkpoint.table.runs.toArray
    (directory.file .stagedManifest) cut.checkpoint.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    calls.writeRun (fun path bytes => stageFreshWithCache path bytes calls.stage)
    (SyncPathGroup.run (sync directory.path calls.openRead calls.fsync)) calls.rename

/-- Each returned callback leaves the state used by the next one. The
same captured directory survives both barriers. The interrupted final
barrier has an effect report and no callback return. -/
structure CheckpointManifestDirectoryReached {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (calls : CheckpointManifestDirectoryCalls)
    (runEnd : ManifestState) (runs : ManifestState → RunUnlinkImage) where
  directoryHandle : ManifestHandle
  directoryCaptured : runEnd.1.directory = some directoryHandle
  drops : List LockReferenceDrop
  directoryLive : directoryHandle.2.reference ∈
    (directoryHandle.1.afterDrops drops).references directoryHandle.2.description
  directorySettled : WalInodeImage
  runSynced : calls.fsync directoryHandle runEnd.2 = .ok () directorySettled
  runNames : runs (runEnd.1, directorySettled) = (runs runEnd).syncDirectory
  stageHandle : ManifestHandle
  written : WalInodeImage
  staged : calls.stage (directory.file .stagedManifest) cut.checkpoint.manifest directorySettled = .ok stageHandle written
  stageLive : stageHandle.2 ∈ stageHandle.1.slots
  stageBytes : written.visible (manifestInode stageHandle) = cut.checkpoint.manifest
  synced : calls.fsync stageHandle written = .ok () (written.completeFileSync (manifestInode stageHandle))
  bindings : WalInodeImage → FilePath → Option Nat
  stageBinding : bindings (written.completeFileSync (manifestInode stageHandle))
    (directory.file .stagedManifest) = some (manifestInode stageHandle)
  oldVisible : (bindings (written.completeFileSync (manifestInode stageHandle))
    (directory.file .manifest)).map written.visible = before.wal.directory.active.manifest
  oldStable : ∀ inode, bindings (written.completeFileSync (manifestInode stageHandle))
    (directory.file .manifest) = some inode →
    (written.completeFileSync (manifestInode stageHandle)).crashBytes inode = [written.visible inode]
  renamed : WalInodeImage
  renameReturned : calls.rename (directory.file .stagedManifest) (directory.file .manifest)
    (runEnd.1.consume (directory.file .stagedManifest), written.completeFileSync (manifestInode stageHandle)) =
    .ok () (runEnd.1.consume (directory.file .stagedManifest), renamed)
  liveBinding : bindings renamed (directory.file .manifest) = some (manifestInode stageHandle)
  directoryBinding : bindings renamed directory.path = some (manifestInode directoryHandle)
  stageRunNames : runs (runEnd.1.remember (directory.file .stagedManifest) stageHandle, written) =
    runs (runEnd.1, directorySettled)
  syncRunNames : runs (runEnd.1.consume (directory.file .stagedManifest),
      written.completeFileSync (manifestInode stageHandle)) =
    runs (runEnd.1.remember (directory.file .stagedManifest) stageHandle, written)
  renameRunNames : runs (runEnd.1.consume (directory.file .stagedManifest), renamed) =
    runs (runEnd.1.consume (directory.file .stagedManifest), written.completeFileSync (manifestInode stageHandle))
  renameSurvivors : List (Option Nat)
  renameChoices : ∀ binding ∈ renameSurvivors, binding = some (manifestInode stageHandle) ∨
    binding = bindings (written.completeFileSync (manifestInode stageHandle)) (directory.file .manifest)
  renameBytes : ∀ binding, binding = some (manifestInode stageHandle) ∨ binding ∈ renameSurvivors →
    manifestCrashBytes renamed binding =
      manifestCrashBytes (written.completeFileSync (manifestInode stageHandle)) binding
  interrupted : WalInodeImage
  crashBindings : List (Option Nat)
  directoryEffect : crashBindings = if cut.tookEffect then [bindings renamed (directory.file .manifest)] else renameSurvivors
  directoryBytes : ∀ binding ∈ crashBindings, manifestCrashBytes interrupted binding = manifestCrashBytes renamed binding
  directoryRunNames : runs (runEnd.1.consume (directory.file .stagedManifest), interrupted) =
    (if cut.tookEffect then (runs (runEnd.1.consume (directory.file .stagedManifest), renamed)).syncDirectory
      else runs (runEnd.1.consume (directory.file .stagedManifest), renamed))

/-- The exact native namespace at a final directory cut and its relation
to the checkpoint selected by bounded recovery. -/
structure CheckpointManifestDirectoryCut {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (published : Image) (runs : RunUnlinkImage)
    (manifests : List (Option ByteArray)) : Prop where
  current : cut.current = .manifest .syncDirectory
  executed : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published
  liveManifest : published.manifest.active = some cut.checkpoint.manifest
  manifestChoices : published.manifest.crashImages = if cut.tookEffect then [some cut.checkpoint.manifest]
    else [some cut.checkpoint.manifest, before.wal.directory.active.manifest]
  admitted : ∀ manifest ∈ manifests, manifest ∈ published.manifest.crashImages
  effective : cut.tookEffect = true → manifests = [some cut.checkpoint.manifest]
  runChoices : runs.crashImages = [runs.visible]
  newRuns : ∀ index < cut.checkpoint.table.runs.length,
    runs.guaranteed (SegmentedCheckpointReport.generation before) index =
      published.durable (SegmentedCheckpointReport.generation before) index
  priorRuns : SelectedRunsAgree before.wal.directory.active.manifest runs.guaranteed published.durable

private theorem CheckpointPowerCut.finalDirectoryPublication {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged]) :
    ∃ published,
      before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published ∧
      published.manifest.active = some cut.checkpoint.manifest ∧
      published.manifest.crashImages = (if cut.tookEffect then [some cut.checkpoint.manifest]
        else [some cut.checkpoint.manifest, before.wal.directory.active.manifest]) ∧
      (∀ index, published.durable (SegmentedCheckpointReport.generation before) index = cut.checkpoint.plan.files[index]?) ∧
      ∀ generation, generation ≠ SegmentedCheckpointReport.generation before → ∀ index,
        published.durable generation index = before.published.durable generation index := by
  let count := cut.checkpoint.table.runs.length
  let generation := SegmentedCheckpointReport.generation before
  have planCount : cut.checkpoint.plan.files.length = count := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  have planBytes : cut.checkpoint.plan.manifest.encode = cut.checkpoint.manifest := by
    have encoded := cut.encoded
    by_cases fits : (cut.checkpoint.table.runs.map (·.run.bytes)).all
        (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact Except.ok.inj ((encodeCheckpointIntegrityManifest_exact generation
        (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))).symm.trans encoded)
    · simp [encodeCheckpointIntegrityManifest, fits, Bind.bind, Except.bind] at encoded
  have prior : before.published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  have cutLength : cut.checkpoint.cut = (runSteps count).length + 4 + (if cut.tookEffect then 1 else 0) := by
    rw [cut.reachedCount.1, completed, List.length_append]
    rfl
  cases effective : cut.tookEffect
  · obtain ⟨written, ran, same, durable, older⟩ := checkpoint_runs_complete before.published cut.checkpoint.plan.runSet
    let manifest : Publication.Image :=
      ⟨some cut.checkpoint.manifest, some cut.checkpoint.manifest :: before.published.manifest.crashImages, none⟩
    refine ⟨{ written with manifest }, ?_, rfl,
      by simpa [manifest] using congrArg (List.cons (some cut.checkpoint.manifest)) prior, durable, older⟩
    rw [cutLength, effective]
    exact before.published.executeVersioned_atManifestRename cut.checkpoint.plan written ran same planCount planBytes true
  · obtain ⟨published, ran, manifest, durable, older⟩ := checkpointVersioned_complete before.published cut.checkpoint.plan
    have exactLength : cut.checkpoint.cut = (steps cut.checkpoint.plan.files.length).length := by
      rw [cutLength, effective, planCount]
      simp [steps, Publication.steps]
    exact ⟨published, exactLength.symm ▸ ran, by simp [manifest, planBytes, Publication.Image.settled],
      by simp [manifest, planBytes, Publication.Image.settled], durable, older⟩

private theorem syncDirectorySelected (directory : DiskDirectory) (calls : CheckpointManifestDirectoryCalls)
    (state : ManifestState) (handle : ManifestHandle) (captured : state.1.directory = some handle) :
    sync directory.path calls.openRead calls.fsync directory.path state = withCache state.1 (calls.fsync handle state.2) := by
  rcases state with ⟨cache, image⟩
  change cache.directory = some handle at captured
  simp [sync, Cache.resolve, captured]

/-- Reach the final directory barrier through the returned rename. The
same retained directory description issues both directory syncs. A crash
after the final effect settles the exact new manifest and its synced runs.
Before the effect, the observed old or new bindings are admissible. -/
theorem CheckpointPowerCut.atManifestDirectory {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (calls : CheckpointManifestDirectoryCalls) (atRun : Nat → ManifestState) (runs : ManifestState → RunUnlinkImage)
    (runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs)
    (reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs)
    (completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged]) :
    let stagePath := directory.file .stagedManifest
    let cache := (atRun cut.checkpoint.table.runs.length).1.consume stagePath
    let atBarrier : ManifestState := (cache, reached.renamed)
    let interrupted : ManifestState := (cache, reached.interrupted)
    ((cut.completed.forM (calls.perform cut)) (atRun 0) = .ok () atBarrier) ∧
    reached.directoryHandle.2.reference ∈
      (reached.directoryHandle.1.afterDrops reached.drops).references reached.directoryHandle.2.description ∧
    reached.bindings reached.renamed directory.path = some (manifestInode reached.directoryHandle) ∧
    calls.perform cut cut.current atBarrier =
      SyncPathGroup.run (m := EStateM IO.Error ManifestState)
        (fun _ (files, image) => withCache files (calls.fsync reached.directoryHandle image)) #[directory.path] atBarrier ∧
    ∃ published, CheckpointManifestDirectoryCut cut published (runs interrupted)
      (reached.crashBindings.flatMap (manifestCrashBytes reached.interrupted)) := by
  intro stagePath cache atBarrier interrupted
  let count := cut.checkpoint.table.runs.length
  let perform := calls.perform cut
  let runEnd := atRun count
  let staged := (runEnd.1.remember stagePath reached.stageHandle, reached.written)
  let stageInode := manifestInode reached.stageHandle
  let synced := reached.written.completeFileSync stageInode
  let livePath := directory.file .manifest
  let old := reached.bindings synced livePath
  have current : cut.current = .manifest .syncDirectory := by
    have whole : steps count = cut.completed ++ [.manifest .syncDirectory] := by
      rw [completed]
      simp [steps, Publication.steps, count, List.append_assoc]
    exact (List.cons.inj (List.append_cancel_left (cut.schedule.symm.trans whole))).1
  have runDirectory : perform .syncRunsDirectory runEnd = .ok () (runEnd.1, reached.directorySettled) := by
    change SyncPathGroup.run (sync directory.path calls.openRead calls.fsync) #[directory.path] runEnd = _
    rw [SyncPathGroup.run_single, syncDirectorySelected _ _ _ _ reached.directoryCaptured, reached.runSynced]
    rfl
  have stageWritten : perform (.manifest .writeStaged) (runEnd.1, reached.directorySettled) = .ok () staged := by
    change stageFreshWithCache stagePath cut.checkpoint.manifest calls.stage (runEnd.1, reached.directorySettled) = _
    have wrote : calls.stage stagePath cut.checkpoint.manifest reached.directorySettled =
        .ok reached.stageHandle reached.written := reached.staged
    simp only [stageFreshWithCache, wrote, staged]
  have stageSynced : perform (.manifest .syncStaged) staged = .ok () (cache, synced) := by
    change SyncPathGroup.run (sync directory.path calls.openRead calls.fsync) #[stagePath] staged = _
    rw [SyncPathGroup.run_single, syncRemembered (cache := runEnd.1) (CheckpointPowerCut.stagedManifest_ne_directory directory),
      reached.synced]
  have stageRenamed : perform (.manifest .renameStaged) (cache, synced) = .ok () atBarrier := reached.renameReturned
  have prefixRan : (cut.completed.forM perform) (atRun 0) = .ok () atBarrier := by
    rw [completed, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    let suffix : List Step := [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged]
    change EStateM.bind ((runSteps count).forM perform) (fun _ => suffix.forM perform) (atRun 0) = _
    have finishedRuns : ((runSteps count).forM perform) (atRun 0) = .ok () runEnd := runPrefix.returned
    have finishedSuffix : suffix.forM perform = (perform .syncRunsDirectory >>= fun _ =>
        perform (.manifest .writeStaged) >>= fun _ => perform (.manifest .syncStaged) >>= fun _ =>
          perform (.manifest .renameStaged)) := by
      simp [suffix, List.forM_eq_forM, List.forM_cons, List.forM_nil]
    rw [finishedSuffix]
    simp only [Bind.bind, EStateM.bind, finishedRuns, runDirectory, stageWritten, stageSynced, stageRenamed]
  have finalRoute : perform cut.current atBarrier = SyncPathGroup.run (m := EStateM IO.Error ManifestState)
      (fun _ (files, image) => withCache files (calls.fsync reached.directoryHandle image)) #[directory.path] atBarrier := by
    rw [current]
    let cached (_ : FilePath) : EStateM IO.Error ManifestState Unit :=
      fun (files, image) => withCache files (calls.fsync reached.directoryHandle image)
    change SyncPathGroup.run (sync directory.path calls.openRead calls.fsync) #[directory.path] atBarrier =
      SyncPathGroup.run cached #[directory.path] atBarrier
    rw [SyncPathGroup.run_single (sync directory.path calls.openRead calls.fsync), SyncPathGroup.run_single cached]
    have capturedFinal : atBarrier.1.directory = some reached.directoryHandle := reached.directoryCaptured
    rw [syncDirectorySelected directory calls atBarrier reached.directoryHandle capturedFinal]
  obtain ⟨published, projected, visible, choices, freshBytes, older⟩ := cut.finalDirectoryPublication ready completed
  have settled : runs interrupted = (runs runEnd).syncDirectory := by
    rw [show runs interrupted = _ from reached.directoryRunNames,
      reached.renameRunNames, reached.syncRunNames, reached.stageRunNames, reached.runNames]
    cases cut.tookEffect <;> rfl
  have runChoices : (runs interrupted).crashImages = [(runs interrupted).visible] := by
    rw [settled]
    rfl
  have runPayloads : (runs interrupted).guaranteed = (runs runEnd).visible := by
    rw [settled]
    exact congrArg Image.durable (RunUnlinkImage.project_settled (runs runEnd).visible (.settled none))
  have newManifestBytes : manifestCrashBytes synced (some stageInode) = [some cut.checkpoint.manifest] := by
    simp [manifestCrashBytes, synced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, reached.stageBytes, stageInode]
  have oldManifestBytes : manifestCrashBytes synced old = [before.wal.directory.active.manifest] := by
    cases oldBinding : old with
    | none =>
      have absent : before.wal.directory.active.manifest = none := by
        simpa [oldBinding] using (show old.map reached.written.visible = _ from reached.oldVisible).symm
      simp [manifestCrashBytes, absent]
    | some inode =>
      have payload : some (reached.written.visible inode) = before.wal.directory.active.manifest := by
        simpa [oldBinding] using (show old.map reached.written.visible = _ from reached.oldVisible)
      have inodeBytes : synced.crashBytes inode = [reached.written.visible inode] := reached.oldStable inode oldBinding
      simp [manifestCrashBytes, inodeBytes, payload]
  have effective (took : cut.tookEffect = true) :
      reached.crashBindings.flatMap (manifestCrashBytes reached.interrupted) = [some cut.checkpoint.manifest] := by
    have newBinding : reached.crashBindings = [some stageInode] := by
      simp [reached.directoryEffect, took, reached.liveBinding, stageInode]
    have survived : some stageInode ∈ reached.crashBindings := by rw [newBinding]; exact List.mem_singleton_self _
    have payload := (reached.directoryBytes _ survived).trans (reached.renameBytes _ (.inl rfl))
    rw [newBinding, List.flatMap_singleton, payload, newManifestBytes]
  have physicalChoices : ∀ bytes ∈ reached.crashBindings.flatMap (manifestCrashBytes reached.interrupted),
      bytes ∈ published.manifest.crashImages := by
    intro bytes survives
    rw [choices]
    cases took : cut.tookEffect with
    | true =>
      rw [effective took] at survives
      exact survives
    | false =>
      obtain ⟨binding, survived, payload⟩ := List.mem_flatMap.mp survives
      have beforeEffect : binding ∈ reached.renameSurvivors := by simpa [reached.directoryEffect, took] using survived
      have stable := (reached.directoryBytes binding survived).trans (reached.renameBytes binding (.inr beforeEffect))
      rw [stable] at payload
      rcases reached.renameChoices binding beforeEffect with fresh | previous
      · rw [fresh, newManifestBytes] at payload
        exact List.mem_cons.mpr (.inl (List.mem_singleton.mp payload))
      · rw [previous, oldManifestBytes] at payload
        exact List.mem_cons_of_mem _ payload
  refine ⟨prefixRan, reached.directoryLive, reached.directoryBinding, finalRoute, published,
    ⟨current, projected, visible, choices, physicalChoices, effective, runChoices, ?_, ?_⟩⟩
  · intro index within
    rw [runPayloads, runPrefix.freshVisible index within, freshBytes index]
  · intro bytes metadata binding decoded index within
    rw [runPayloads, runPrefix.priorVisible bytes metadata binding decoded index within,
      older _ (cut.priorSelectedGeneration ready binding decoded).2 _]

end Alvoki.Storage.DiskSession
