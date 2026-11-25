import Alvoki.Storage.Disk.Checkpoint.Manifest.RenamePrefix

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The reached manifest bytes are the encoding of this exact run plan. -/
theorem CheckpointPowerCut.plannedManifestBytes {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) : cut.checkpoint.plan.manifest.encode = cut.checkpoint.manifest := by
  let generation := SegmentedCheckpointReport.generation before
  have encoded := cut.encoded
  by_cases fits : (cut.checkpoint.table.runs.map (·.run.bytes)).all (fun bytes => decide (bytes.size < UInt64.size)) = true
  · exact Except.ok.inj ((encodeCheckpointIntegrityManifest_exact generation
      (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))).symm.trans encoded)
  · simp [encodeCheckpointIntegrityManifest, fits, Bind.bind, Except.bind] at encoded

private theorem CheckpointPowerCut.newManifestHeader {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    {metadata : Manifest.IntegrityCheckpoint}
    (decoded : Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata) :
    metadata.header = checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation before) := by
  obtain ⟨_, refinement, _⟩ := ready.resumed.canonical
  let generation := SegmentedCheckpointReport.generation before
  let files := cut.checkpoint.table.runs.map (·.run.bytes)
  let exactManifest := Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader cut.checkpoint.table generation) files
  have encoded := cut.encoded
  have exactBytes : cut.checkpoint.manifest = exactManifest.encode := by
    by_cases fits : files.all (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact Except.ok.inj (encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation
        (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))))
    · simp [encodeCheckpointIntegrityManifest, files, fits, Bind.bind, Except.bind] at encoded
  have written := (WrittenCheckpoint.of_flushForCheckpoint cut.flushed refinement cut.runCountFits
    ready.resumed.bounds.runs ready.resumed.bounds.memory generation).1
  have roundTrip := Manifest.IntegrityCheckpoint.decode_encode exactManifest written.validFloor
    (by simpa [exactManifest, files, Manifest.IntegrityCheckpoint.fromRuns] using written.count)
  rw [exactBytes] at decoded
  exact congrArg Manifest.IntegrityCheckpoint.header (Except.ok.inj (decoded.symm.trans roundTrip))

/-- Any prior manifest describes a different generation from the new one. -/
theorem CheckpointPowerCut.manifestChanges {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer) :
    before.wal.directory.active.manifest ≠ some cut.checkpoint.manifest := by
  intro same
  have prior := CheckpointPowerCut.selectedGeneration ready.resumed.selected
  rw [← ready.resumed.generation, ← ready.walPair, same] at prior
  cases decoded : Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest with
  | error cause => simp [Option.mapM, Functor.map, Except.map, decoded] at prior
  | ok metadata =>
    apply (cut.priorSelectedGeneration ready same decoded).2
    rw [cut.newManifestHeader ready decoded]
    rfl

/-- A physical run map can be reindexed using the exact manifest that
selected it. The published new header fixes its generation and run count. -/
theorem CheckpointPowerCut.selectedRunAgreement {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat}
    (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (published : Image) (binding : Option ByteArray)
    (origin : binding = before.wal.directory.active.manifest ∨ binding = some cut.checkpoint.manifest)
    (runs : RunFiles)
    (newRuns : ∀ index < cut.checkpoint.table.runs.length, runs (SegmentedCheckpointReport.generation before) index =
      published.durable (SegmentedCheckpointReport.generation before) index)
    (oldRuns : SelectedRunsAgree before.wal.directory.active.manifest runs published.durable) :
    SelectedRunsAgree binding runs published.durable := by
  rcases origin with old | new
  · exact old.symm ▸ oldRuns
  · intro bytes metadata present decoded index inside
    have sameBytes : bytes = cut.checkpoint.manifest := Option.some.inj (present.symm.trans new)
    subst bytes
    rw [cut.newManifestHeader ready decoded] at inside ⊢
    have count : (checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation before)).runCount.toNat =
        cut.checkpoint.table.runs.length := UInt64.toNat_ofNat_of_lt' cut.runCountFits
    exact newRuns index (count ▸ inside)

/-- At the manifest rename, the issued source is the staged description's
synced inode. The effect-time report selects the prior target alone or
also the replacement, without a callback return. The already settled
run names remain available for either selected manifest. -/
theorem CheckpointPowerCut.atManifestRename {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (writeRun : FilePath → ByteArray →
      EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage) Unit)
    (stage : FilePath → ByteArray → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot))
    (openRead : FilePath → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot))
    (fsync : (DescriptorInventory × DescriptorSlot) → EStateM IO.Error WalInodeImage Unit)
    (rename : FilePath → FilePath →
      EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage) Unit)
    (atRun : Nat → Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage)
    (directoryCache : Cache (DescriptorInventory × DescriptorSlot))
    (directorySettled written interrupted : WalInodeImage)
    (inventory : DescriptorInventory) (slot : DescriptorSlot)
    (runs : WalInodeImage → RunUnlinkImage) (bindings : WalInodeImage → FilePath → Option Nat)
    (crashBindings : List (Option Nat)) :
    let count := cut.checkpoint.table.runs.length
    let generation := SegmentedCheckpointReport.generation before
    let stagePath := directory.file .stagedManifest
    let livePath := directory.file .manifest
    let captured := (inventory, slot)
    let inode := inventory.inode slot.description
    let synced := written.completeFileSync inode
    let oldBinding := bindings synced livePath
    let stageSync := SyncPathGroup.run (sync directory.path openRead fsync)
    let perform := performCheckpointFileStep directory generation cut.checkpoint.table.runs.toArray
      stagePath cut.checkpoint.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun (fun path bytes => stageFreshWithCache path bytes stage) stageSync rename
    cut.completed = runSteps count ++ [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged] →
    (∀ index < count, (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
      .ok () (atRun (index + 1))) →
    (∀ index < count, (runs (atRun count).2).visible generation index = cut.checkpoint.plan.files[index]?) →
    (∀ bytes metadata, before.wal.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat,
        (runs (atRun count).2).visible metadata.header.generation index =
          before.published.durable metadata.header.generation index) →
    perform .syncRunsDirectory (atRun count) = .ok () (directoryCache, directorySettled) →
    runs directorySettled = (runs (atRun count).2).syncDirectory →
    stage stagePath cut.checkpoint.manifest directorySettled = .ok captured written →
    fsync captured written = .ok () synced →
    written.visible inode = cut.checkpoint.manifest →
    bindings synced stagePath = some inode →
    oldBinding.map synced.visible = before.wal.directory.active.manifest →
    (∀ old, oldBinding = some old → synced.crashBytes old = [synced.visible old]) →
    runs written = runs directorySettled →
    runs synced = runs written →
    runs interrupted = runs synced →
    (∀ chosen ∈ crashBindings,
      chosen ∈ (if cut.tookEffect then [bindings synced stagePath, oldBinding] else [oldBinding])) →
    (∀ chosen ∈ crashBindings, manifestCrashBytes interrupted chosen = manifestCrashBytes synced chosen) →
    cut.current = .manifest .renameStaged ∧
    (cut.completed.forM perform) (atRun 0) = .ok () (directoryCache.consume stagePath, synced) ∧
    perform cut.current (directoryCache.consume stagePath, synced) =
      rename stagePath livePath (directoryCache.consume stagePath, synced) ∧
    ∃ published, before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published ∧
      (∀ bytes ∈ crashBindings.flatMap (manifestCrashBytes interrupted), bytes ∈ published.manifest.crashImages) ∧
      (∀ index < count, (runs interrupted).guaranteed generation index = published.durable generation index) ∧
      (∀ bytes metadata, before.wal.directory.active.manifest = some bytes →
        Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat,
          (runs interrupted).guaranteed metadata.header.generation index =
            published.durable metadata.header.generation index) ∧
      ∀ older, older ≠ generation → ∀ index,
        published.durable older index = before.published.durable older index := by
  intro count generation stagePath livePath captured inode synced oldBinding stageSync perform
    completed pairs syncedRuns oldRuns directoryReturned directoryNames stageReturned
    fsyncReturned writtenBytes sourceBinding oldVisible oldSynced stageRuns syncRuns renameRuns choices inodeContent
  have current : cut.current = .manifest .renameStaged := by
    have schedule := cut.schedule
    rw [completed] at schedule
    change runSteps count ++ [.syncRunsDirectory] ++ Publication.steps.map Step.manifest =
      (runSteps count ++ [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]) ++
        cut.current :: cut.remaining at schedule
    simp only [Publication.steps, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append] at schedule
    have suffix := List.append_cancel_left schedule
    have remaining := congrArg (·[3]?) suffix
    simpa using remaining.symm
  have prefixRan := runSteps_returned perform count atRun pairs
  have stagePair : ((perform (.manifest .writeStaged) >>= fun _ => perform (.manifest .syncStaged))
      (directoryCache, directorySettled)) = .ok () (directoryCache.consume stagePath, synced) := by
    change ((stageFreshWithCache stagePath cut.checkpoint.manifest stage >>= fun _ =>
      SyncPathGroup.run (sync directory.path openRead fsync) #[stagePath]) (directoryCache, directorySettled)) = _
    have wrote : stageFreshWithCache stagePath cut.checkpoint.manifest stage (directoryCache, directorySettled) =
        .ok () (directoryCache.remember stagePath captured, written) := by
      simp only [stageFreshWithCache, stageReturned]
    have route := syncRemembered (dir := directory.path) (path := stagePath) (cache := directoryCache)
      (CheckpointPowerCut.stagedManifest_ne_directory directory) captured openRead fsync written
    simp only [Bind.bind, EStateM.bind, wrote, SyncPathGroup.run_single, route, fsyncReturned]
  have completedRan : (cut.completed.forM perform) (atRun 0) =
      .ok () (directoryCache.consume stagePath, synced) := by
    rw [completed, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    change EStateM.bind ((runSteps count).forM perform)
      (fun _ => [Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged].forM perform) (atRun 0) = _
    have suffix : [Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged].forM perform =
        (perform .syncRunsDirectory >>= fun _ =>
          perform (.manifest .writeStaged) >>= fun _ => perform (.manifest .syncStaged)) := by
      simp [List.forM_eq_forM, List.forM_cons, List.forM_nil]
    rw [suffix]
    simp only [EStateM.bind, prefixRan, Bind.bind, directoryReturned]
    exact stagePair
  have settledContents : (runs interrupted).guaranteed = (runs (atRun count).2).visible := by
    rw [renameRuns, syncRuns, stageRuns, directoryNames]
    exact congrArg Image.durable
      (RunUnlinkImage.project_settled (runs (atRun count).2).visible (.settled none))
  have planCount : cut.checkpoint.plan.files.length = count := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  have stableOld : before.published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [ready.manifestFiles, ready.directoryFiles]
    have settled := ready.walDirectorySettled
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, settled]
  obtain ⟨writtenRuns, runModel, sameManifest, durable, older⟩ :=
    checkpoint_runs_complete before.published cut.checkpoint.plan.runSet
  have renamedPrefix : cut.checkpoint.cut = (runSteps count).length + 1 + (2 + (if cut.tookEffect then 1 else 0)) := by
    rw [cut.reachedCount.1, completed, List.length_append]
    simp
    omega
  have oldProjection : manifestCrashBytes synced oldBinding = [before.wal.directory.active.manifest] := by
    cases old : oldBinding with
    | none =>
      have absent : before.wal.directory.active.manifest = none := by simpa [old] using oldVisible.symm
      simp [manifestCrashBytes, absent]
    | some prior =>
      have payload : some (synced.visible prior) = before.wal.directory.active.manifest := by
        simpa [old] using oldVisible
      simp [manifestCrashBytes, oldSynced prior old, payload]
  have newProjection : manifestCrashBytes synced (some inode) = [some cut.checkpoint.manifest] := by
    simp [manifestCrashBytes, synced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, writtenBytes]
  have result (took : Bool) :
      before.published.executeVersioned cut.checkpoint.plan
          ((runSteps count).length + 1 + (2 + (if took then 1 else 0))) =
        some { writtenRuns with manifest := if took then
          ⟨some cut.checkpoint.manifest, some cut.checkpoint.manifest :: before.published.manifest.crashImages, none⟩
          else { before.published.manifest with staged := some (cut.checkpoint.manifest, true) } } := by
    exact before.published.executeVersioned_atManifestRename cut.checkpoint.plan writtenRuns runModel
      sameManifest planCount cut.plannedManifestBytes took
  have crashContents : ∀ bytes ∈ crashBindings.flatMap (manifestCrashBytes interrupted),
      bytes ∈ (if cut.tookEffect then some cut.checkpoint.manifest :: before.published.manifest.crashImages
        else before.published.manifest.crashImages) := by
    intro bytes survives
    obtain ⟨chosen, member, payload⟩ := List.mem_flatMap.mp survives
    rw [inodeContent chosen member] at payload
    have possible := choices chosen member
    rw [sourceBinding] at possible
    cases effective : cut.tookEffect
    · have same : chosen = oldBinding := by simpa [effective] using possible
      simpa [effective, same, oldProjection, stableOld] using payload
    · have candidates : chosen = some inode ∨ chosen = oldBinding := by simpa [effective] using possible
      rcases candidates with rfl | rfl
      · simp only [newProjection, List.mem_singleton] at payload
        simp [payload]
      · rw [oldProjection, ← stableOld] at payload
        exact List.mem_cons_of_mem _ payload
  rw [renamedPrefix]
  refine ⟨current, completedRan, ?_, _, result cut.tookEffect, ?_, ?_, ?_, older⟩
  · rw [current]
    rfl
  · intro bytes survives
    have admitted := crashContents bytes survives
    cases effective : cut.tookEffect <;> simpa [effective] using admitted
  · intro index within
    rw [settledContents]
    exact (syncedRuns index within).trans (durable index).symm
  · intro bytes metadata bound decoded index within
    have oldChoice : some bytes ∈ before.published.manifest.crashImages := by
      rw [stableOld, bound]
      exact List.mem_singleton_self _
    have disjoint : metadata.header.generation ≠ generation :=
      freshGeneration ready cut.generationFits bytes (.inr oldChoice) (.integrity metadata)
        (Manifest.VersionedCheckpoint.decode_integrity decoded)
    rw [settledContents]
    exact (oldRuns bytes metadata bound decoded index within).trans (older _ disjoint index).symm

end Alvoki.Storage.DiskSession
