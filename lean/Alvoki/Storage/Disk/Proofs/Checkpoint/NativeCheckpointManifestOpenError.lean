import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointManifestSyncError

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

namespace CheckpointPrimitiveCalls

variable {handle image : Type}

private def unlinkResult (result : Except IO.Error Unit) (after : image) : EStateM.Result IO.Error image Unit :=
  match RunCollection.ownedUnlinkResult result with
  | .ok () => .ok () after
  | .error cause => .error cause after

/-- The exact no-follow lookup and guarded unlink reached after an
exclusive-create conflict. ENOENT permits a retry and every other
lookup or unlink error follows the shared staging schedule. -/
inductive StaleStageCleanup (calls : CheckpointPrimitiveCalls handle image) (path : FilePath) (before : image) :
    EStateM.Result IO.Error image Unit → Prop where
  | missing (looked : calls.lookup path before = .ok (.error (.noFileOrDirectory name 2 message)) reached) :
      StaleStageCleanup calls path before (.ok () reached)
  | lookupError (looked : calls.lookup path before = .ok (.error cause) reached)
      (propagated : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
      StaleStageCleanup calls path before (.error cause reached)
  | nonregular (looked : calls.lookup path before = .ok (.ok metadata) reached)
      (other : (metadata.type == .file) = false) :
      StaleStageCleanup calls path before
        (.error (IO.userError s!"expected a regular database staging file: '{path}'") reached)
  | unlink (looked : calls.lookup path before = .ok (.ok metadata) checked)
      (regular : metadata.type = .file) (unlinked : calls.unlink path checked = .ok result reached) :
      StaleStageCleanup calls path before (unlinkResult result reached)

theorem StaleStageCleanup.returns {calls : CheckpointPrimitiveCalls handle image} {path : FilePath} {before : image}
    {result : EStateM.Result IO.Error image Unit} (cleanup : calls.StaleStageCleanup path before result) :
    removeStaleStagingWith calls.lookup calls.unlink path before = result := by
  cases cleanup with
  | missing looked =>
    simp [removeStaleStagingWith, looked, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  | @lookupError cause reached looked propagated =>
    simp only [removeStaleStagingWith, looked, Bind.bind, EStateM.bind]
    cases cause with
    | noFileOrDirectory name code message =>
      by_cases same : code = 2
      · subst code
        exact False.elim (propagated name message rfl)
      · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | _ => rfl
  | nonregular looked other =>
    simp [removeStaleStagingWith, looked, other, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | @unlink metadata checked result reached looked regular unlinked =>
    have kind : (metadata.type == .file) = true := by rw [regular]; rfl
    cases reduced : RunCollection.ownedUnlinkResult result with
    | ok returned =>
      cases returned
      simp [removeStaleStagingWith, looked, kind, unlinked, unlinkResult, reduced,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    | error cause =>
      simp [removeStaleStagingWith, looked, kind, unlinked, unlinkResult, reduced,
        Bind.bind, EStateM.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- A staged open can fail on the initial create, while checking and
detaching a stale name, or on the issued retry. The flag identifies
the branches in which an exclusive create itself reported the error. -/
inductive StageOpenError (calls : CheckpointPrimitiveCalls handle image) (path : FilePath) (before : image) :
    IO.Error → image → Bool → Prop where
  | direct (failed : calls.tryCreateStage path before = .ok (.error cause) reached)
      (nonConflict : ∀ name message, cause ≠ .alreadyExists name 17 message) :
      StageOpenError calls path before cause reached true
  | stale (conflict : calls.tryCreateStage path before = .ok (.error (.alreadyExists name 17 message)) collided)
      (failed : calls.StaleStageCleanup path collided (.error cause reached)) :
      StageOpenError calls path before cause reached false
  | retry (conflict : calls.tryCreateStage path before = .ok (.error (.alreadyExists name 17 message)) collided)
      (cleaned : calls.StaleStageCleanup path collided (.ok () ready))
      (failed : calls.createStage path ready = .error cause reached) :
      StageOpenError calls path before cause reached true

theorem StageOpenError.returns {calls : CheckpointPrimitiveCalls handle image} {path : FilePath} {before reached : image}
    {cause : IO.Error} {creating : Bool} (opening : calls.StageOpenError path before cause reached creating) (bytes : ByteArray) :
    calls.cached.writeStaged path bytes before = .error cause reached := by
  cases opening with
  | direct failed nonConflict =>
    simp only [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, failed]
    rfl
  | stale conflict failed =>
    simp [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, conflict, failed.returns]
  | retry conflict cleaned failed =>
    simp [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, conflict, cleaned.returns, failed]

end CheckpointPrimitiveCalls

/-- Either the returned failure added no reference or it came from an
observed live raw slot after successful exclusive creation and failed
wrapping. The stale guard or unlink route cannot allocate that slot. -/
inductive ManifestStageOpenCensus (before : DescriptorInventory) : DescriptorInventory → Bool → Option DescriptorSlot → Prop where
  | unchanged : ManifestStageOpenCensus before before creating none
  | unwrapped (slot : DescriptorSlot) (free : ∀ old ∈ before.slots, old.address ≠ slot.address)
      (fresh : before.references slot.description = []) (closeOnExec : slot.reference.closeOnExec = true) :
      ManifestStageOpenCensus before (before.insert slot free) true (some slot)

namespace ManifestStageOpenCensus

theorem keepsSlots {before after : DescriptorInventory} {creating : Bool} {raw : Option DescriptorSlot}
    (effect : ManifestStageOpenCensus before after creating raw) {slot : DescriptorSlot} (live : slot ∈ before.slots) :
    slot ∈ after.slots := by
  cases effect with
  | unchanged => exact live
  | unwrapped slot _ _ _ => exact List.mem_cons_of_mem slot live

theorem slot {before after : DescriptorInventory} {creating : Bool} {raw : Option DescriptorSlot}
    (effect : ManifestStageOpenCensus before after creating raw) :
    (raw = none → after = before) ∧
    ∀ descriptor, raw = some descriptor → creating = true ∧ before.references descriptor.description = [] ∧
      after.references descriptor.description = [descriptor.reference] ∧ descriptor.reference.closeOnExec = true := by
  cases effect with
  | unchanged => simp
  | unwrapped slot free fresh closed =>
    refine ⟨by simp, ?_⟩
    intro descriptor equality
    cases Option.some.inj equality
    exact ⟨rfl, fresh, by simp [DescriptorInventory.references_insert, fresh], closed⟩

end ManifestStageOpenCensus

/-- Opening the stage fails after the complete run-directory prefix.
The raw namespace and inode observations frame the protected names,
whether stale cleanup was skipped, failed or reached the next create. -/
structure NativeCheckpointManifestOpenError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  settled : NativeCheckpointRunsSynced (image := image) state cut
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++ [.syncRunsDirectory]
  cause : IO.Error
  after : image
  creating : Bool
  opening : settled.runs.primitives.StageOpenError (state.session.directory.file .stagedManifest)
    settled.after cause after creating
  raw : Option DescriptorSlot
  slots : ManifestStageOpenCensus (settled.runs.descriptors settled.after) (settled.runs.descriptors after) creating raw
  view : RunDirectoryInodeView state.session.directory (settled.runs.inodes after) (settled.runs.runs after)
  protectedPaths : ∀ path, path ≠ state.session.directory.file .stagedManifest →
    view.visible path = settled.view.visible path
  protectedSurvivors : ∀ binding ∈ view.crashBindings, ∃ earlier ∈ settled.view.crashBindings, ∀ path,
    path ≠ state.session.directory.file .stagedManifest → binding path = earlier path
  protectedBytes : ∀ path inode, path ≠ state.session.directory.file .stagedManifest →
    settled.view.visible path = some inode →
    (settled.runs.inodes after).visible inode = (settled.runs.inodes settled.after).visible inode ∧
    (settled.runs.inodes after).crashBytes inode = (settled.runs.inodes settled.after).crashBytes inode
  emptyScratch : ∀ slot, raw = some slot →
    let inode := (settled.runs.descriptors after).inode slot.description
    view.visible (state.session.directory.file .stagedManifest) = some inode ∧
    (settled.runs.inodes after).visible inode = ByteArray.empty ∧
    (settled.runs.files after).directory.staged .manifest = some (ByteArray.empty, false)
  pair : (settled.runs.files after).directory.active = (settled.runs.files settled.after).directory.active
  crashPair : (settled.runs.files after).directory.crashImages = (settled.runs.files settled.after).directory.crashImages
  wal : CheckpointWalView.ofFiles (settled.runs.files after) = CheckpointWalView.ofFiles (settled.runs.files settled.after)

namespace NativeCheckpointManifestOpenError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

def atIssue (report : NativeCheckpointManifestOpenError (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache, report.settled.after)

theorem current (report : NativeCheckpointManifestOpenError (image := image) state cut) :
    cut.current = .manifest .writeStaged := by
  have ordered := cut.schedule
  rw [report.completed] at ordered
  simp only [CheckpointPublication.steps, Publication.steps, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append] at ordered
  exact (List.cons.inj (List.cons.inj (List.append_cancel_left ordered)).2).1.symm

theorem issues (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.settled.runs.perform state.session.phase report.settled.runs.entry cut.checkpoint.prepared
      cut.checkpoint.manifest cut.completed (.manifest .writeStaged) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  have completed := report.settled.runPrefix
  rw [← report.completed] at completed
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.settled.runs.perform report.settled.runs.entry scheduled completed

theorem callbackFails (report : NativeCheckpointManifestOpenError (image := image) state cut) :
    report.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .writeStaged) report.atIssue =
      .error report.cause (state.cache, report.after) :=
  stageFreshWithCache_error _ _ _ _ (report.opening.returns cut.checkpoint.manifest)

theorem returns (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.settled.runs.perform (state.session.phase, report.settled.runs.entry) =
      .error report.cause (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

/-- The failure leaves the original census or exactly one unwrapped
raw reference. Only the branch that issued create can retain that
reference and its exact empty scratch inode. -/
theorem reachedSlot (report : NativeCheckpointManifestOpenError (image := image) state cut) :
    (report.raw = none → report.settled.runs.descriptors report.after = state.census) ∧
    ∀ descriptor, report.raw = some descriptor → report.creating = true ∧
      state.census.references descriptor.description = [] ∧
      (report.settled.runs.descriptors report.after).references descriptor.description = [descriptor.reference] ∧
      descriptor.reference.closeOnExec = true ∧
      report.view.visible (state.session.directory.file .stagedManifest) =
        some ((report.settled.runs.descriptors report.after).inode descriptor.description) ∧
      (report.settled.runs.inodes report.after).visible
        ((report.settled.runs.descriptors report.after).inode descriptor.description) = ByteArray.empty ∧
      (report.settled.runs.files report.after).directory.staged .manifest = some (ByteArray.empty, false) := by
  obtain ⟨without, withSlot⟩ := report.slots.slot
  refine ⟨fun missing => (without missing).trans report.settled.keepsCensus, ?_⟩
  intro descriptor present
  obtain ⟨created, fresh, slot, closes⟩ := withSlot descriptor present
  rw [report.settled.keepsCensus] at fresh
  obtain ⟨named, bytes, staged⟩ := report.emptyScratch descriptor present
  exact ⟨created, fresh, slot, closes, named, bytes, staged⟩

private theorem fixedNameNeStage (directory : DiskDirectory) {file : DiskFile}
    (fixed : file = .lock ∨ file = .manifest) : directory.file file ≠ directory.file .stagedManifest := by
  intro equal
  rcases fixed with rfl | rfl <;>
    have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
    <;> contradiction

theorem custody (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    state.directorySlot ∈ (report.settled.runs.descriptors report.after).slots ∧
    state.owner ∈ (report.settled.runs.descriptors report.after).slots ∧
    report.view.visible state.session.directory.path = some (report.settled.runs.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  refine ⟨report.slots.keepsSlots (report.settled.keepsCensus.symm ▸ valid.directoryLive),
    report.slots.keepsSlots (report.settled.keepsCensus.symm ▸ valid.ownerLive), ?_, ?_⟩
  · rw [report.protectedPaths _ (file_ne_directory _ .stagedManifest).symm, report.settled.sameDirectory]
    exact (report.settled.directoryCustody valid).2.2.1
  · rw [report.protectedPaths _ (fixedNameNeStage _ (.inl rfl)), report.settled.sameNames .lock]
    exact report.settled.lockAtIssue

theorem keepsOther (report : NativeCheckpointManifestOpenError (image := image) state cut)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (different : path ≠ state.session.directory.file .stagedManifest)
    (stable : report.settled.view.Stable path inode bytes) : report.view.Stable path inode bytes := by
  obtain ⟨visible, durable⟩ := report.protectedBytes path inode different stable.visibleBinding
  refine ⟨(report.protectedPaths path different).trans stable.visibleBinding, ?_,
    visible.trans stable.visibleBytes, durable.trans stable.crashBytes⟩
  intro survivor member
  obtain ⟨earlier, observed, names⟩ := report.protectedSurvivors survivor member
  exact (names path different).trans (stable.crashBinding earlier observed)

theorem selectedPair (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    (report.settled.runs.files report.after).directory.active = state.writer.target.pair ∧
    (report.settled.runs.files report.after).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (report.settled.runs.files report.after) = CheckpointWalView.ofFiles state.files.image := by
  obtain ⟨pair, survives, wal⟩ := report.settled.selectedPair valid
  exact ⟨report.pair.trans pair, report.crashPair.trans survives, report.wal.trans wal⟩

theorem manifestAtReturn (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    match (report.settled.runs.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  have before : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  rw [(report.selectedPair valid).1, ← before]
  have manifest := report.settled.runs.manifestAtEnd
  cases known : state.files.image.directory.active.manifest with
  | none =>
    rw [known] at manifest
    rw [report.protectedPaths _ (fixedNameNeStage _ (.inr rfl)), report.settled.sameNames .manifest]
    exact manifest
  | some payload =>
    rw [known] at manifest
    obtain ⟨inode, initial, stable⟩ := manifest
    exact ⟨inode, initial, report.keepsOther (fixedNameNeStage _ (.inr rfl))
      (report.settled.stableAfter stable.visibleBinding stable.visibleBytes stable.crashBytes)⟩

theorem freshRunBytes (report : NativeCheckpointManifestOpenError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    ∃ run inode, cut.checkpoint.table.runs.toArray[index]? = some run ∧
      report.view.Stable (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) inode run.run.bytes := by
  obtain ⟨run, inode, selected, binding, visible, durable⟩ := report.settled.runs.freshRunAtEnd within
  exact ⟨run, inode, selected, report.keepsOther (runFile_ne_stagedManifest _ _ _) (report.settled.stableAfter binding visible durable)⟩

theorem priorRunBytes (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, initial, stable⟩ := report.settled.runs.priorRunAtEnd valid binding decoded within stored
  exact ⟨inode, initial, report.keepsOther (runFile_ne_stagedManifest _ _ _)
    (report.settled.stableAfter stable.visibleBinding stable.visibleBytes stable.crashBytes)⟩

theorem selectedCheckpoint (report : NativeCheckpointManifestOpenError (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.settled.runs.runs report.after).guaranteed
      (report.settled.runs.files report.after).directory.active.manifest state.writer.checkpoint := by
  let ready := valid.retained
  have agrees : SelectedRunsAgree state.writer.wal.directory.active.manifest
      (report.settled.runs.runs report.after).guaranteed state.writer.published.durable := by
    intro bytes metadata binding decoded index within
    have selected := ready.resumed.selected
    rw [← ready.walPair] at selected
    obtain ⟨payload, stored⟩ := selected.runExists binding decoded within
    obtain ⟨_, _, exactRun⟩ := report.priorRunBytes valid binding decoded within stored
    exact exactRun.guaranteed.trans stored.symm
  rw [(report.selectedPair valid).1, ← ready.walPair]
  exact SelectedIntegrityCheckpoint.withRunMap (ready.walPair.symm ▸ ready.resumed.selected) agrees.symm

end NativeCheckpointManifestOpenError

structure NativeReturnedCheckpointManifestOpenError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestOpenError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.settled.runs.perform current.state.session.phase report.settled.runs.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .writeStaged) report.atIssue
  returned : runCheckpointWithEffects report.settled.runs.perform (current.state.session.phase, report.settled.runs.entry) =
    .error report.cause (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  directoryLive : current.state.directorySlot ∈ (report.settled.runs.descriptors report.after).slots
  lockLive : current.state.owner ∈ (report.settled.runs.descriptors report.after).slots
  directoryObject : report.view.visible current.state.session.directory.path =
    some (report.settled.runs.captured.inode current.state.directorySlot.description)
  lockObject : report.view.visible (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  pair : (report.settled.runs.files report.after).directory.active = current.state.writer.target.pair
  survives : (report.settled.runs.files report.after).directory.crashImages = [current.state.writer.target.pair]
  wal : CheckpointWalView.ofFiles (report.settled.runs.files report.after) = CheckpointWalView.ofFiles current.state.files.image
  checkpoint : SelectedIntegrityCheckpoint (report.settled.runs.runs report.after).guaranteed
    (report.settled.runs.files report.after).directory.active.manifest current.state.writer.checkpoint
  replay : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.checkpointManifestOpenError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestOpenError (image := image) current.state cut) :
    NativeReturnedCheckpointManifestOpenError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨directoryLive, lockLive, directory, lock⟩ := report.custody valid
  obtain ⟨pair, survives, wal⟩ := report.selectedPair valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, directoryLive, lockLive,
    directory, lock, pair, survives, wal, report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
