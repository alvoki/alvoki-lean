import Alvoki.Storage.Disk.Proofs.Rotation.RotationSuccessorFsyncStop

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation SyncHandleRouting

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
  {parent : RotationCreateParent directory before lookup inventory}
  {created : RotationRawSuccessor parent}

private abbrev successorName (before : SegmentedWriterState) :=
  renderWalSegmentName (before.installed.walBytes / WAL.frameSize)

private abbrev keeperName (before : SegmentedWriterState) := renderWalSegmentName before.installed.activeFirst

private def rotationFailure (path : FilePath) (returned : Option IO.Error) (after : σ) :
    EStateM.Result FilePath σ (Except IO.Error Unit) :=
  match returned with
  | none => .error path after
  | some cause => .ok (.error cause) after

/-- The newly created file has been synced on its returned descriptor.
The final barrier uses the cached directory. The last callback can stop
or return a diagnostic, with the same physical effect choices. -/
structure RotationDirectoryFsyncFailure (created : RotationRawSuccessor parent) (diagnostic : Option IO.Error)
    extends RotationSuccessorFileIssue created where
  directoryHandle : RotationSuccessorHandle
  captured : cache.directory = some directoryHandle
  captureObject : parent.files.view.modelObject parent.root = directoryHandle.1.inode directoryHandle.2.1.description
  effectObject : parent.files.view.modelObject parent.root = inventory.inode directoryHandle.2.1.description
  pathObject : FilePath → Option DeviceInode
  bound : pathObject directory.path = some parent.root
  beforeDirectory : List LockReferenceDrop
  directoryLive : directoryHandle.2.1 ∈ ((created.handle.1.afterDrops drops).afterDrops beforeDirectory).slots
  ownerStillLive : parent.owner ∈ ((created.handle.1.afterDrops drops).afterDrops beforeDirectory).slots
  fsync : RotationSuccessorHandle → EStateM FilePath RotationCreateFiles (Except IO.Error Unit)
  fileReturned : fsync created.handle created.files = .ok (.ok ()) (created.afterSync true).files
  effective : Bool
  after : RotationCreateFiles
  failed : fsync directoryHandle (created.afterSync true).files = rotationFailure directory.path diagnostic after
  view : after.view = created.files.view
  bytes : after.inodes = (created.afterSync true).files.inodes
  successorSurvives : after.crashNames (successorName before) = if effective then
    [some created.child.child] else created.files.crashNames (successorName before)
  keeperSurvives : after.crashNames (keeperName before) = created.files.crashNames (keeperName before)
  markerSurvives : after.crashNames "WAL.commit" = created.files.crashNames "WAL.commit"

abbrev RotationDirectoryFsyncStop (created : RotationRawSuccessor parent) := RotationDirectoryFsyncFailure created none

namespace RotationDirectoryFsyncFailure

variable {returned : Option IO.Error}


def effectInventory (report : RotationDirectoryFsyncFailure created returned) : DescriptorInventory :=
  (created.handle.1.afterDrops report.drops).afterDrops report.beforeDirectory

def cut (report : RotationDirectoryFsyncFailure created returned) : RotationInFlightCut directory before :=
  parent.cutAtBarrier true report.effective

private def syncPath (report : RotationDirectoryFsyncFailure created returned) (path : FilePath) :
    ExceptT IO.Error (EStateM FilePath (Cache RotationSuccessorHandle × State)) Unit :=
  fun (cache, files) =>
    match cache.resolve directory.path path report.openRead files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, reached) =>
      let atDirectory := reached.successor = .fileSynced
      let image := if atDirectory then (created.afterSync true).files else created.files
      let after := if atDirectory then report.cut.image else ⟨before.wal.directory, .fileSynced⟩
      match report.fsync handle image with
      | .ok value _ => .ok value (cache, after)
      | .error stop _ => .error stop (cache, after)

def run (report : RotationDirectoryFsyncFailure created returned) :=
  let issue := report.toRotationSuccessorFileIssue
  runRotationWithInterruption directory before lookup issue.openNew issue.cache
    (fun path => SyncPathGroup.run report.syncPath #[path])

/-- The file barrier consumes the pending entries for the successor. The final
sync uses the original cached directory slot, which still names its inode
at the effect point. The owner remains live through this same census. -/
theorem custody (report : RotationDirectoryFsyncFailure created returned) :
    report.pathObject directory.path = some parent.root ∧
    report.directoryHandle.1.inode report.directoryHandle.2.1.description =
      report.effectInventory.inode report.directoryHandle.2.1.description ∧
    report.directoryHandle.2.1 ∈ report.effectInventory.slots ∧
    parent.owner ∈ report.effectInventory.slots ∧
    report.toRotationSuccessorFileIssue.atIssue.directory = some report.directoryHandle :=
  ⟨report.bound, report.captureObject.symm.trans report.effectObject, report.directoryLive,
    report.ownerStillLive, report.captured⟩

theorem resolves (report : RotationDirectoryFsyncFailure created returned) :
    let cache := report.toRotationSuccessorFileIssue.atIssue
    cache.resolve directory.path directory.path report.openRead ⟨before.wal.directory, .fileSynced⟩ =
      .ok report.directoryHandle (cache, ⟨before.wal.directory, .fileSynced⟩) := by
  simp [Cache.resolve, report.custody.2.2.2.2]

theorem fileGroupReturns (report : RotationDirectoryFsyncFailure created returned) :
    let issue := report.toRotationSuccessorFileIssue
    let path := rotationSuccessorPath directory before
    (SyncPathGroup.run report.syncPath #[path]).run
      (report.cache.remember path created.handle, ⟨before.wal.directory, .created⟩) =
    .ok (.ok ()) (issue.atIssue, ⟨before.wal.directory, .fileSynced⟩) := by
  intro issue path
  have selected : (report.cache.remember path created.handle).resolve directory.path path report.openRead
      ⟨before.wal.directory, .created⟩ = .ok created.handle (issue.atIssue, ⟨before.wal.directory, .created⟩) :=
    issue.resolves
  have synced : report.syncPath path (report.cache.remember path created.handle, ⟨before.wal.directory, .created⟩) =
      .ok (.ok ()) (issue.atIssue, ⟨before.wal.directory, .fileSynced⟩) := by
    simp [syncPath, selected, report.fileReturned]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
    tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
    StateT.pure, Pure.pure, ExceptT.pure, EStateM.pure, synced]

/-- A grouped directory sync forwards a stop without a diagnostic.
An ordinary error is returned with the issued pathname added. -/
theorem directoryGroupFails (report : RotationDirectoryFsyncFailure created returned) :
    let cache := report.toRotationSuccessorFileIssue.atIssue
    (SyncPathGroup.run report.syncPath #[directory.path]).run (cache, ⟨before.wal.directory, .fileSynced⟩) =
      rotationFailure directory.path (returned.map (fun cause => IO.userError s!"sync failed for '{directory.path}': {cause}"))
        (cache, report.cut.image) := by
  intro cache
  have failed : report.syncPath directory.path (cache, ⟨before.wal.directory, .fileSynced⟩) =
      rotationFailure directory.path returned (cache, report.cut.image) := by
    cases returned <;> simp [syncPath, cache, report.resolves, report.failed, rotationFailure]
  cases returned <;> simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw, rotationFailure] at failed ⊢
  all_goals rw [failed] <;> rfl

theorem directoryGroupStops (report : RotationDirectoryFsyncStop created) :
    let cache := report.toRotationSuccessorFileIssue.atIssue
    (SyncPathGroup.run report.syncPath #[directory.path]).run (cache, ⟨before.wal.directory, .fileSynced⟩) =
      .error directory.path (cache, report.cut.image) :=
  report.directoryGroupFails

/-- Both earlier callbacks return before the final directory failure.
Either channel leaves the old writer poisoned, with the consumed cache
and original held owner. -/
theorem failsSchedule (report : RotationDirectoryFsyncFailure created returned) :
    report.run = rotationFailure directory.path (returned.map
      (fun cause => IO.userError s!"sync failed for '{directory.path}': {cause}"))
      (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) := by
  let issue := report.toRotationSuccessorFileIssue
  obtain ⟨_, _, absent⟩ := parent.absent
  have opened := issue.opens
  have fileReturned : (SyncPathGroup.run report.syncPath #[rotationSuccessorPath directory before])
      (report.cache.remember (rotationSuccessorPath directory before) created.handle, ⟨before.wal.directory, .created⟩) =
      .ok (.ok ()) (issue.atIssue, ⟨before.wal.directory, .fileSynced⟩) := report.fileGroupReturns
  have failed : (SyncPathGroup.run report.syncPath #[directory.path]) (issue.atIssue, ⟨before.wal.directory, .fileSynced⟩) =
      rotationFailure directory.path (returned.map (fun cause => IO.userError s!"sync failed for '{directory.path}': {cause}"))
        (issue.atIssue, report.cut.image) := report.directoryGroupFails
  cases returned <;>
    simp [run, issue, runRotationWithInterruption, rotateWalSchedule, Phase.installed, parent.nonempty, report.checked,
      publishPrepared, rotateFileCall, WalSegmentRotation.runAt_fileEffects, observeSuccessorWith, readEmptyWith,
      optionalMetadataWith, absent, opened, fileReturned, failed, rotationFailure, Bind.bind, ExceptT.bind, ExceptT.bindCont,
      ExceptT.mk, ExceptT.run, ExceptT.lift, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, Functor.map, EStateM.map, Pure.pure, ExceptT.pure, EStateM.pure, Except.pure]

theorem stopsSchedule (report : RotationDirectoryFsyncStop created) :
    report.run = .error directory.path
      (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) :=
  report.failsSchedule

theorem returnsError (report : RotationDirectoryFsyncFailure created (some cause)) :
    report.run = .ok (.error (IO.userError s!"sync failed for '{directory.path}': {cause}"))
      (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) :=
  report.failsSchedule

/-- An effective directory barrier settles the canonical successor. A
stop before that effect carries exactly the previous name choices. -/
theorem settled (report : RotationDirectoryFsyncFailure created returned) :
    (report.cut.image.successor = .durable ↔ report.effective = true) ∧
    (report.effective = true → report.after.crashNames (successorName before) = [some created.child.child]) ∧
    (report.effective = false →
      report.after.crashNames (successorName before) = created.files.crashNames (successorName before)) := by
  refine ⟨?_, ?_, ?_⟩
  · cases effective : report.effective <;> simp [cut, RotationCreateParent.cutAtBarrier, effective]
  · intro effective
    simpa only [effective, ite_true] using report.successorSurvives
  · intro effective
    simpa only [effective, Bool.false_eq_true, ite_false] using report.successorSurvives

/-- The predecessor keeper and marker keep their exact bytes and names
whether or not the directory effect has settled the successor. -/
theorem keepsKeeperMarker (report : RotationDirectoryFsyncFailure created returned) :
    report.after.view.child parent.root (keeperName before) = some parent.keeper.child ∧
    report.after.view.child parent.root "WAL.commit" = some parent.marker.child ∧
    report.after.crashNames (keeperName before) = [some parent.keeper.child] ∧
    report.after.crashNames "WAL.commit" = [some parent.marker.child] ∧
    report.after.inodes.crashBytes (report.after.view.modelObject parent.keeper.child) = [before.wal.active.bytes] ∧
    ∃ marker, before.wal.directory.active.walBoundary = some marker ∧
      report.after.inodes.crashBytes (report.after.view.modelObject parent.marker.child) = [marker] := by
  have prior := (RotationRawCreateEffect.afterOpen (created.afterSync true)).keepsKeeperMarker
  obtain ⟨objects, keeper, marker, keeperName, markerName, _, keeperBytes, markerBound, markerBytes⟩ := prior
  rw [report.view, report.keeperSurvives, report.markerSurvives, report.bytes, created.objects]
  exact ⟨keeper, marker, keeperName, markerName, keeperBytes, _, markerBound, markerBytes⟩

/-- The physically reported name and payload select the same keeper for
recovery. An effective directory barrier permits only the newly created
empty successor. Before effect, the old keeper can still be selected. -/
theorem selectedKeeperPayload (report : RotationDirectoryFsyncFailure created returned)
    {name : Option DeviceInode} (survived : name ∈ report.after.crashNames (successorName before))
    {payload : ByteArray}
    (bytes : payload ∈ report.after.inodes.crashBytes (report.after.view.modelObject (name.getD parent.keeper.child))) :
    report.cut.image.successor.MaySurvive name.isSome ∧
    (report.cut.survivingWal before.wal.directory.active name.isSome).active.bytes = payload ∧
    (report.effective = true → name = some created.child.child ∧ payload = ByteArray.empty) := by
  cases effective : report.effective
  · have beforeEffect := report.settled.2.2 effective
    rw [beforeEffect] at survived
    rw [report.bytes, report.view] at bytes
    have prior := (RotationRawCreateEffect.afterOpen (created.afterSync true)).selectedKeeperPayload
      (cut := report.cut) survived bytes
    exact ⟨by simp [cut, RotationCreateParent.cutAtBarrier, effective, Binding.MaySurvive], prior.1, by simp⟩
  · rw [report.settled.2.1 effective] at survived
    have chosen := List.mem_singleton.mp survived
    subst name
    rw [report.bytes, report.view] at bytes
    change payload ∈ (created.afterSync true).files.inodes.crashBytes
      (created.files.view.modelObject created.child.child) at bytes
    rw [created.inode, created.syncedBytes] at bytes
    have empty := List.mem_singleton.mp bytes
    exact ⟨by simp [cut, RotationCreateParent.cutAtBarrier, effective, Binding.MaySurvive], empty.symm,
      fun _ => ⟨rfl, empty⟩⟩

/-- The chosen physical survivor starts the
fixed-keeper retry with the original acknowledged WAL, even if no open
has yet returned a writer. -/
theorem preparesReopenPrefix (report : RotationDirectoryFsyncFailure created returned)
    (ready : before.RetainedReady directory parent.owner.description)
    {name : Option DeviceInode} (survived : name ∈ report.after.crashNames (successorName before))
    {payload : ByteArray}
    (bytes : payload ∈ report.after.inodes.crashBytes (report.after.view.modelObject (name.getD parent.keeper.child)))
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory
      (report.cut.survivingWal before.wal.directory.active name.isSome).active.first
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry) :
    let keeper := (report.cut.survivingWal before.wal.directory.active name.isSome).active
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry ∧
    retry.image.directory.active = before.target.pair ∧
    (report.effective = true → name = some created.child.child ∧ payload = ByteArray.empty) ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ layout.keeper.bytes = payload ∧ Prepared retry.image layout.target layout.plan := by
  have metadata : before.wal.directory.active ∈ report.cut.image.metadata.crashImages := by
    cases effective : report.effective <;>
      simp [cut, RotationCreateParent.cutAtBarrier, effective, DirectoryPublication.Image.syncDirectory,
        ready.walDirectorySettled]
  obtain ⟨admitted, payload, fixed⟩ := report.selectedKeeperPayload survived bytes
  obtain ⟨trace, pair, layout, selected, prepared⟩ := report.cut.refinesReportedReopenPrefix ready metadata admitted reported
  exact ⟨trace, pair, fixed, layout, selected,
    (congrArg WalSegment.bytes selected).trans payload, prepared⟩

/-- The stopped native schedule and chosen physical survivor start the
fixed-keeper retry with the original acknowledged WAL, even if no open
has yet returned a writer. -/
theorem refinesReopenPrefix (report : RotationDirectoryFsyncStop created)
    (ready : before.RetainedReady directory parent.owner.description)
    {name : Option DeviceInode} (survived : name ∈ report.after.crashNames (successorName before))
    {payload : ByteArray}
    (bytes : payload ∈ report.after.inodes.crashBytes (report.after.view.modelObject (name.getD parent.keeper.child)))
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory
      (report.cut.survivingWal before.wal.directory.active name.isSome).active.first
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry) :
    let keeper := (report.cut.survivingWal before.wal.directory.active name.isSome).active
    report.run = .error directory.path (.poisoned,
      ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) ∧
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry ∧
    retry.image.directory.active = before.target.pair ∧
    (report.effective = true → name = some created.child.child ∧ payload = ByteArray.empty) ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ layout.keeper.bytes = payload ∧ Prepared retry.image layout.target layout.plan := by
  exact ⟨report.stopsSchedule, report.preparesReopenPrefix ready survived bytes reported⟩

end RotationDirectoryFsyncFailure

end Alvoki.Storage.DiskSession
