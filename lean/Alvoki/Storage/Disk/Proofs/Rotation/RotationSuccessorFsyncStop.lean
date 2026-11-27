import Alvoki.Storage.Disk.Proofs.Rotation.RotationCreatePhysical
import Alvoki.Storage.Disk.KeeperReadCustody

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation SyncHandleRouting
open WAL.Boundary (WalInodeImage)

abbrev RotationSuccessorHandle := DescriptorInventory × DescriptorSlot × Nat

abbrev rotationSuccessorPath (directory : DiskDirectory) (before : SegmentedWriterState) :=
  directory.file (.walSegment (before.installed.walBytes / WAL.frameSize))

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
  {parent : RotationCreateParent directory before lookup inventory}

/-- The handle returned by wrapping the raw slot that exclusive open allocated. -/
def RotationRawSuccessor.handle (created : RotationRawSuccessor parent) : RotationSuccessorHandle :=
  (inventory.insert created.raw created.free, created.raw, 0)

/-- File sync changes the new inode's durability and frames its existing
name, all old bytes and every namespace crash choice. -/
def RotationRawSuccessor.afterSync (created : RotationRawSuccessor parent) (effective : Bool) :
    RotationRawSuccessor parent :=
  { created with
    files := { created.files with inodes := if effective then
      created.files.inodes.completeFileSync (inventory.inode created.raw.description) else created.files.inodes }
    empty := by cases effective <;> exact created.empty
    emptySurvivors := by
      intro bytes member
      cases effective
      · exact created.emptySurvivors bytes member
      · apply List.mem_singleton.mp
        simpa [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, created.empty] using member
    bytes := by
      intro inode distinct
      cases effective
      · exact created.bytes inode distinct
      · have unchanged := created.bytes inode distinct
        refine ⟨unchanged.1, ?_⟩
        change (if inode = inventory.inode created.raw.description then
          _ else created.files.inodes.crashBytes inode) = _
        rw [ite_eq_right distinct]
        exact unchanged.2 }

theorem RotationRawSuccessor.syncedBytes (created : RotationRawSuccessor parent) :
    (created.afterSync true).files.inodes.crashBytes (inventory.inode created.raw.description) =
      [ByteArray.empty] := by
  simp [RotationRawSuccessor.afterSync, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, created.empty]

/-- The returned exclusive-open handle is the one selected by the
first file barrier. Both rotation interruption routes use this prefix. -/
structure RotationSuccessorFileIssue (created : RotationRawSuccessor parent) where
  cache : Cache RotationSuccessorHandle
  checked : checkActiveSegmentWith directory before.installed lookup = .ok ()
  openExclusive : FilePath →
    EStateM FilePath (DescriptorInventory × RotationCreateFiles) (Except IO.Error RotationSuccessorHandle)
  returned : openExclusive (rotationSuccessorPath directory before) (inventory, parent.files) =
    .ok (.ok created.handle) (created.handle.1, created.files)
  drops : List LockReferenceDrop
  successorLive : created.raw ∈ (created.handle.1.afterDrops drops).slots
  ownerLive : parent.owner ∈ (created.handle.1.afterDrops drops).slots
  openRead : FilePath → EStateM IO.Error State RotationSuccessorHandle

namespace RotationSuccessorFileIssue

variable {created : RotationRawSuccessor parent}

def atIssue (report : RotationSuccessorFileIssue created) : Cache RotationSuccessorHandle :=
  (report.cache.remember (rotationSuccessorPath directory before) created.handle).consume (rotationSuccessorPath directory before)

def openNew (report : RotationSuccessorFileIssue created) (path : FilePath) :
    ExceptT IO.Error (EStateM FilePath (Cache RotationSuccessorHandle × State)) RotationSuccessorHandle :=
  fun (cache, _) =>
    match report.openExclusive path (inventory, parent.files) with
    | .ok value after => .ok value (cache, parent.project after.2)
    | .error stop after => .error stop (cache, parent.project after.2)

/-- The actual pending hit consumes the successor's entry and selects
the exact description from creation without an additional open. -/
theorem resolves (report : RotationSuccessorFileIssue created) :
    (report.cache.remember (rotationSuccessorPath directory before) created.handle).resolve directory.path
      (rotationSuccessorPath directory before) report.openRead ⟨before.wal.directory, .created⟩ =
    .ok created.handle (report.atIssue, ⟨before.wal.directory, .created⟩) := by
  have separate := file_ne_directory directory (.walSegment (before.installed.walBytes / WAL.frameSize))
  simp [Cache.resolve, atIssue, Cache.remember, pushPending, separate]

theorem custody (report : RotationSuccessorFileIssue created) :
    let inventory := created.handle.1.afterDrops report.drops
    created.raw ∈ inventory.slots ∧ parent.owner ∈ inventory.slots ∧
    created.files.view.child parent.root (renderWalSegmentName (before.installed.walBytes / WAL.frameSize)) =
      some created.child.child ∧ created.files.view.modelObject created.child.child = inventory.inode created.raw.description := by
  refine ⟨report.successorLive, report.ownerLive, ?_, created.inode⟩
  simpa only [created.child.atRoot, created.child.atName] using created.child.binds

theorem opens (report : RotationSuccessorFileIssue created) :
    report.openNew (rotationSuccessorPath directory before) (report.cache, .initial before.wal) =
    .ok (.ok created.handle) (report.cache, ⟨before.wal.directory, .created⟩) := by
  have named := report.custody.2.2.1
  simp [openNew, report.returned, RotationCreateParent.project, named]

end RotationSuccessorFileIssue

/-- The primitive report supplies the stop and possible effect at the
first successor fsync. -/
structure RotationSuccessorFsyncStop (created : RotationRawSuccessor parent)
    extends RotationSuccessorFileIssue created where
  fsync : RotationSuccessorHandle → EStateM FilePath RotationCreateFiles (Except IO.Error Unit)
  effective : Bool
  stopped : fsync created.handle created.files =
    .error (rotationSuccessorPath directory before) (created.afterSync effective).files

namespace RotationSuccessorFsyncStop

variable {created : RotationRawSuccessor parent}

def image (report : RotationSuccessorFsyncStop created) : State :=
  ⟨before.wal.directory, if report.effective then .fileSynced else .created⟩

private def syncPath (report : RotationSuccessorFsyncStop created) (path : FilePath) :
    ExceptT IO.Error (EStateM FilePath (Cache RotationSuccessorHandle × State)) Unit :=
  fun (cache, files) =>
    match cache.resolve directory.path path report.openRead files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, _) => match report.fsync handle created.files with
      | .ok value _ => .ok value (cache, report.image)
      | .error stop _ => .error stop (cache, report.image)

def run (report : RotationSuccessorFsyncStop created) :=
  runRotationWithInterruption directory before lookup report.toRotationSuccessorFileIssue.openNew report.cache
    (fun path => SyncPathGroup.run report.syncPath #[path])

theorem groupStops (report : RotationSuccessorFsyncStop created) :
    (SyncPathGroup.run report.syncPath #[rotationSuccessorPath directory before]).run
      (report.cache.remember (rotationSuccessorPath directory before) created.handle, ⟨before.wal.directory, .created⟩) =
    .error (rotationSuccessorPath directory before) (report.toRotationSuccessorFileIssue.atIssue, report.image) := by
  have stopped : report.syncPath (rotationSuccessorPath directory before)
      (report.cache.remember (rotationSuccessorPath directory before) created.handle, ⟨before.wal.directory, .created⟩) =
      .error (rotationSuccessorPath directory before) (report.toRotationSuccessorFileIssue.atIssue, report.image) := by
    simp only [syncPath, report.toRotationSuccessorFileIssue.resolves, report.stopped]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch,
    Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind,
    StateT.pure, Pure.pure, ExceptT.pure, stopped]

/-- The public rotation stops at the successor file barrier in the
poisoned phase, before installing the successor as the active writer. -/
theorem stopsSchedule (report : RotationSuccessorFsyncStop created) :
    report.run = .error (rotationSuccessorPath directory before)
      (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.image), before.owners⟩) := by
  obtain ⟨_, _, absent⟩ := parent.absent
  have createdReturned := report.toRotationSuccessorFileIssue.opens
  have stopped : (SyncPathGroup.run report.syncPath #[rotationSuccessorPath directory before])
      (report.cache.remember (rotationSuccessorPath directory before) created.handle, ⟨before.wal.directory, .created⟩) =
      .error (rotationSuccessorPath directory before) (report.toRotationSuccessorFileIssue.atIssue, report.image) := report.groupStops
  simp [run, runRotationWithInterruption, rotateWalSchedule, Phase.installed, parent.nonempty, report.checked,
    publishPrepared, rotateFileCall, WalSegmentRotation.runAt_fileEffects, observeSuccessorWith, readEmptyWith,
    optionalMetadataWith, absent, createdReturned, stopped, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, ExceptT.run, ExceptT.lift, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Functor.map, EStateM.map,
    Pure.pure, ExceptT.pure, EStateM.pure, Except.pure]

end RotationSuccessorFsyncStop

private def applyModelStep (action : WalSegmentRotation.Step) : EStateM IO.Error State Unit := fun files =>
  match files.step action with
  | some reached => .ok () reached
  | none => .error (IO.userError "invalid rotation effect") files

/-- A first-create rotation can stop at either barrier. The reported
prefix fixes which barrier was issued and whether its effect applied. -/
def RotationCreateParent.cutAtBarrier (parent : RotationCreateParent directory before lookup inventory)
    (fileReturned effective : Bool) : RotationInFlightCut directory before where
  read := fun path files =>
    match readEmptyWith (m := Except IO.Error) (.ok (lookup path)) path "WAL segment successor is not empty" with
    | .ok value => .ok value files
    | .error cause => .error cause files
  create := fun _ => applyModelStep .createEmpty
  sync := fun path => applyModelStep (if path = directory.path then .syncDirectory else .syncFile)
  nonempty := parent.nonempty
  lookup := by
    obtain ⟨_, _, absent⟩ := parent.absent
    simp [readEmptyWith, optionalMetadataWith, absent, Bind.bind, Except.bind, Pure.pure, Except.pure]
  reports := by
    intro action files
    have separate := file_ne_directory directory (.walSegment (before.installed.walBytes / WAL.frameSize))
    cases action <;> simp only [WalSegmentRotation.performPaths, separate, ite_false, ite_true, applyModelStep]
    · cases files.step .createEmpty <;> simp
    · cases files.step .syncFile <;> simp
    · cases files.step .syncDirectory <;> simp
  completed := if fileReturned then 2 else 1
  within := by cases fileReturned <;> decide
  reached := ⟨before.wal.directory, if fileReturned then .fileSynced else .created⟩
  returned := by
    have separate := file_ne_directory directory (.walSegment (before.installed.walBytes / WAL.frameSize))
    cases fileReturned <;> simp [WalSegmentRotation.steps, WalSegmentRotation.performPaths, separate, applyModelStep,
      State.initial, State.step, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, List.forM_cons, List.forM_nil]
  image := if fileReturned then
    if effective then ⟨before.wal.directory.syncDirectory, .durable⟩ else ⟨before.wal.directory, .fileSynced⟩
    else ⟨before.wal.directory, if effective then .fileSynced else .created⟩
  effect := by
    cases effective
    · cases fileReturned <;> exact .inl rfl
    · cases fileReturned
      · exact .inr ⟨.syncFile, rfl, rfl⟩
      · exact .inr ⟨.syncDirectory, rfl, rfl⟩

namespace RotationSuccessorFsyncStop

variable {created : RotationRawSuccessor parent}

def cut (report : RotationSuccessorFsyncStop created) : RotationInFlightCut directory before :=
  parent.cutAtBarrier false report.effective

/-- The file barrier leaves all names unsettled exactly as at creation.
Only the empty successor's own payload is settled by an effective sync. -/
theorem fileEffect (report : RotationSuccessorFsyncStop created) :
    (created.afterSync report.effective).files.crashNames = created.files.crashNames ∧
    (report.effective = true →
      (created.afterSync report.effective).files.inodes.crashBytes (inventory.inode created.raw.description) =
        [ByteArray.empty]) := by
  refine ⟨rfl, ?_⟩
  intro settled
  rw [settled]
  exact created.syncedBytes

/-- The raw frame retains the old keeper, marker and lock bindings. Live
slots at the barrier come from the reached census in `custody`. -/
theorem reachedEffect (report : RotationSuccessorFsyncStop created) :
    RotationRawCreateEffect parent (created.handle.1, (created.afterSync report.effective).files) :=
  .afterOpen (created.afterSync report.effective)

/-- The new inode's exact crash payload or the old keeper's durable
payload feeds the same fixed-keeper retry as the interrupted create.
The reported fault is before directory settlement and ready installation. -/
theorem refinesReopenPrefix (report : RotationSuccessorFsyncStop created)
    (ready : before.RetainedReady directory parent.owner.description)
    {name : Option DeviceInode}
    (survived : name ∈ (created.afterSync report.effective).files.crashNames
      (renderWalSegmentName (before.installed.walBytes / WAL.frameSize)))
    {payload : ByteArray}
    (bytes : payload ∈ (created.afterSync report.effective).files.inodes.crashBytes
      ((created.afterSync report.effective).files.view.modelObject (name.getD parent.keeper.child)))
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory
      (report.cut.survivingWal before.wal.directory.active name.isSome).active.first
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry) :
    let keeper := (report.cut.survivingWal before.wal.directory.active name.isSome).active
    report.run = .error (rotationSuccessorPath directory before) (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) ∧
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (report.cut.crashedFiles before.wal.directory.active name.isSome) retry ∧
    retry.image.directory.active = before.target.pair ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ layout.keeper.bytes = payload ∧ Prepared retry.image layout.target layout.plan := by
  have metadata : before.wal.directory.active ∈ report.cut.image.metadata.crashImages := by
    change before.wal.directory.active ∈ before.wal.directory.crashImages
    simp [ready.walDirectorySettled]
  have maySurvive : report.cut.image.successor.MaySurvive name.isSome := by
    cases effective : report.effective <;> simp [cut, RotationCreateParent.cutAtBarrier, effective, Binding.MaySurvive]
  obtain ⟨trace, pair, layout, selected, prepared⟩ := report.cut.refinesReportedReopenPrefix ready metadata maySurvive reported
  have payloadBytes := (report.reachedEffect.selectedKeeperPayload (cut := report.cut) survived bytes).1
  exact ⟨report.stopsSchedule, trace, pair, layout, selected, (congrArg WalSegment.bytes selected).trans payloadBytes,
    prepared⟩

end RotationSuccessorFsyncStop

end Alvoki.Storage.DiskSession
