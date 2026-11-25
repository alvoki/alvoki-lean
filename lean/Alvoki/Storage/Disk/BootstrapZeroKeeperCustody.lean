import Alvoki.Storage.Disk.ObservedBootstrapCache
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage

private abbrev zeroPath (directory : DiskDirectory) : FilePath := directory.file (.walSegment 0)

private def imageResult : EStateM.Result IO.Error (Cache Handle × Files) Unit →
    EStateM.Result IO.Error WalSegmentRotation.State Unit
  | .ok () (_, rotation, _) => .ok () rotation
  | .error cause (_, rotation, _) => .error cause rotation

private theorem zeroPath_ne_directory (directory : DiskDirectory) : zeroPath directory ≠ directory.path := by
  intro same
  have lengths := congrArg (fun path : FilePath => path.toString.length) same
  rw [show zeroPath directory = directory.file (.walSegment 0) from rfl, directory.walSegment_path] at lengths
  simp [String.length_append] at lengths
  have slash : "/".length = 1 := by decide
  rw [slash] at lengths
  omega

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

/-- At a markerless bootstrap that sees no segment zero, the exclusive
open adds the reported slot to the reached listing census. The namespace
reports identify the new named empty inode and the retained directory.
The return equations record the actual file and directory sync effects. -/
structure BootstrapFreshZeroKeeper (listed : BootstrapCheckedListing captured) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  absent : ∃ name message, lookup (zeroPath directory) = .error (.noFileOrDirectory name 2 message)
  probeProjection : calls.readEmpty (zeroPath directory) =
    WalSegmentRotation.readEmptyWith (.ok (lookup (zeroPath directory))) (zeroPath directory) WAL.Boundary.missingOpenMarker
  probeParent : DeviceInode
  probeAtRoot : probeParent = captured.root
  missing : captured.view.child probeParent (renderWalSegmentName 0) = none
  initial : WalInodeImage
  opened : WalInodeImage
  openExclusive : FilePath → EStateM IO.Error Files Handle
  openRead : FilePath → EStateM IO.Error Files Handle
  fsync : Handle → EStateM IO.Error Files Unit
  beforeCreate : List LockReferenceDrop
  lockBeforeCreate : calls.slot ∈ (listed.scan.afterClose.afterDrops beforeCreate).slots
  directoryBeforeCreate : captured.cached ∈ (listed.scan.afterClose.afterDrops beforeCreate).slots
  slot : DescriptorSlot
  free : ∀ other ∈ (listed.scan.afterClose.afterDrops beforeCreate).slots, other.address ≠ slot.address
  freshInode : ∀ other ∈ (listed.scan.afterClose.afterDrops beforeCreate).slots,
    (listed.scan.afterClose.afterDrops beforeCreate).inode slot.description ≠
      (listed.scan.afterClose.afterDrops beforeCreate).inode other.description
  created : openExclusive (zeroPath directory) (before.image, initial) =
    .ok ((listed.scan.afterClose.afterDrops beforeCreate).insert slot free, slot, 0)
      (⟨before.image.metadata, .created⟩, opened)
  namespaceView : DirectoryReadNamespace
  sameObjects : namespaceView.modelObject = captured.view.modelObject
  child : RunChildLookup captured.root (renderWalSegmentName 0) namespaceView
  object : namespaceView.modelObject child.child = (listed.scan.afterClose.afterDrops beforeCreate).inode slot.description
  active : opened.active = namespaceView.modelObject child.child
  empty : opened.visible opened.active = ByteArray.empty
  beforeFile : List LockReferenceDrop
  fileLive : slot ∈ (((listed.scan.afterClose.afterDrops beforeCreate).insert slot free).afterDrops beforeFile).slots
  afterFile : List LockReferenceDrop
  lockLive : calls.slot ∈ (((listed.scan.afterClose.afterDrops beforeCreate).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  directoryLive : captured.cached ∈ (((listed.scan.afterClose.afterDrops beforeCreate).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  fileSynced :
    let keeper := ((listed.scan.afterClose.afterDrops beforeCreate).insert slot free, slot, 0)
    fsync keeper (⟨before.image.metadata, .created⟩, opened) =
      .ok () (⟨before.image.metadata, .fileSynced⟩, opened.completeFileSync opened.active)
  directorySynced :
    let childSynced := opened.completeFileSync opened.active
    fsync (captured.reached, captured.cached, 0) (⟨before.image.metadata, .fileSynced⟩, childSynced) =
      .ok () (⟨before.image.metadata.syncDirectory, .durable⟩, childSynced.settleBinding)
  projectCreate :
    calls.createEmpty captured.cache (zeroPath directory) before.image =
      imageResult (stageFreshWithCache (zeroPath directory) ByteArray.empty (fun name _ => openExclusive name)
        (captured.cache, before.image, initial))
  projectFile :
    let keeper := ((listed.scan.afterClose.afterDrops beforeCreate).insert slot free, slot, 0)
    calls.sync captured.cache #[zeroPath directory] ⟨before.image.metadata, .created⟩ =
      imageResult (SyncPathGroup.run (sync directory.path openRead fsync) #[zeroPath directory]
        (captured.cache.remember (zeroPath directory) keeper, ⟨before.image.metadata, .created⟩, opened))
  projectDirectory :
    calls.sync captured.cache #[directory.path] ⟨before.image.metadata, .fileSynced⟩ =
      imageResult (SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path]
        (captured.cache.consume (zeroPath directory), ⟨before.image.metadata, .fileSynced⟩,
          opened.completeFileSync opened.active))

namespace BootstrapFreshZeroKeeper

variable {listed : BootstrapCheckedListing captured}

theorem absentSegment (observed : BootstrapFreshZeroKeeper listed) : before.image.successor = .absent := by
  obtain ⟨_, _, raw⟩ := observed.absent
  have probe := observed.probeProjection
  rw [raw, calls.zeroRead] at probe
  have missing : before.image.observeSuccessor = none := Except.ok.inj probe
  simpa [WalSegmentRotation.State.observeSuccessor] using missing

/-- The executed create and grouped barriers thread the cache and the
same keeper inode. File sync consumes the pending entry. Directory sync
then uses the original directory handle and settles the synced inode. -/
theorem callbacks (observed : BootstrapFreshZeroKeeper listed) :
    let path := zeroPath directory
    let keeper : Handle := ((listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free,
      observed.slot, 0)
    let atFile : Files := (⟨before.image.metadata, .created⟩, observed.opened)
    let atDirectory : Files := (⟨before.image.metadata, .fileSynced⟩,
      observed.opened.completeFileSync observed.opened.active)
    let settled : Files := (⟨before.image.metadata.syncDirectory, .durable⟩, atDirectory.2.settleBinding)
    let grouped := SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
    let pending := captured.cache.remember path keeper
    let consumed := captured.cache.consume path
    stageFreshWithCache path ByteArray.empty (fun name _ => observed.openExclusive name)
      (captured.cache, before.image, observed.initial) = .ok () (pending, atFile) ∧
    grouped #[path] (pending, atFile) = .ok () (consumed, atDirectory) ∧
    grouped #[directory.path] (consumed, atDirectory) = .ok () (consumed, settled) := by
  intro path keeper atFile atDirectory settled grouped pending consumed
  refine ⟨?_, ?_, ?_⟩
  · simp [stageFreshWithCache, path, observed.created, pending, atFile, keeper]
  · change SyncPathGroup.run (sync directory.path observed.openRead observed.fsync) #[path] (pending, atFile) = _
    rw [SyncPathGroup.run_single]
    dsimp only [pending]
    rw [syncRemembered (zeroPath_ne_directory directory) keeper observed.openRead observed.fsync atFile,
      show observed.fsync keeper atFile = .ok () atDirectory from observed.fileSynced]
  · change SyncPathGroup.run (sync directory.path observed.openRead observed.fsync) #[directory.path]
      (consumed, atDirectory) = _
    rw [SyncPathGroup.run_single]
    have projected : consumed.directory = some (captured.reached, captured.cached, 0) := rfl
    simp [sync, Cache.resolve, projected, observed.directorySynced, atDirectory, settled, withCache]

/-- The initial listing is the base census. The file issuer and the
retained directory identify the created child and its canonical parent.
Once both reported barriers complete, the only modeled surviving zero
keeper binding has exactly the empty payload. -/
theorem settledKeeper (observed : BootstrapFreshZeroKeeper listed) :
    let inventory := (listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free
    let after := (observed.opened.completeFileSync observed.opened.active).settleBinding
    observed.slot ∈ (inventory.afterDrops observed.beforeFile).slots ∧
    calls.slot ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    captured.cached ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    captured.view.child captured.root (renderWalSegmentName 0) = none ∧
    observed.namespaceView.modelObject captured.root = inventory.inode captured.cached.description ∧
    observed.namespaceView.child captured.root (renderWalSegmentName 0) = some observed.child.child ∧
    observed.opened.active = inventory.inode observed.slot.description ∧
    observed.opened.active ≠ inventory.inode calls.slot.description ∧
    observed.opened.active ≠ inventory.inode captured.cached.description ∧
    after.crashBindings = [observed.opened.active] ∧ after.crashBytes observed.opened.active = [ByteArray.empty] := by
  intro inventory after
  have openedObject : observed.opened.active = inventory.inode observed.slot.description :=
    observed.active.trans observed.object
  refine ⟨observed.fileLive, observed.lockLive, observed.directoryLive, observed.probeAtRoot ▸ observed.missing,
    ?_, ?_, openedObject, openedObject.symm ▸ observed.freshInode calls.slot observed.lockBeforeCreate,
    openedObject.symm ▸ observed.freshInode captured.cached observed.directoryBeforeCreate, rfl, ?_⟩
  · rw [observed.sameObjects]
    change captured.view.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
    rw [listed.scan.afterClose_eq]
    exact captured.captures.2.2.2.2
  · have bound := observed.child.binds
    rwa [observed.child.atRoot, observed.child.atName] at bound
  · simp [after, WalInodeImage.settleBinding, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync,
      observed.empty]

/-- The captured exclusive open and both reached syncs supply the
existing rotation contract at segment zero before marker publication. -/
theorem rotationHealthy (observed : BootstrapFreshZeroKeeper listed) : calls.RotationHealthy captured.cache := by
  have created := observed.projectCreate
  have file := observed.projectFile
  have directorySync := observed.projectDirectory
  obtain ⟨rawCreate, rawFile, rawDirectory⟩ := observed.callbacks
  dsimp only at rawCreate rawFile rawDirectory file
  rw [rawCreate] at created
  rw [rawFile] at file
  rw [rawDirectory] at directorySync
  have absent := observed.absentSegment
  have creates : before.image.step .createEmpty = some ⟨before.image.metadata, .created⟩ := by
    simp [WalSegmentRotation.State.step, absent]
  intro done step todo prior next order reached effect
  have schedule : WalSegmentRotation.steps before.image.observeSuccessor.isSome =
      [.createEmpty, .syncFile, .syncDirectory] := by
    simp [WalSegmentRotation.steps, WalSegmentRotation.State.observeSuccessor, absent]
  rw [schedule] at order
  rcases done with _ | ⟨_, _ | ⟨_, _ | ⟨_, rest⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, _⟩ := order
    cases reached
    rw [creates] at effect
    cases effect
    exact created
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, rfl, _⟩ := order
    simp [WalSegmentRotation.State.execute, List.foldlM_cons, creates, Bind.bind, Option.bind] at reached
    cases reached
    cases effect
    exact file
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, rfl, rfl, _⟩ := order
    simp [WalSegmentRotation.State.execute, List.foldlM_cons, creates, Bind.bind, Option.bind] at reached
    cases reached
    cases effect
    exact directorySync
  · simp at order

/-- The admitted markerless opener installs on the same reached cache.
Only the later marker operations still require their separate reports. -/
theorem installs {input : FilePath} (observed : BootstrapFreshZeroKeeper listed)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (marker : calls.MarkerHealthy captured.cache) (allowCollection : Bool) :
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      calls.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer :=
  (SegmentedBatchDatabaseTrace.fromBootstrapWithCapturedCache captured listed admission valid
    observed.rotationHealthy marker allowCollection).2.2.2

end BootstrapFreshZeroKeeper

end Alvoki.Storage.DiskSession
