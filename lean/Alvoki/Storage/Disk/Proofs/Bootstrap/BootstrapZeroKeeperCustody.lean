import Alvoki.Storage.Disk.Proofs.Bootstrap.ObservedBootstrapCache
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage

private abbrev zeroPath (directory : DiskDirectory) : FilePath := directory.file (.walSegment 0)

def zeroKeeperProjection : EStateM.Result IO.Error (Cache Handle × Files) Unit →
    EStateM.Result IO.Error WalSegmentRotation.State Unit
  | .ok () (_, rotation, _) => .ok () rotation
  | .error cause (_, rotation, _) => .error cause rotation

theorem zeroPath_ne_directory (directory : DiskDirectory) : zeroPath directory ≠ directory.path := by
  intro same
  have lengths := congrArg (fun path : FilePath => path.toString.length) same
  rw [show zeroPath directory = directory.file (.walSegment 0) from rfl, directory.walSegment_path] at lengths
  simp [String.length_append] at lengths
  have slash : "/".length = 1 := by decide
  rw [slash] at lengths
  omega

/-- Both zero-keeper routes use the retained directory handle. -/
private theorem retainedDirectorySync {directory : DiskDirectory} {cache : Cache Handle} {handle : Handle}
    {before after : Files} (openRead : FilePath → EStateM IO.Error Files Handle)
    (fsync : Handle → EStateM IO.Error Files Unit) (captured : cache.directory = some handle)
    (reported : fsync handle before = .ok () after) :
    SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path] (cache, before) =
      .ok () (cache, after) := by
  rw [SyncPathGroup.run_single]
  simp [sync, Cache.resolve, captured, reported, withCache]

private def HealthySteps (perform : WalSegmentRotation.Step → EStateM IO.Error WalSegmentRotation.State Unit)
    (before : WalSegmentRotation.State) (steps : List WalSegmentRotation.Step) : Prop :=
  ∀ done step todo prior next, steps = done ++ step :: todo →
    before.execute done = some prior → prior.step step = some next → perform step prior = .ok () next

private theorem HealthySteps.prepend
    {perform : WalSegmentRotation.Step → EStateM IO.Error WalSegmentRotation.State Unit}
    {before after : WalSegmentRotation.State} {step : WalSegmentRotation.Step} {rest : List WalSegmentRotation.Step}
    (effect : before.step step = some after) (returned : perform step before = .ok () after)
    (tail : HealthySteps perform after rest) : HealthySteps perform before (step :: rest) := by
  intro done action todo prior next order reached applied
  cases done with
  | nil =>
    obtain ⟨same, _⟩ := List.cons.inj order
    subst action
    have same : before = prior := Option.some.inj reached
    subst prior
    have same := Option.some.inj (effect.symm.trans applied)
    exact same ▸ returned
  | cons head done =>
    obtain ⟨same, restOrder⟩ := List.cons.inj order
    subst head
    have reachedTail : after.execute done = some prior := by
      simpa [WalSegmentRotation.State.execute, List.foldlM_cons, effect, Bind.bind, Option.bind] using reached
    exact tail done action todo prior next restOrder reachedTail applied

private theorem HealthySteps.none
    (perform : WalSegmentRotation.Step → EStateM IO.Error WalSegmentRotation.State Unit) (before : WalSegmentRotation.State) :
    HealthySteps perform before [] := by
  intro done step todo prior next order
  have lengths := congrArg List.length order
  simp at lengths

private def afterZeroFileSync (before : WalSegmentRotation.State) : WalSegmentRotation.State :=
  { before with successor := if before.successor = .created then .fileSynced else before.successor }

private theorem syncZeroFileStep {before : WalSegmentRotation.State}
    (present : before.successor ≠ .absent) : before.step .syncFile = some (afterZeroFileSync before) := by
  cases before with
  | mk metadata binding =>
    cases binding <;> simp_all [WalSegmentRotation.State.step, afterZeroFileSync]

private theorem syncZeroDirectoryStep {before : WalSegmentRotation.State} (present : before.successor ≠ .absent) :
    (afterZeroFileSync before).step .syncDirectory = some ⟨before.metadata.syncDirectory, .durable⟩ := by
  cases before with
  | mk metadata binding =>
    cases binding <;> simp_all [WalSegmentRotation.State.step, afterZeroFileSync]

private theorem syncedZeroKeeperBytes (image : WalInodeImage) (empty : image.visible image.active = ByteArray.empty) :
    let settled := (image.completeFileSync image.active).settleBinding
    settled.crashBindings = [image.active] ∧ settled.crashBytes image.active = [ByteArray.empty] :=
  ⟨rfl, by simp [WalInodeImage.settleBinding, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, empty]⟩

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

/-- At a markerless bootstrap that sees no segment zero, the exclusive
open adds the reported slot to the reached listing census. The namespace
reports identify the new named empty inode and the retained directory.
The pending description is available at the next file barrier. -/
structure BootstrapFreshZeroKeeperOpen (listed : BootstrapCheckedListing captured) where
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
  projectCreate :
    calls.createEmpty captured.cache (zeroPath directory) before.image =
      zeroKeeperProjection (stageFreshWithCache (zeroPath directory) ByteArray.empty (fun name _ => openExclusive name)
        (captured.cache, before.image, initial))
  projectFile :
    let keeper := ((listed.scan.afterClose.afterDrops beforeCreate).insert slot free, slot, 0)
    calls.sync captured.cache #[zeroPath directory] ⟨before.image.metadata, .created⟩ =
      zeroKeeperProjection (SyncPathGroup.run (sync directory.path openRead fsync) #[zeroPath directory]
        (captured.cache.remember (zeroPath directory) keeper, ⟨before.image.metadata, .created⟩, opened))

/-- The opened keeper prefix followed by a successful file barrier. -/
structure BootstrapFreshZeroKeeperPrefix (listed : BootstrapCheckedListing captured)
    extends BootstrapFreshZeroKeeperOpen listed where
  fileSynced :
    let keeper := ((listed.scan.afterClose.afterDrops beforeCreate).insert slot free, slot, 0)
    fsync keeper (⟨before.image.metadata, .created⟩, opened) =
      .ok () (⟨before.image.metadata, .fileSynced⟩, opened.completeFileSync opened.active)
  projectDirectory :
    calls.sync captured.cache #[directory.path] ⟨before.image.metadata, .fileSynced⟩ =
      zeroKeeperProjection (SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path]
        (captured.cache.consume (zeroPath directory), ⟨before.image.metadata, .fileSynced⟩,
          opened.completeFileSync opened.active))

/-- Fresh creation whose directory barrier succeeds. -/
structure BootstrapFreshZeroKeeper (listed : BootstrapCheckedListing captured)
    extends BootstrapFreshZeroKeeperPrefix listed where
  directorySynced :
    let childSynced := opened.completeFileSync opened.active
    fsync (captured.reached, captured.cached, 0) (⟨before.image.metadata, .fileSynced⟩, childSynced) =
      .ok () (⟨before.image.metadata.syncDirectory, .durable⟩, childSynced.settleBinding)

variable {listed : BootstrapCheckedListing captured}

namespace BootstrapFreshZeroKeeperOpen

theorem absentSegment (observed : BootstrapFreshZeroKeeperOpen listed) : before.image.successor = .absent := by
  obtain ⟨_, _, raw⟩ := observed.absent
  have probe := observed.probeProjection
  rw [raw, calls.zeroRead] at probe
  have missing : before.image.observeSuccessor = none := Except.ok.inj probe
  simpa [WalSegmentRotation.State.observeSuccessor] using missing

theorem create (observed : BootstrapFreshZeroKeeperOpen listed) :
    let path := zeroPath directory
    let keeper : Handle := ((listed.scan.afterClose.afterDrops observed.beforeCreate).insert
      observed.slot observed.free, observed.slot, 0)
    stageFreshWithCache path ByteArray.empty (fun name _ => observed.openExclusive name)
      (captured.cache, before.image, observed.initial) =
      .ok () (captured.cache.remember path keeper, (⟨before.image.metadata, .created⟩, observed.opened)) := by
  dsimp only
  rw [stageFreshWithCache, observed.created]

end BootstrapFreshZeroKeeperOpen

namespace BootstrapFreshZeroKeeperPrefix

abbrev absentSegment (observed : BootstrapFreshZeroKeeperPrefix listed) : before.image.successor = .absent :=
  observed.toBootstrapFreshZeroKeeperOpen.absentSegment

/-- The exclusive create and file barrier thread the exact cached keeper
through the file sync and consume its pending entry. -/
theorem filePrefix (observed : BootstrapFreshZeroKeeperPrefix listed) :
    let path := zeroPath directory
    let keeper : Handle := ((listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free,
      observed.slot, 0)
    let atFile : Files := (⟨before.image.metadata, .created⟩, observed.opened)
    let atDirectory : Files := (⟨before.image.metadata, .fileSynced⟩,
      observed.opened.completeFileSync observed.opened.active)
    let grouped := SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
    let pending := captured.cache.remember path keeper
    let consumed := captured.cache.consume path
    stageFreshWithCache path ByteArray.empty (fun name _ => observed.openExclusive name)
      (captured.cache, before.image, observed.initial) = .ok () (pending, atFile) ∧
    grouped #[path] (pending, atFile) = .ok () (consumed, atDirectory) := by
  intro path keeper atFile atDirectory grouped pending consumed
  refine ⟨?_, ?_⟩
  · exact observed.toBootstrapFreshZeroKeeperOpen.create
  · change SyncPathGroup.run (sync directory.path observed.openRead observed.fsync) #[path] (pending, atFile) = _
    rw [SyncPathGroup.run_single]
    dsimp only [pending]
    rw [syncRemembered (zeroPath_ne_directory directory) keeper observed.openRead observed.fsync atFile,
      show observed.fsync keeper atFile = .ok () atDirectory from observed.fileSynced]

end BootstrapFreshZeroKeeperPrefix

namespace BootstrapFreshZeroKeeper

abbrev absentSegment (observed : BootstrapFreshZeroKeeper listed) : before.image.successor = .absent :=
  observed.toBootstrapFreshZeroKeeperPrefix.absentSegment

/-- The executed create, file sync and directory sync thread the same
keeper inode and original directory handle. -/
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
    grouped #[directory.path] (consumed, atDirectory) = .ok () (consumed, settled) :=
  ⟨observed.toBootstrapFreshZeroKeeperPrefix.filePrefix.1, observed.toBootstrapFreshZeroKeeperPrefix.filePrefix.2,
    retainedDirectorySync observed.openRead observed.fsync rfl observed.directorySynced⟩

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
    openedObject.symm ▸ observed.freshInode captured.cached observed.directoryBeforeCreate,
    syncedZeroKeeperBytes observed.opened observed.empty⟩
  · rw [observed.sameObjects]
    change captured.view.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
    rw [listed.scan.afterClose_eq]
    exact captured.captures.2.2.2.2
  · have bound := observed.child.binds
    rwa [observed.child.atRoot, observed.child.atName] at bound

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
  have schedule : WalSegmentRotation.steps before.image.observeSuccessor.isSome =
      [.createEmpty, .syncFile, .syncDirectory] := by
    simp [WalSegmentRotation.steps, WalSegmentRotation.State.observeSuccessor, absent]
  unfold BootstrapOpenCalls.RotationHealthy
  rw [schedule]
  exact HealthySteps.prepend creates created (HealthySteps.prepend rfl file
    (HealthySteps.prepend rfl directorySync (HealthySteps.none _ _)))

end BootstrapFreshZeroKeeper

/-- A checked, already present zero keeper is reused. The separate
no-follow lookup and read open resolve the same canonical child in the
captured root. Only the file sync uses the new read description. -/
structure BootstrapReusedZeroKeeperOpen (listed : BootstrapCheckedListing captured) where
  lookup : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  metadata : IO.FS.Metadata
  statChild : RunChildLookup captured.root (renderWalSegmentName 0) captured.view
  stat : lookup (zeroPath directory) = .ok (metadata, statChild.child)
  regular : metadata.type = .file
  singleLink : metadata.numLinks = 1
  size : metadata.byteSize = 0
  probeProjection : calls.readEmpty (zeroPath directory) =
    WalSegmentRotation.readEmptyWith (.ok ((lookup (zeroPath directory)).map Prod.fst)) (zeroPath directory)
      WAL.Boundary.missingOpenMarker
  openedChild : RunChildLookup captured.root (renderWalSegmentName 0) captured.view
  files : WalInodeImage
  statObject : captured.view.modelObject statChild.child = files.active
  extent : metadata.byteSize.toNat = (files.visible files.active).size
  openRead : FilePath → EStateM IO.Error Files Handle
  fsync : Handle → EStateM IO.Error Files Unit
  beforeOpen : List LockReferenceDrop
  lockBeforeOpen : calls.slot ∈ (listed.scan.afterClose.afterDrops beforeOpen).slots
  directoryBeforeOpen : captured.cached ∈ (listed.scan.afterClose.afterDrops beforeOpen).slots
  slot : DescriptorSlot
  free : ∀ other ∈ (listed.scan.afterClose.afterDrops beforeOpen).slots, other.address ≠ slot.address
  openedObject : captured.view.modelObject openedChild.child =
    (listed.scan.afterClose.afterDrops beforeOpen).inode slot.description
  fresh : (listed.scan.afterClose.afterDrops beforeOpen).references slot.description = []
  opened : openRead (zeroPath directory) (before.image, files) =
    .ok ((listed.scan.afterClose.afterDrops beforeOpen).insert slot free, slot, 0) (before.image, files)
  beforeFile : List LockReferenceDrop
  fileLive : slot ∈ (((listed.scan.afterClose.afterDrops beforeOpen).insert slot free).afterDrops beforeFile).slots
  afterFile : List LockReferenceDrop
  lockLive : calls.slot ∈ (((listed.scan.afterClose.afterDrops beforeOpen).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  directoryLive : captured.cached ∈ (((listed.scan.afterClose.afterDrops beforeOpen).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  projectFile :
    calls.sync captured.cache #[zeroPath directory] before.image =
      zeroKeeperProjection (SyncPathGroup.run (sync directory.path openRead fsync) #[zeroPath directory]
        (captured.cache, before.image, files))

/-- The opened keeper prefix followed by a successful file barrier. -/
structure BootstrapReusedZeroKeeperPrefix (listed : BootstrapCheckedListing captured)
    extends BootstrapReusedZeroKeeperOpen listed where
  fileSynced :
    let keeper := ((listed.scan.afterClose.afterDrops beforeOpen).insert slot free, slot, 0)
    fsync keeper (before.image, files) =
      .ok () (afterZeroFileSync before.image, files.completeFileSync files.active)
  projectDirectory :
    calls.sync captured.cache #[directory.path] (afterZeroFileSync before.image) =
      zeroKeeperProjection (SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path]
        (captured.cache, afterZeroFileSync before.image, files.completeFileSync files.active))

/-- Checked reuse whose directory barrier succeeds. -/
structure BootstrapReusedZeroKeeper (listed : BootstrapCheckedListing captured)
    extends BootstrapReusedZeroKeeperPrefix listed where
  directorySynced :
    let childSynced := files.completeFileSync files.active
    fsync (captured.reached, captured.cached, 0) (afterZeroFileSync before.image, childSynced) =
      .ok () (⟨before.image.metadata.syncDirectory, .durable⟩, childSynced.settleBinding)

namespace BootstrapReusedZeroKeeperOpen

/-- The checked metadata probe produces the literal empty byte array.
The observed extent also identifies the physical contents as empty. -/
theorem readEmpty (observed : BootstrapReusedZeroKeeperOpen listed) :
    calls.readEmpty (zeroPath directory) = .ok (some ByteArray.empty) ∧
    before.image.observeSuccessor = some ByteArray.empty ∧
    observed.files.visible observed.files.active = ByteArray.empty := by
  have read : calls.readEmpty (zeroPath directory) = .ok (some ByteArray.empty) := by
    have regular : (observed.metadata.type == .file) = true := by rw [observed.regular]; rfl
    rw [observed.probeProjection]
    simp [WalSegmentRotation.readEmptyWith, optionalMetadataWith, checkPrivateRegularWith, observed.stat,
      regular, observed.singleLink, observed.size, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have empty := observed.extent.symm
  rw [observed.size] at empty
  exact ⟨read, Except.ok.inj (calls.zeroRead.symm.trans read), ByteArray.size_eq_zero_iff.mp empty⟩

end BootstrapReusedZeroKeeperOpen

namespace BootstrapReusedZeroKeeperPrefix

abbrev fileSyncedState (_ : BootstrapReusedZeroKeeperPrefix listed) : WalSegmentRotation.State :=
  afterZeroFileSync before.image

abbrev readEmpty (observed : BootstrapReusedZeroKeeperPrefix listed) :=
  observed.toBootstrapReusedZeroKeeperOpen.readEmpty

/-- The read-only file open occurs on a cache miss. The directory barrier
still routes to the original captured handle, even though the file open
returned a distinct slot table and there is no pending entry to consume. -/
theorem filePrefix (observed : BootstrapReusedZeroKeeperPrefix listed) :
    let atFile : Files := (before.image, observed.files)
    let atDirectory : Files := (afterZeroFileSync before.image, observed.files.completeFileSync observed.files.active)
    let grouped := SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
    grouped #[zeroPath directory] (captured.cache, atFile) = .ok () (captured.cache, atDirectory) := by
  intro atFile atDirectory grouped
  change SyncPathGroup.run (sync directory.path observed.openRead observed.fsync) #[zeroPath directory]
    (captured.cache, atFile) = _
  rw [SyncPathGroup.run_single]
  have separate : (zeroPath directory == directory.path) = false := by
    simpa using zeroPath_ne_directory directory
  have resolved := observed.opened
  dsimp only [atFile]
  have pending : captured.cache.pending = [] := rfl
  have active : captured.cache.active = none := rfl
  simp [sync, Cache.resolve, pending, active, separate, resolved, observed.fileSynced, withCache, atDirectory]

end BootstrapReusedZeroKeeperPrefix

namespace BootstrapReusedZeroKeeper

abbrev readEmpty (observed : BootstrapReusedZeroKeeper listed) :=
  observed.toBootstrapReusedZeroKeeperPrefix.readEmpty

/-- The keeper sync opens the checked child on a cache miss, and the
directory barrier uses the original captured description. -/
theorem callbacks (observed : BootstrapReusedZeroKeeper listed) :
    let atFile : Files := (before.image, observed.files)
    let atDirectory : Files := (afterZeroFileSync before.image, observed.files.completeFileSync observed.files.active)
    let settled : Files := (⟨before.image.metadata.syncDirectory, .durable⟩, atDirectory.2.settleBinding)
    let grouped := SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
    grouped #[zeroPath directory] (captured.cache, atFile) = .ok () (captured.cache, atDirectory) ∧
    grouped #[directory.path] (captured.cache, atDirectory) = .ok () (captured.cache, settled) :=
  ⟨observed.toBootstrapReusedZeroKeeperPrefix.filePrefix,
    retainedDirectorySync observed.openRead observed.fsync rfl observed.directorySynced⟩

/-- The same identified empty inode that passed no-follow lookup is
synced through the newly opened file description and survives settlement.
The lock and captured directory remain live through both callbacks. -/
theorem settledKeeper (observed : BootstrapReusedZeroKeeper listed) :
    let inventory := (listed.scan.afterClose.afterDrops observed.beforeOpen).insert observed.slot observed.free
    let after := (observed.files.completeFileSync observed.files.active).settleBinding
    observed.slot ∈ (inventory.afterDrops observed.beforeFile).slots ∧
    calls.slot ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    captured.cached ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    captured.view.modelObject captured.root = inventory.inode captured.cached.description ∧
    captured.view.child captured.root (renderWalSegmentName 0) = some observed.statChild.child ∧
    observed.openedChild.child = observed.statChild.child ∧
    observed.files.active = inventory.inode observed.slot.description ∧
    observed.slot.description ≠ calls.slot.description ∧ observed.slot.description ≠ captured.cached.description ∧
    after.crashBindings = [observed.files.active] ∧ after.crashBytes observed.files.active = [ByteArray.empty] := by
  intro inventory after
  have bound := observed.statChild.binds
  rw [observed.statChild.atRoot, observed.statChild.atName] at bound
  have same := observed.openedChild.child_eq bound
  have freshFrom (old : DescriptorSlot) (live : old ∈ (listed.scan.afterClose.afterDrops observed.beforeOpen).slots) :
      observed.slot.description ≠ old.description := by
    intro same
    have present : old.reference ∈ (listed.scan.afterClose.afterDrops observed.beforeOpen).references observed.slot.description :=
      (DescriptorInventory.mem_references _).mpr ⟨old, live, rfl, same.symm⟩
    rw [observed.fresh] at present
    exact List.not_mem_nil present
  refine ⟨observed.fileLive, observed.lockLive, observed.directoryLive, ?_, bound, same, ?_,
    freshFrom calls.slot observed.lockBeforeOpen, freshFrom captured.cached observed.directoryBeforeOpen,
    syncedZeroKeeperBytes observed.files observed.readEmpty.2.2⟩
  · change captured.view.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
    rw [listed.scan.afterClose_eq]
    exact captured.captures.2.2.2.2
  · exact observed.statObject.symm.trans ((congrArg captured.view.modelObject same).symm.trans observed.openedObject)

/-- The existing rotation schedule takes the two-barrier branch. There
is no exclusive create callback after the checked zero-length lookup. -/
theorem rotationHealthy (observed : BootstrapReusedZeroKeeper listed) : calls.RotationHealthy captured.cache := by
  obtain ⟨rawFile, rawDirectory⟩ := observed.callbacks
  dsimp only at rawFile rawDirectory
  have file := observed.projectFile
  have directorySync := observed.projectDirectory
  rw [rawFile] at file
  rw [rawDirectory] at directorySync
  have present : before.image.successor ≠ .absent := by
    have seen := observed.readEmpty.2.1
    intro absent
    simp [WalSegmentRotation.State.observeSuccessor, absent] at seen
  have schedule : WalSegmentRotation.steps before.image.observeSuccessor.isSome =
      [.syncFile, .syncDirectory] := by
    simp [WalSegmentRotation.steps, observed.readEmpty.2.1]
  unfold BootstrapOpenCalls.RotationHealthy
  rw [schedule]
  exact HealthySteps.prepend (syncZeroFileStep present) file
    (HealthySteps.prepend (syncZeroDirectoryStep present) directorySync (HealthySteps.none _ _))

end BootstrapReusedZeroKeeper

/-- Either zero-keeper route through the file sync, before the keeper's
directory barrier has returned. -/
inductive BootstrapZeroKeeperFilePrefix (listed : BootstrapCheckedListing captured) where
  | fresh (reported : BootstrapFreshZeroKeeperPrefix listed)
  | reused (reported : BootstrapReusedZeroKeeperPrefix listed)

namespace BootstrapZeroKeeperFilePrefix

variable {listed : BootstrapCheckedListing captured}

def inodeImage : BootstrapZeroKeeperFilePrefix listed → WalInodeImage
  | .fresh reported => reported.opened
  | .reused reported => reported.files

def state : BootstrapZeroKeeperFilePrefix listed → WalSegmentRotation.State
  | .fresh _ => ⟨before.image.metadata, .fileSynced⟩
  | .reused reported => reported.fileSyncedState

def view : BootstrapZeroKeeperFilePrefix listed → DirectoryReadNamespace
  | .fresh reported => reported.namespaceView
  | .reused _ => captured.view

def child : BootstrapZeroKeeperFilePrefix listed → DeviceInode
  | .fresh reported => reported.child.child
  | .reused reported => reported.statChild.child

def keeperSlot : BootstrapZeroKeeperFilePrefix listed → DescriptorSlot
  | .fresh reported => reported.slot
  | .reused reported => reported.slot

def inventory : BootstrapZeroKeeperFilePrefix listed → DescriptorInventory
  | .fresh reported =>
    ((listed.scan.afterClose.afterDrops reported.beforeCreate).insert reported.slot reported.free).afterDrops
      (reported.beforeFile ++ reported.afterFile)
  | .reused reported =>
    ((listed.scan.afterClose.afterDrops reported.beforeOpen).insert reported.slot reported.free).afterDrops
      (reported.beforeFile ++ reported.afterFile)

def openRead : BootstrapZeroKeeperFilePrefix listed → FilePath → EStateM IO.Error Files Handle
  | .fresh reported => reported.openRead
  | .reused reported => reported.openRead

def fsync : BootstrapZeroKeeperFilePrefix listed → Handle → EStateM IO.Error Files Unit
  | .fresh reported => reported.fsync
  | .reused reported => reported.fsync

def grouped (route : BootstrapZeroKeeperFilePrefix listed) : Array FilePath → EStateM IO.Error (Cache Handle × Files) Unit :=
  SyncPathGroup.run (sync directory.path route.openRead route.fsync)

def synced (route : BootstrapZeroKeeperFilePrefix listed) : WalInodeImage :=
  route.inodeImage.completeFileSync route.inodeImage.active

end BootstrapZeroKeeperFilePrefix

/-- The admitted markerless installer consumes the same successful
segment contract for exclusive creation or checked reuse. -/
inductive BootstrapZeroKeeperRoute (listed : BootstrapCheckedListing captured) where
  | fresh (observed : BootstrapFreshZeroKeeper listed)
  | reused (observed : BootstrapReusedZeroKeeper listed)

namespace BootstrapZeroKeeperRoute

variable {listed : BootstrapCheckedListing captured}

def filePrefix : BootstrapZeroKeeperRoute listed → BootstrapZeroKeeperFilePrefix listed
  | .fresh observed => .fresh observed.toBootstrapFreshZeroKeeperPrefix
  | .reused observed => .reused observed.toBootstrapReusedZeroKeeperPrefix

def keeperImage (route : BootstrapZeroKeeperRoute listed) : WalInodeImage := route.filePrefix.inodeImage

def fileSyncedState (route : BootstrapZeroKeeperRoute listed) : WalSegmentRotation.State := route.filePrefix.state

def groupedSync (route : BootstrapZeroKeeperRoute listed) :
    Array FilePath → EStateM IO.Error (Cache Handle × Files) Unit := route.filePrefix.grouped

/-- Either segment route reaches marker publication with this exact
settled file state and the original cache holding the directory. -/
theorem reachesMarker (route : BootstrapZeroKeeperRoute listed) :
    let image := route.keeperImage
    let fileSynced := image.completeFileSync image.active
    route.groupedSync #[directory.path] (captured.cache, route.fileSyncedState, fileSynced) =
      .ok () (captured.cache, ⟨before.image.metadata.syncDirectory, .durable⟩, fileSynced.settleBinding) := by
  cases route with
  | fresh observed => exact observed.callbacks.2.2
  | reused observed => exact observed.callbacks.2

/-- Both reports settle the exact selected inode and its empty payload. -/
theorem settledEmpty (route : BootstrapZeroKeeperRoute listed) :
    let image := route.keeperImage
    let settled := (image.completeFileSync image.active).settleBinding
    settled.crashBindings = [image.active] ∧ settled.crashBytes image.active = [ByteArray.empty] := by
  apply syncedZeroKeeperBytes
  cases route with
  | fresh observed => exact observed.empty
  | reused observed => exact observed.readEmpty.2.2

theorem rotationHealthy (route : BootstrapZeroKeeperRoute listed) : calls.RotationHealthy captured.cache :=
  match route with
  | .fresh observed => observed.rotationHealthy
  | .reused observed => observed.rotationHealthy

/-- Once either observed segment path has settled, the marker effects
complete the same admitted empty-writer installation. -/
theorem installs {input : FilePath} (route : BootstrapZeroKeeperRoute listed)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (marker : calls.MarkerHealthy captured.cache) (allowCollection : Bool) :
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      calls.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer :=
  (SegmentedBatchDatabaseTrace.fromBootstrapWithCapturedCache captured listed admission valid
    route.rotationHealthy marker allowCollection).2.2.2

end BootstrapZeroKeeperRoute

abbrev BootstrapFreshZeroKeeper.installs {listed : BootstrapCheckedListing captured} {input : FilePath}
    (observed : BootstrapFreshZeroKeeper listed) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (marker : calls.MarkerHealthy captured.cache) (allowCollection : Bool) :=
  BootstrapZeroKeeperRoute.installs (.fresh observed) admission valid marker allowCollection

end Alvoki.Storage.DiskSession
