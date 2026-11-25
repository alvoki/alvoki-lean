import Alvoki.Storage.Disk.ObservedRotationSchedule
import Alvoki.Storage.Disk.RotationSuccessorFsyncStop

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev Files := DescriptorInventory × RotationCreateFiles
private abbrev Handle := RotationSuccessorHandle

private abbrev successorName (before : SegmentedWriterState) :=
  renderWalSegmentName (before.installed.walBytes / WAL.frameSize)

/-- The no-follow metadata guard and the fallback read open resolve the same
child of the held directory. The open is issued by the file sync's cache
miss. The metadata guard itself neither opens the file nor writes the cache. -/
structure RotationExistingSuccessorOpen (directory : DiskDirectory) (before : SegmentedWriterState) where
  inventory : DescriptorInventory
  files : RotationCreateFiles
  owner : DescriptorSlot
  held : before.owners.Owns directory owner.description
  ownerLive : owner ∈ inventory.slots
  root : DeviceInode
  lock : RunChildLookup root "LOCK" files.view
  lockObject : files.view.modelObject lock.child = inventory.inode owner.description
  cache : Cache Handle
  pendingMiss : cache.pending.find? (fun entry => entry.1 == rotationSuccessorPath directory before) = none
  activeMiss : ∀ active ∈ cache.active, active.1 ≠ rotationSuccessorPath directory before
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  nonempty : before.installed.activeFirst < before.installed.walBytes / WAL.frameSize
  checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache Handle × Files))
    directory before.installed (fun path => liftExcept (lookup path)) (cache, inventory, files) =
    .ok () (cache, inventory, files)
  probe : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  metadata : IO.FS.Metadata
  statChild : RunChildLookup root (successorName before) files.view
  stat : probe (rotationSuccessorPath directory before) = .ok (metadata, statChild.child)
  regular : metadata.type = .file
  singleLink : metadata.numLinks = 1
  size : metadata.byteSize = 0
  extent : metadata.byteSize.toNat = (files.inodes.visible (files.view.modelObject statChild.child)).size
  openedChild : RunChildLookup root (successorName before) files.view
  slot : DescriptorSlot
  free : ∀ other ∈ inventory.slots, other.address ≠ slot.address
  fresh : inventory.references slot.description = []
  sameProcess : slot.reference.process = owner.reference.process
  object : files.view.modelObject openedChild.child = inventory.inode slot.description
  beforeSync : List LockReferenceDrop
  slotLive : slot ∈ ((inventory.insert slot free).afterDrops beforeSync).slots
  ownerAtSync : owner ∈ ((inventory.insert slot free).afterDrops beforeSync).slots
  openRead : FilePath → EStateM IO.Error Files Handle
  opened : openRead (rotationSuccessorPath directory before) (inventory, files) =
    .ok (inventory.insert slot free, slot, 0) ((inventory.insert slot free).afterDrops beforeSync, files)

namespace RotationExistingSuccessorOpen

variable {directory : DiskDirectory} {before : SegmentedWriterState}

abbrev handle (report : RotationExistingSuccessorOpen directory before) : Handle :=
  (report.inventory.insert report.slot report.free, report.slot, 0)

abbrev atSync (report : RotationExistingSuccessorOpen directory before) : Files :=
  (report.handle.1.afterDrops report.beforeSync, report.files)

def readEmpty (report : RotationExistingSuccessorOpen directory before) (path : FilePath) :
    EStateM IO.Error (Cache Handle × Files) (Option ByteArray) :=
  WalSegmentRotation.readEmptyWith (pure ((report.probe path).map Prod.fst)) path "WAL segment successor is not empty"

theorem readsEmpty (report : RotationExistingSuccessorOpen directory before) :
    report.readEmpty (rotationSuccessorPath directory before) (report.cache, report.inventory, report.files) =
      .ok (some ByteArray.empty) (report.cache, report.inventory, report.files) := by
  have regular : (report.metadata.type == .file) = true := by rw [report.regular]; rfl
  simp [readEmpty, WalSegmentRotation.readEmptyWith, optionalMetadataWith, checkPrivateRegularWith,
    report.stat, regular, report.singleLink, report.size, Except.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem resolves (report : RotationExistingSuccessorOpen directory before) :
    report.cache.resolve directory.path (rotationSuccessorPath directory before) report.openRead
      (report.inventory, report.files) = .ok report.handle (report.cache, report.atSync) := by
  have separate : (rotationSuccessorPath directory before == directory.path) = false := by
    simpa using file_ne_directory directory (.walSegment (before.installed.walBytes / WAL.frameSize))
  cases seen : report.cache.active with
  | none =>
    simp [Cache.resolve, separate, report.pendingMiss, seen, withCache, report.opened]
  | some active =>
    have other : (active.1 == rotationSuccessorPath directory before) = false := by
      simpa using report.activeMiss active (seen.symm ▸ Option.mem_some.mpr rfl)
    simp [Cache.resolve, separate, report.pendingMiss, seen, other, withCache, report.opened]

/-- The file barrier reaches the live description returned by the open.
Its inode is the private zero-length object inspected at the same path. -/
theorem custody (report : RotationExistingSuccessorOpen directory before) :
    report.openedChild.child = report.statChild.child ∧
    report.files.view.modelObject report.statChild.child = report.atSync.1.inode report.slot.description ∧
    report.slot ∈ report.atSync.1.slots ∧ report.owner ∈ report.atSync.1.slots ∧
    report.files.inodes.visible (report.atSync.1.inode report.slot.description) = ByteArray.empty := by
  have bound := report.statChild.binds
  rw [report.statChild.atRoot, report.statChild.atName] at bound
  have same := report.openedChild.child_eq bound
  have object : report.files.view.modelObject report.statChild.child = report.atSync.1.inode report.slot.description :=
    (congrArg report.files.view.modelObject same).symm.trans report.object
  have empty := report.extent.symm
  rw [report.size] at empty
  exact ⟨same, object, report.slotLive, report.ownerAtSync, object ▸ ByteArray.size_eq_zero_iff.mp empty⟩

/-- The fresh read description belongs to the process that still owns
the canonical lock. Its allocation leaves the lock description distinct. -/
theorem lockCustody (report : RotationExistingSuccessorOpen directory before) :
    before.owners.Owns directory report.owner.description ∧
    report.files.view.child report.root "LOCK" = some report.lock.child ∧
    report.files.view.modelObject report.lock.child = report.atSync.1.inode report.owner.description ∧
    report.slot.description ≠ report.owner.description ∧
    report.slot.reference.process = report.owner.reference.process := by
  have bound := report.lock.binds
  rw [report.lock.atRoot, report.lock.atName] at bound
  refine ⟨report.held, bound, report.lockObject, ?_, report.sameProcess⟩
  intro same
  have present := report.inventory.mem_references.mpr ⟨report.owner, report.ownerLive, rfl, same.symm⟩
  rw [report.fresh] at present
  exact List.not_mem_nil present

end RotationExistingSuccessorOpen

private def fileSyncReturn (after : Files) : Except IO.Error Unit → EStateM.Result IO.Error Files Unit
  | .ok value => .ok value after
  | .error cause => .error cause after

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {opened : RotationExistingSuccessorOpen directory before}

/-- Report the successor fsync and the drops through release of the
uncached read handle on either return. Only the inspected empty inode's
byte durability can change. A failed return may still have that effect. -/
structure RotationExistingSuccessorFileSync (opened : RotationExistingSuccessorOpen directory before) where
  fsync : Handle → EStateM IO.Error Files Unit
  outcome : Except IO.Error Unit
  effective : Bool
  complete : outcome = .ok () → effective = true
  afterSync : List LockReferenceDrop
  ownerRetained : opened.owner ∈ (opened.atSync.1.afterDrops (afterSync ++ [opened.slot.closeEvent])).slots
  returned : fsync opened.handle opened.atSync =
    let synced := if effective then
      opened.files.inodes.completeFileSync (opened.inventory.inode opened.slot.description)
      else opened.files.inodes
    let after := (opened.atSync.1.afterDrops (afterSync ++ [opened.slot.closeEvent]), { opened.files with inodes := synced })
    fileSyncReturn after outcome

namespace RotationExistingSuccessorFileSync

abbrev after (report : RotationExistingSuccessorFileSync opened) : Files :=
  (opened.atSync.1.afterDrops (report.afterSync ++ [opened.slot.closeEvent]), { opened.files with
    inodes := if report.effective then
      opened.files.inodes.completeFileSync (opened.inventory.inode opened.slot.description)
      else opened.files.inodes })

def group (report : RotationExistingSuccessorFileSync opened) (path : FilePath) :=
  SyncPathGroup.run (sync directory.path opened.openRead report.fsync) #[path]

/-- Neither the successful nor the failed group keeps the unretained
read description. The returned census carries the other reported drops
and still contains the original owner. -/
theorem closesReadSlot (report : RotationExistingSuccessorFileSync opened) :
    report.after.1 =
      opened.inventory.afterDrops (opened.beforeSync ++ report.afterSync ++ [opened.slot.closeEvent]) ∧
    report.after.1.references opened.slot.description = [] ∧ opened.owner ∈ report.after.1.slots := by
  have closed : report.after.1 =
      opened.inventory.afterDrops (opened.beforeSync ++ report.afterSync ++ [opened.slot.closeEvent]) := by
    change ((opened.inventory.insert opened.slot opened.free).afterDrops opened.beforeSync).afterDrops
      (report.afterSync ++ [opened.slot.closeEvent]) = _
    rw [DescriptorInventory.afterDrops_append, ← List.append_assoc]
    exact DescriptorInventory.insert_thenClose _ _ _ _
  exact ⟨closed, by rw [closed, DescriptorInventory.references_afterDrops, opened.fresh]; rfl, report.ownerRetained⟩

/-- The physical post-fsync image frames all names and the other inodes.
In the effective case, a crash on the selected inode can retain only its
empty bytes. -/
theorem effects (report : RotationExistingSuccessorFileSync opened) :
    report.after.2.view = opened.files.view ∧ report.after.2.crashNames = opened.files.crashNames ∧
    (∀ inode, inode ≠ opened.inventory.inode opened.slot.description →
      report.after.2.inodes.crashBytes inode = opened.files.inodes.crashBytes inode) ∧
    (report.effective = true → report.after.2.inodes.crashBytes (opened.inventory.inode opened.slot.description) =
      [ByteArray.empty]) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro inode distinct
    cases observed : report.effective <;>
      simp [observed, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, distinct]
  · intro effective
    have empty := opened.custody.2.2.2.2
    change opened.files.inodes.visible (opened.inventory.inode opened.slot.description) = ByteArray.empty at empty
    simp [effective, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, empty]

/-- The one-path group invokes the open and fsync once. A returned error
carries that path in its diagnostic and leaves the cache untouched. -/
theorem fileGroup (report : RotationExistingSuccessorFileSync opened) :
    report.group (rotationSuccessorPath directory before) (opened.cache, opened.inventory, opened.files) =
      match report.outcome with
      | .ok value => .ok value (opened.cache, report.after)
      | .error cause => .error (IO.userError s!"sync failed for '{rotationSuccessorPath directory before}': {cause}")
          (opened.cache, report.after) := by
  unfold group
  rw [SyncPathGroup.run_single]
  simp only [sync, opened.resolves, report.returned]
  cases report.outcome with
  | ok value =>
    cases value
    rfl
  | error cause => rfl

/-- On the checked present-successor route, an ordinary child fsync
error returns before the directory barrier and before the ready reset.
The cause, held lock, cache and effect image are those just reached. -/
theorem returnsFileError (report : RotationExistingSuccessorFileSync opened)
    (create : FilePath → EStateM IO.Error (Cache Handle × Files) Unit)
    {cause : IO.Error} (failed : report.outcome = .error cause) :
    runObservedRotation directory opened.lookup opened.readEmpty create report.group
      (.ready before.installed, ⟨(opened.cache, opened.inventory, opened.files), before.owners⟩) =
    .error (IO.userError s!"sync failed for '{rotationSuccessorPath directory before}': {cause}")
      (.poisoned, ⟨(opened.cache, report.after), before.owners⟩) := by
  have file := report.fileGroup
  rw [failed] at file
  apply runObservedRotation_publishError _ _ _ _ _ _ _ opened.nonempty opened.checked
  rw [WalSegmentRotation.runAt_fileEffects]
  simp [WalSegmentRotation.observeSuccessorWith, opened.readsEmpty, file, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

end RotationExistingSuccessorFileSync

/-- On a successful existing-successor rotation, the directory is synced
through the captured directory handle in the original cache. The effect
records settlement only for the selected successor name. -/
structure RotationExistingSuccessorDirectorySync (file : RotationExistingSuccessorFileSync opened) where
  fileSucceeded : file.outcome = .ok ()
  handle : Handle
  cached : opened.cache.directory = some handle
  pathObject : FilePath → Option DeviceInode
  bound : pathObject directory.path = some opened.root
  capturedObject : opened.files.view.modelObject opened.root = handle.1.inode handle.2.1.description
  currentObject : opened.files.view.modelObject opened.root = file.after.1.inode handle.2.1.description
  directoryLive : handle.2.1 ∈ file.after.1.slots
  drops : List LockReferenceDrop
  ownerRetained : opened.owner ∈ (file.after.1.afterDrops drops).slots
  directoryRetained : handle.2.1 ∈ (file.after.1.afterDrops drops).slots
  settled : RotationCreateFiles
  returned : file.fsync handle file.after = .ok () (file.after.1.afterDrops drops, settled)
  view : settled.view = file.after.2.view
  bytes : settled.inodes = file.after.2.inodes
  successorSurvives : settled.crashNames (successorName before) = [some opened.statChild.child]

namespace RotationExistingSuccessorDirectorySync

variable {file : RotationExistingSuccessorFileSync opened}

abbrev after (report : RotationExistingSuccessorDirectorySync file) : Files :=
  (file.after.1.afterDrops report.drops, report.settled)

/-- The grouped directory barrier uses the cached description, whose live
slot still identifies the observed root at the effect point. -/
theorem directoryGroup (report : RotationExistingSuccessorDirectorySync file) :
    file.group directory.path (opened.cache, file.after) = .ok () (opened.cache, report.after) := by
  unfold RotationExistingSuccessorFileSync.group
  rw [SyncPathGroup.run_single]
  simp [sync, Cache.resolve, report.cached, report.returned, withCache]

theorem publishes (report : RotationExistingSuccessorDirectorySync file)
    (create : FilePath → EStateM IO.Error (Cache Handle × Files) Unit) :
    WalSegmentRotation.runAt directory (before.installed.walBytes / WAL.frameSize)
      opened.readEmpty create file.group (opened.cache, opened.inventory, opened.files) =
      .ok () (opened.cache, report.after) := by
  have fileSynced := file.fileGroup
  rw [report.fileSucceeded] at fileSynced
  rw [WalSegmentRotation.runAt_fileEffects]
  simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind,
    opened.readsEmpty, fileSynced, report.directoryGroup, Pure.pure, EStateM.pure]

/-- Both barriers succeed on the existing empty successor route.
The returned writer changes its keeper offset, clears the old append
entry, and keeps the same table and lock. -/
theorem returnsRotation (report : RotationExistingSuccessorDirectorySync file)
    (create : FilePath → EStateM IO.Error (Cache Handle × Files) Unit) :
    runObservedRotation directory opened.lookup opened.readEmpty create file.group
      (.ready before.installed, ⟨(opened.cache, opened.inventory, opened.files), before.owners⟩) =
    .ok () (.ready { before.installed with activeFirst := before.installed.walBytes / WAL.frameSize },
      ⟨({ opened.cache with active := none }, report.after), before.owners⟩) := by
  exact runObservedRotationWithReset_ready directory before.installed
    ⟨(opened.cache, opened.inventory, opened.files), before.owners⟩ opened.lookup opened.readEmpty create file.group
    (fun _ files => files) opened.nonempty opened.checked (report.publishes create)

/-- The settled name and payload are for the same private empty inode that
was inspected and opened, and the lock and directory slots remain live. -/
theorem durableSuccessor (report : RotationExistingSuccessorDirectorySync file) :
    report.settled.view.child opened.root (successorName before) = some opened.statChild.child ∧
    report.settled.crashNames (successorName before) = [some opened.statChild.child] ∧
    report.settled.view.modelObject opened.statChild.child = report.after.1.inode opened.slot.description ∧
    report.settled.inodes.crashBytes (report.settled.view.modelObject opened.statChild.child) = [ByteArray.empty] ∧
    report.pathObject directory.path = some opened.root ∧
    report.handle.1.inode report.handle.2.1.description = file.after.1.inode report.handle.2.1.description ∧
    report.handle.2.1 ∈ file.after.1.slots ∧
    opened.owner ∈ report.after.1.slots ∧ report.handle.2.1 ∈ report.after.1.slots := by
  have bound := opened.statChild.binds
  rw [opened.statChild.atRoot, opened.statChild.atName] at bound
  have child := (congrArg (fun view => view.child opened.root (successorName before)) report.view).trans bound
  have object := (congrArg (fun view => view.modelObject opened.statChild.child) report.view).trans opened.custody.2.1
  refine ⟨child, report.successorSurvives, object, ?_, report.bound,
    report.capturedObject.symm.trans report.currentObject, report.directoryLive,
    report.ownerRetained, report.directoryRetained⟩
  rw [report.bytes, object]
  exact file.effects.2.2.2 (file.complete report.fileSucceeded)

end RotationExistingSuccessorDirectorySync

end Alvoki.Storage.DiskSession
