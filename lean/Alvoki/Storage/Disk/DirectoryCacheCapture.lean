import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Interpret the three new references by their contents. The directory
open carries the reached descriptor census and filesystem state. -/
def runSyncFilesOpen {state handle : Type} (openDirectory : EStateM IO.Error state handle) :
    EStateM IO.Error state (Cache handle) :=
  openSyncFilesWith openDirectory pure pure pure fun directory active pending => ⟨directory, active, pending⟩

theorem runSyncFilesOpen_openError {state handle : Type} {openDirectory : EStateM IO.Error state handle}
    {before reached : state} {cause : IO.Error} (failed : openDirectory before = .error cause reached) :
    runSyncFilesOpen openDirectory before = .error cause reached := by
  simp [runSyncFilesOpen, openSyncFilesWith, Bind.bind, EStateM.bind, failed]

/-- The successful native open of the canonical directory inserts its
fresh slot with the reported object identity, alongside the held lock.
The scope is one open and reference initialization, with inode identity
and the actual slot allocation supplied by the observation. -/
structure DirectoryCacheOpenReports (directory : DiskDirectory) (initial : DescriptorInventory)
    (owner cached : DescriptorSlot) (before : LockedFileState FileImage)
    (view : DirectoryReadNamespace) (root : DeviceInode) where
  opened : FilePath → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage)
    (DescriptorInventory × DescriptorSlot × Nat)
  lockLive : owner ∈ initial.slots
  free : ∀ slot ∈ initial.slots, slot.address ≠ cached.address
  fresh : initial.references cached.description = []
  held : before.owners.Owns directory owner.description
  object : view.modelObject root = initial.inode cached.description
  returned : opened directory.path (initial, before) =
    .ok (initial.insert cached free, cached, 0) (initial.insert cached free, before)

theorem DirectoryCacheOpenReports.captures {directory initial owner cached before view root}
    (observed : DirectoryCacheOpenReports directory initial owner cached before view root) :
    let reached := initial.insert cached observed.free
    runSyncFilesOpen (observed.opened directory.path) (initial, before) =
      .ok ⟨some (reached, cached, 0), none, []⟩ (reached, before) ∧
    owner ∈ reached.slots ∧ cached ∈ reached.slots ∧ cached.description ≠ owner.description ∧
    view.modelObject root = reached.inode cached.description ∧ before.owners.Owns directory owner.description := by
  intro reached
  refine ⟨?_, List.mem_cons_of_mem _ observed.lockLive, List.mem_cons_self, ?_, observed.object, observed.held⟩
  · simp [runSyncFilesOpen, openSyncFilesWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, observed.returned, reached]
  · intro same
    have present := initial.mem_references.mpr ⟨owner, observed.lockLive, rfl, same.symm⟩
    rw [observed.fresh] at present
    exact List.not_mem_nil present

/-- The installer's file-opening callback projects the real initialization
of its synchronization cache. The same reached census supplies the inventory
of live descriptors used by the later directory listing. -/
theorem MarkedRetryChunkOperations.capturedDirectoryFromOpen {directory : DiskDirectory}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history}
    (operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout)
    {initial : DescriptorInventory} {cached : DescriptorSlot} {view : DirectoryReadNamespace} {root : DeviceInode}
    (observed : DirectoryCacheOpenReports directory initial operations.slot cached
      ⟨before.image, before.owners.set (directory.file .lock) (some operations.slot.description)⟩ view root)
    (census : operations.descriptors = initial.insert cached observed.free)
    (projected : operations.openFiles before.image =
      match runSyncFilesOpen (observed.opened directory.path)
        (initial, ⟨before.image, before.owners.set (directory.file .lock) (some operations.slot.description)⟩) with
      | .ok cache (_, reached) => .ok cache reached.image
      | .error cause (_, reached) => .error cause reached.image) :
    operations.cache = ⟨some (operations.descriptors, cached, 0), none, []⟩ ∧
      operations.slot ∈ operations.descriptors.slots ∧ cached ∈ operations.descriptors.slots ∧
      view.modelObject root = operations.descriptors.inode cached.description := by
  obtain ⟨returned, lockLive, cacheLive, _, object, _⟩ := observed.captures
  rw [returned, operations.initialized] at projected
  exact ⟨census ▸ (EStateM.Result.ok.inj projected).1, census ▸ lockLive, census ▸ cacheLive, census ▸ object⟩

end Alvoki.Storage.DiskSession
