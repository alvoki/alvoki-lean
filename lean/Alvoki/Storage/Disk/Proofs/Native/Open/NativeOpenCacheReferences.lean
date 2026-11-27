import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenClose
import Alvoki.Storage.Disk.Proofs.Recovery.DirectoryCacheCapture

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

structure OpenSyncCacheCallbacks (heap : Type) where
  openDirectory : FilePath → EStateM IO.Error heap IO.FS.Handle
  newRef : {α : Type} → α → EStateM IO.Error heap (IO.Ref α)

variable {heap image : Type} {directory : DiskDirectory} {initial : DescriptorInventory}
  {owner cached : DescriptorSlot} {files : LockedFileState image} {namespaceView : DirectoryReadNamespace}
  {root : DeviceInode}

/-- The read-only directory allocation supplies the same raw handle
stored by the consecutive directory, active and pending allocations.
The contents and external projection at each reached heap are reported. -/
structure OpenSyncCacheAllocations
    (opened : DirectoryCacheOpenReports directory initial owner cached files namespaceView root)
    (view : OpenCloseHeapView heap image) (calls : OpenSyncCacheCallbacks heap) (entry : heap) where
  handle : IO.FS.Handle
  directoryRef : IO.Ref (Option IO.FS.Handle)
  activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))
  pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))
  afterOpen : heap
  afterDirectory : heap
  afterActive : heap
  afterPending : heap
  entryFiles : view.files entry = files
  entrySlots : view.descriptors entry = initial
  rawOpened : calls.openDirectory directory.path entry = .ok handle afterOpen
  openedFiles : view.files afterOpen = files
  openedSlots : view.descriptors afterOpen = initial.insert cached opened.free
  openedHandle : view.handle afterOpen handle = (initial.insert cached opened.free, cached, 0)
  directoryAllocated : calls.newRef (some handle) afterOpen = .ok directoryRef afterDirectory
  directorySet : view.directory afterDirectory directoryRef = some handle
  directoryFiles : view.files afterDirectory = view.files afterOpen
  directorySlots : view.descriptors afterDirectory = view.descriptors afterOpen
  activeAllocated : calls.newRef none afterDirectory = .ok activeRef afterActive
  activeSet : view.active afterActive activeRef = none
  activeFiles : view.files afterActive = view.files afterDirectory
  activeSlots : view.descriptors afterActive = view.descriptors afterDirectory
  pendingAllocated : calls.newRef [] afterActive = .ok pendingRef afterPending
  pendingSet : view.pending afterPending pendingRef = []
  directoryKept : view.directory afterPending directoryRef = view.directory afterDirectory directoryRef
  activeKept : view.active afterPending activeRef = view.active afterActive activeRef
  pendingFiles : view.files afterPending = view.files afterActive
  pendingSlots : view.descriptors afterPending = view.descriptors afterActive
  sameHandle : view.handle afterPending handle = view.handle afterOpen handle

namespace OpenSyncCacheAllocations

variable {opened : DirectoryCacheOpenReports directory initial owner cached files namespaceView root}
  {view : OpenCloseHeapView heap image} {calls : OpenSyncCacheCallbacks heap} {entry : heap}

/-- Follow the actual cache initializer at the four reached primitive
returns, using one observed directory slot and the same raw references
in the resulting synchronization record. -/
theorem installs (seen : OpenSyncCacheAllocations opened view calls entry) :
    ∃ (action : IO DiskTable.OpenSyncFiles)
      (assemble : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path action ∧
      action = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) assemble ∧
      openSyncFilesWith (calls.openDirectory directory.path) calls.newRef calls.newRef calls.newRef assemble entry =
        .ok cache seen.afterPending ∧
      cache.UsesCacheReferences seen.activeRef seen.pendingRef seen.directoryRef ∧
      cache.AtDirectory directory.path ∧
      view.directory seen.afterPending seen.directoryRef = some seen.handle ∧
      view.active seen.afterPending seen.activeRef = none ∧ view.pending seen.afterPending seen.pendingRef = [] ∧
      view.cacheAt seen.afterPending seen.directoryRef seen.activeRef seen.pendingRef =
        ⟨some (initial.insert cached opened.free, cached, 0), none, []⟩ ∧
      view.files seen.afterPending = files ∧ view.descriptors seen.afterPending = initial.insert cached opened.free ∧
      runSyncFilesOpen (opened.opened directory.path) (initial, files) =
        .ok (view.cacheAt seen.afterPending seen.directoryRef seen.activeRef seen.pendingRef)
          (view.descriptors seen.afterPending, view.files seen.afterPending) ∧
      owner ∈ (view.descriptors seen.afterPending).slots ∧ cached ∈ (view.descriptors seen.afterPending).slots ∧
      namespaceView.modelObject root = (view.descriptors seen.afterPending).inode cached.description := by
  obtain ⟨action, assemble, starts, source, references⟩ := DiskTable.openSyncCacheReferences directory.path
  let cache := assemble seen.directoryRef seen.activeRef seen.pendingRef
  have directoryHandle := seen.directoryKept.trans seen.directorySet
  have activeEmpty := seen.activeKept.trans seen.activeSet
  have filesMatch := seen.pendingFiles.trans (seen.activeFiles.trans (seen.directoryFiles.trans seen.openedFiles))
  have slots := seen.pendingSlots.trans (seen.activeSlots.trans (seen.directorySlots.trans seen.openedSlots))
  obtain ⟨captured, ownerLive, cachedLive, _, object, _⟩ := opened.captures
  have cacheMatch : view.cacheAt seen.afterPending seen.directoryRef seen.activeRef seen.pendingRef =
      ⟨some (initial.insert cached opened.free, cached, 0), none, []⟩ := by
    simp only [OpenCloseHeapView.cacheAt, directoryHandle, activeEmpty, seen.pendingSet, Option.map_some, Option.map_none,
      List.map_nil, seen.sameHandle, seen.openedHandle]
  obtain ⟨uses, path⟩ := references seen.directoryRef seen.activeRef seen.pendingRef
  refine ⟨action, assemble, cache, starts, source, ?_, uses, path, directoryHandle, activeEmpty, seen.pendingSet,
    cacheMatch, filesMatch, slots, ?_, slots.symm ▸ ownerLive, slots.symm ▸ cachedLive, slots.symm ▸ object⟩
  · simp only [openSyncFilesWith, Bind.bind, EStateM.bind, seen.rawOpened, seen.directoryAllocated,
      seen.activeAllocated, seen.pendingAllocated, Pure.pure, EStateM.pure, cache]
  · rw [cacheMatch, slots, filesMatch]
    exact captured

end OpenSyncCacheAllocations
end Alvoki.Storage.DiskSession
