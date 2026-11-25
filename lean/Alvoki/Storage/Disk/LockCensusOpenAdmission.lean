import Alvoki.Storage.Disk.LockCensusTrace
import Alvoki.Storage.Disk.DirectoryCacheCapture

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Interpret the common native admission and flock schedule on the census
reached by the earlier owner. A successful append-open inserts its slot and
the reported successful flock changes that slot's ownership. The directory
open consumes precisely that state. Both allocations use descriptions
distinct from the retired lock description. The drop steps extend the
earlier retry prefix. Recovery receives the resulting cache and census,
with the native unlock-on-error handler still in place. The
primitive reports supply successful allocations and the outcome of flock on
the cooperating opener's stable canonical lock object. -/
theorem LockCensusTrace.capturesAfterAdmission {result : Type} {directory : DiskDirectory}
    {description keeper : Nat} {initial inventory : DescriptorInventory}
    {origin source retry : LockedFileState FileImage}
    (trace : LockCensusTrace directory description initial source inventory retry)
    (earlier : ReportedReopenPrefix directory keeper origin source)
    (last : inventory.references description = [])
    {input : FilePath} {owner cached : DescriptorSlot} {view : DirectoryReadNamespace} {root : DeviceInode}
    (free : ∀ slot ∈ inventory.slots, slot.address ≠ owner.address)
    (fresh : inventory.references owner.description = [])
    (distinct : owner.description ≠ description)
    (distinctCached : cached.description ≠ description)
    (lockObject : inventory.inode owner.description = initial.inode description)
    (realPath : FilePath → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage) FilePath)
    (lookup : FilePath → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage)
      (Except IO.Error IO.FS.Metadata))
    (openAppend : FilePath → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage) DescriptorSlot)
    (flock : DescriptorSlot → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage) Bool)
    (unlock : DescriptorSlot → Unit → EStateM IO.Error (DescriptorInventory × LockedFileState FileImage) Unit)
    (recover : DiskDirectory → DescriptorSlot → Cache (DescriptorInventory × DescriptorSlot × Nat) →
      EStateM IO.Error (DescriptorInventory × LockedFileState FileImage) result)
    (resolved : realPath input (inventory, retry) = .ok directory.path (inventory, retry))
    (flat : optionalMetadataWith (lookup (directory.file .wal)) (inventory, retry) = .ok none (inventory, retry))
    {lock : Option IO.FS.Metadata}
    (probed : optionalMetadataWith (lookup (directory.file .lock)) (inventory, retry) = .ok lock (inventory, retry))
    (safe : ∀ metadata, lock = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true)
    (appended : openAppend (directory.file .lock) (inventory, retry) = .ok owner (inventory.insert owner free, retry))
    (acquired : flock owner (inventory.insert owner free, retry) =
      .ok true (inventory.insert owner free, ⟨retry.image, retry.owners.set (directory.file .lock) (some owner.description)⟩))
    (opened : DirectoryCacheOpenReports directory (inventory.insert owner free) owner cached
      ⟨retry.image, retry.owners.set (directory.file .lock) (some owner.description)⟩ view root) :
    let reached := (inventory.insert owner free).insert cached opened.free
    let held : LockedFileState FileImage :=
      ⟨retry.image, retry.owners.set (directory.file .lock) (some owner.description)⟩
    let cache : Cache (DescriptorInventory × DescriptorSlot × Nat) := ⟨some (reached, cached, 0), none, []⟩
    ReportedReopenPrefix directory keeper origin retry ∧
    TryLockObserves retry.owners directory (.ok true) ∧
    reached.references owner.description = [owner.reference] ∧
    owner.description ≠ description ∧
    reached.references description = [] ∧
    reached.inode owner.description = initial.inode description ∧
    view.modelObject root = reached.inode cached.description ∧
    DiskTable.withOpenAdmission input realPath lookup openAppend (fun path slot =>
      openWithLock (flock slot) (fun _ => IO.userError s!"database already open: {path.path}") (unlock slot) fun _ => do
        let files ← runSyncFilesOpen (opened.opened path.path)
        recover path slot files) (inventory, retry) =
      (tryCatchThe IO.Error (recover directory owner cache) fun cause => do
        unlock owner ()
        throw cause) (reached, held) := by
  intro reached held cache
  obtain ⟨captured, _, _, separate, object, _⟩ := opened.captures
  refine ⟨trace.reopenTrace earlier, trace.freshFlockAllowed.mpr last, ?_, distinct, ?_, lockObject, object, ?_⟩
  · change ((inventory.insert owner free).insert cached opened.free).references owner.description = _
    rw [DescriptorInventory.references_insert, ite_eq_right separate,
      DescriptorInventory.references_insert, ite_eq_left rfl, fresh]
  · change ((inventory.insert owner free).insert cached opened.free).references description = []
    rw [DescriptorInventory.references_insert, ite_eq_right distinctCached,
      DescriptorInventory.references_insert, ite_eq_right distinct, last]
  · rw [DiskTable.withOpenAdmission_lockOpen realPath lookup openAppend _ resolved flat probed safe, appended]
    simp only [openWithLock, Bind.bind, EStateM.bind, acquired, ↓reduceIte,
      MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, captured]
    rfl

end Alvoki.Storage.DiskSession
