import Alvoki.Storage.Disk.Proofs.Filesystem.LockCensusTrace
import Alvoki.Storage.Disk.Proofs.Recovery.DirectoryCacheCapture

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

abbrev OpenCensus (image : Type) := DescriptorInventory × LockedFileState image
abbrev CensusOpenState := OpenCensus FileImage
abbrev CensusDirectoryCache := Cache (DescriptorInventory × DescriptorSlot × Nat)

/-- Primitive reports for the guarded append-open, flock and directory
open. The filesystem image is the stable projection under the lock. -/
structure CensusOpenAdmissionReports {image : Type} (input : FilePath) (directory : DiskDirectory)
    (inventory : DescriptorInventory) (retry : LockedFileState image) where
  owner : DescriptorSlot
  cached : DescriptorSlot
  view : DirectoryReadNamespace
  root : DeviceInode
  free : ∀ slot ∈ inventory.slots, slot.address ≠ owner.address
  fresh : inventory.references owner.description = []
  realPath : FilePath → EStateM IO.Error (OpenCensus image) FilePath
  lookup : FilePath → EStateM IO.Error (OpenCensus image) (Except IO.Error IO.FS.Metadata)
  openAppend : FilePath → EStateM IO.Error (OpenCensus image) DescriptorSlot
  flock : DescriptorSlot → EStateM IO.Error (OpenCensus image) Bool
  unlock : DescriptorSlot → Unit → EStateM IO.Error (OpenCensus image) Unit
  resolved : realPath input (inventory, retry) = .ok directory.path (inventory, retry)
  flat : optionalMetadataWith (lookup (directory.file .wal)) (inventory, retry) = .ok none (inventory, retry)
  lockMetadata : Option IO.FS.Metadata
  probed : optionalMetadataWith (lookup (directory.file .lock)) (inventory, retry) = .ok lockMetadata (inventory, retry)
  safe : ∀ metadata, lockMetadata = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true
  appended : openAppend (directory.file .lock) (inventory, retry) = .ok owner (inventory.insert owner free, retry)
  acquired : flock owner (inventory.insert owner free, retry) =
    .ok true (inventory.insert owner free, ⟨retry.image, retry.owners.set (directory.file .lock) (some owner.description)⟩)
  opened : DirectoryCacheOpenReports directory (inventory.insert owner free) owner cached
    ⟨retry.image, retry.owners.set (directory.file .lock) (some owner.description)⟩ view root

namespace CensusOpenAdmissionReports

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {image : Type} {retry : LockedFileState image}

def reached (report : CensusOpenAdmissionReports input directory inventory retry) : DescriptorInventory :=
  (inventory.insert report.owner report.free).insert report.cached report.opened.free

def held (report : CensusOpenAdmissionReports input directory inventory retry) : LockedFileState image :=
  ⟨retry.image, retry.owners.set (directory.file .lock) (some report.owner.description)⟩

def cache (report : CensusOpenAdmissionReports input directory inventory retry) : CensusDirectoryCache :=
  ⟨some (report.reached, report.cached, 0), none, []⟩

def run {result : Type} (report : CensusOpenAdmissionReports input directory inventory retry)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error (OpenCensus image) result) :
    EStateM.Result IO.Error (OpenCensus image) result :=
  DiskTable.withOpenAdmission input report.realPath report.lookup report.openAppend (fun path slot =>
    openWithLock (report.flock slot) (fun _ => IO.userError s!"database already open: {path.path}")
      (report.unlock slot) fun _ => do
        let files ← runSyncFilesOpen (report.opened.opened path.path)
        recover path slot files) (inventory, retry)

theorem run_reachesRecovery {result : Type} (report : CensusOpenAdmissionReports input directory inventory retry)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error (OpenCensus image) result) :
    report.run recover =
      (tryCatchThe IO.Error (recover directory report.owner report.cache) fun cause => do
        report.unlock report.owner ()
        throw cause) (report.reached, report.held) := by
  have captured := report.opened.captures
  unfold run
  rw [DiskTable.withOpenAdmission_lockOpen report.realPath report.lookup report.openAppend _
    report.resolved report.flat report.probed report.safe, report.appended]
  simp only [openWithLock, Bind.bind, EStateM.bind, report.acquired, ↓reduceIte,
    MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, captured.1]
  rfl

end CensusOpenAdmissionReports

/-- The native admission schedule carries the census reached by the earlier
owner into the held recovery callback. The two fresh descriptions leave
the retired lock description empty and the drop steps extend the earlier
retry prefix. The continuation retains the native unlock-on-error handler. -/
theorem LockCensusTrace.capturesAfterAdmission {result : Type} {directory : DiskDirectory}
    {description keeper : Nat} {initial inventory : DescriptorInventory}
    {origin source retry : LockedFileState FileImage}
    (trace : LockCensusTrace directory description initial source inventory retry)
    (earlier : ReportedReopenPrefix directory keeper origin source)
    (last : inventory.references description = [])
    {input : FilePath} (admission : CensusOpenAdmissionReports input directory inventory retry)
    (distinct : admission.owner.description ≠ description)
    (distinctCached : admission.cached.description ≠ description)
    (lockObject : inventory.inode admission.owner.description = initial.inode description)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error CensusOpenState result) :
    ReportedReopenPrefix directory keeper origin retry ∧
    TryLockObserves retry.owners directory (.ok true) ∧
    admission.reached.references admission.owner.description = [admission.owner.reference] ∧
    admission.owner.description ≠ description ∧
    admission.reached.references description = [] ∧
    admission.reached.inode admission.owner.description = initial.inode description ∧
    admission.view.modelObject admission.root = admission.reached.inode admission.cached.description ∧
    admission.run recover =
      (tryCatchThe IO.Error (recover directory admission.owner admission.cache) fun cause => do
        admission.unlock admission.owner ()
        throw cause) (admission.reached, admission.held) := by
  obtain ⟨_, _, _, separate, object, _⟩ := admission.opened.captures
  refine ⟨trace.reopenTrace earlier, trace.freshFlockAllowed.mpr last, ?_, distinct, ?_, lockObject, object,
    admission.run_reachesRecovery recover⟩
  · unfold CensusOpenAdmissionReports.reached
    rw [DescriptorInventory.references_insert, ite_eq_right separate,
      DescriptorInventory.references_insert, ite_eq_left rfl, admission.fresh]
  · unfold CensusOpenAdmissionReports.reached
    rw [DescriptorInventory.references_insert, ite_eq_right distinctCached,
      DescriptorInventory.references_insert, ite_eq_right distinct, last]

end Alvoki.Storage.DiskSession
