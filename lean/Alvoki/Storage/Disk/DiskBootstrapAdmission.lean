import Alvoki.Storage.Disk.DiskOpenAdmission
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Project a no-follow metadata report through the same ENOENT handling
used for the locked dispatcher and bootstrap staging probe. -/
private def bootstrapMetadata (lookup : FilePath → Except IO.Error IO.FS.Metadata) (path : FilePath) :
    Except IO.Error (Option IO.FS.Metadata) :=
  optionalMetadataWith (.ok (lookup path))

/-- Reached native observations for an admitted markerless open. The
successful lock belongs to the live slot returned by append-open, and its
object is still bound at the canonical lock path. The reached directory
cache supplies the create, write and sync callbacks used by bootstrap. -/
structure BootstrapOpenReports (files : Type) (directory : DiskDirectory)
    (before : LockedFileState WalSegmentRotation.State) where
  descriptors : DescriptorInventory
  slot : DescriptorSlot
  live : slot ∈ descriptors.slots
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description)
  flock : DescriptorSlot → Except IO.Error Bool
  acquired : flock slot = .ok true
  acquisition : TryLockObserves before.owners directory (flock slot)
  nextRef : Nat
  unlock : UnlockReport
  openFiles : FilePath → EStateM IO.Error WalSegmentRotation.State files
  cache : files
  initialized : openFiles directory.path before.image = .ok cache before.image
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  flatAbsent : ∃ name message, lookup (directory.file .wal) = .error (.noFileOrDirectory name 2 message)
  markerAbsent : before.image.metadata.active.walBoundary = none ∧
    ∃ name message, lookup (directory.file .walBoundary) = .error (.noFileOrDirectory name 2 message)
  marked : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  entries : Array IO.FS.DirEntry
  listed : list directory.path = .ok entries
  clear : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false
  readEmpty : FilePath → Except IO.Error (Option ByteArray)
  zeroRead : readEmpty (directory.file (.walSegment 0)) = .ok before.image.observeSuccessor
  stage : Option IO.FS.Metadata
  staged : bootstrapMetadata lookup (directory.file .stagedWalBoundary) = .ok stage ∧
    stage.isSome = (before.image.metadata.staged .walBoundary).isSome
  allowed : ∀ metadata, stage = some metadata → metadata.type = .file ∧ before.image.observeSuccessor.isSome = true
  createEmpty : files → FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  write : files → FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit
  sync : files → Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  rotation : ∀ done step todo prior next, WalSegmentRotation.steps before.image.observeSuccessor.isSome = done ++ step :: todo →
    before.image.execute done = some prior → prior.step step = some next →
    WalSegmentRotation.performPaths directory 0 (createEmpty cache) (fun path => sync cache #[path]) step prior = .ok () next
  marker : ∀ done step todo prior next, Publication.steps = done ++ step :: todo →
    let settled : WalSegmentRotation.State := ⟨before.image.metadata.syncDirectory, .durable⟩
    done.foldlM bootstrapMarkerStep settled = some prior → bootstrapMarkerStep prior step = some next →
    Publication.performReplacement (write cache · (WAL.Boundary.encode 0)) (sync cache) renameFile
      (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[] step prior = .ok () next

namespace BootstrapOpenReports

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}

private def bootstrapAt (observed : BootstrapOpenReports files directory before) (resolved : DiskDirectory)
    (cache : files) : EStateM IO.Error WalSegmentRotation.State Reopened :=
  bootstrapSegmentedWith resolved (fun path => liftExcept (observed.list path))
    (fun path => liftExcept (observed.readEmpty path)) (fun path => liftExcept (bootstrapMetadata observed.lookup path))
    (observed.createEmpty cache) (observed.write cache) (observed.sync cache) observed.renameFile

private def recoverAt (observed : BootstrapOpenReports files directory before) (resolved : DiskDirectory) :
    EStateM IO.Error WalSegmentRotation.State Reopened := do
  let cache ← observed.openFiles resolved.path
  recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (pure (observed.lookup (resolved.file .wal)))))
    (optionalMetadataWith (pure (observed.lookup (resolved.file .walBoundary))))
    (observed.marked resolved cache) (observed.bootstrapAt resolved cache)

private def runAt (observed : BootstrapOpenReports files directory before) (resolved : DiskDirectory)
    (slot : DescriptorSlot) : EStateM IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  runOpenWithInstallation resolved slot.description observed.nextRef (observed.flock slot) observed.unlock
    (observed.recoverAt resolved)

def run {input : FilePath} (observed : BootstrapOpenReports files directory before)
    (admission : OpenAdmissionReports input directory observed.slot) :
    EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
    (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path)) observed.runAt before

end BootstrapOpenReports

/-- An admitted markerless execution installs the exact empty writer after
its zero segment and marker are durable. It starts the mixed trace under
the returned description. The starting image carries bootstrap validity,
including all admissible survivors of an earlier interrupted bootstrap. -/
theorem SegmentedBatchDatabaseTrace.fromObservedBootstrap {files : Type} {input : FilePath}
    {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    (observed : BootstrapOpenReports files directory before)
    (admission : OpenAdmissionReports input directory observed.slot) (valid : BootstrapValid before.image)
    (allowCollection : Bool) :
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      observed.run admission = .ok ⟨directory, observed.slot.description, .ready writer.installed,
        observed.nextRef, observed.nextRef + 1⟩ after ∧
      observed.slot ∈ observed.descriptors.slots ∧
      observed.bindings (directory.file .lock) = some (observed.descriptors.inode observed.slot.description) ∧
      before.image.metadata.active.walBoundary = none ∧ before.owners (directory.file .lock) = none ∧
      after.owners = before.owners.set (directory.file .lock) (some observed.slot.description) ∧
      writer.RetainedReady directory observed.slot.description ∧
      SegmentedBatchDatabaseTrace directory observed.slot.description writer allowCollection [] observed.slot.description writer := by
  have acquisition : TryLockObserves before.owners directory (.ok true) := by
    simpa only [observed.acquired] using observed.acquisition
  obtain ⟨flatName, flatMessage, flat⟩ := observed.flatAbsent
  obtain ⟨visibleAbsent, markerName, markerMessage, marker⟩ := observed.markerAbsent
  have branch := runOpenWithInstallation_markerlessBranch directory observed.slot.description observed.nextRef before
    observed.unlock (observed.openFiles directory.path) (fun path => pure (observed.lookup path))
    (observed.marked directory) (observed.bootstrapAt directory) observed.cache observed.initialized
    flatName flatMessage markerName markerMessage (by simp [flat, Pure.pure, EStateM.pure])
    (by simp [marker, Pure.pure, EStateM.pure])
  obtain ⟨after, bootstrap, returned, vacant, held, ready, _⟩ :=
    SegmentedDatabaseTrace.fromHealthyBootstrap directory observed.slot.description observed.nextRef before valid
      acquisition observed.unlock observed.list observed.readEmpty (bootstrapMetadata observed.lookup)
      observed.listed observed.clear observed.zeroRead observed.staged.1 observed.allowed
      (observed.createEmpty observed.cache) (observed.write observed.cache) (observed.sync observed.cache)
      observed.renameFile allowCollection observed.rotation observed.marker
  refine ⟨after, bootstrap, ?_, observed.live, observed.lockObject, visibleAbsent, vacant, held, ready, .start⟩
  rw [BootstrapOpenReports.run, admission.admits, BootstrapOpenReports.runAt, observed.acquired,
    BootstrapOpenReports.recoverAt, branch]
  exact returned

end Alvoki.Storage.DiskSession
