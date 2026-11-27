import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedBatchDatabaseTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Project a no-follow metadata report through the same ENOENT handling
used for the locked dispatcher and bootstrap staging probe. -/
private def bootstrapMetadata (lookup : FilePath → Except IO.Error IO.FS.Metadata) (path : FilePath) :
    Except IO.Error (Option IO.FS.Metadata) :=
  optionalMetadataWith (.ok (lookup path))

/-- Calls shared by either recovery route when starting from a bootstrap
image under the admitted lock. -/
structure BootstrapAdmissionCalls (files : Type) (directory : DiskDirectory)
    (before : LockedFileState WalSegmentRotation.State) where
  slot : DescriptorSlot
  flock : DescriptorSlot → Except IO.Error Bool
  acquired : flock slot = .ok true
  acquisition : TryLockObserves before.owners directory (flock slot)
  nextRef : Nat
  unlock : UnlockReport
  openFiles : FilePath → EStateM IO.Error WalSegmentRotation.State files
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  flatAbsent : ∃ name message, lookup (directory.file .wal) = .error (.noFileOrDirectory name 2 message)
  marked : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened

/-- Reached markerless probes and callbacks before certifying the cache,
listing, and publication results. -/
structure BootstrapOpenCalls (files : Type) (directory : DiskDirectory)
    (before : LockedFileState WalSegmentRotation.State) extends BootstrapAdmissionCalls files directory before where
  markerAbsent : before.image.metadata.active.walBoundary = none ∧
    ∃ name message, lookup (directory.file .walBoundary) = .error (.noFileOrDirectory name 2 message)
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
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

namespace BootstrapOpenCalls

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}

abbrev RotationHealthy (calls : BootstrapOpenCalls files directory before) (cache : files) : Prop :=
  ∀ done step todo prior next, WalSegmentRotation.steps before.image.observeSuccessor.isSome = done ++ step :: todo →
    before.image.execute done = some prior → prior.step step = some next →
    WalSegmentRotation.performPaths directory 0 (calls.createEmpty cache) (fun path => calls.sync cache #[path])
      step prior = .ok () next

abbrev MarkerHealthy (calls : BootstrapOpenCalls files directory before) (cache : files) : Prop :=
  ∀ done step todo prior next, Publication.steps = done ++ step :: todo →
    let settled : WalSegmentRotation.State := ⟨before.image.metadata.syncDirectory, .durable⟩
    done.foldlM bootstrapMarkerStep settled = some prior → bootstrapMarkerStep prior step = some next →
    Publication.performReplacement (calls.write cache · (WAL.Boundary.encode 0)) (calls.sync cache) calls.renameFile
      (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[] step prior = .ok () next

end BootstrapOpenCalls

/-- An admitted markerless open uses the lock returned by append-open.
Its reached directory cache supplies the create, write and sync callbacks. -/
structure BootstrapOpenReports (files : Type) (directory : DiskDirectory)
    (before : LockedFileState WalSegmentRotation.State) extends BootstrapOpenCalls files directory before where
  descriptors : DescriptorInventory
  live : slot ∈ descriptors.slots
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description)
  cache : files
  initialized : openFiles directory.path before.image = .ok cache before.image
  entries : Array IO.FS.DirEntry
  listed : list directory.path = .ok entries
  clear : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false
  rotation : toBootstrapOpenCalls.RotationHealthy cache
  marker : toBootstrapOpenCalls.MarkerHealthy cache

namespace BootstrapAdmissionCalls

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}

private def recoverAt (observed : BootstrapAdmissionCalls files directory before)
    (bootstrap : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened)
    (resolved : DiskDirectory) :
    EStateM IO.Error WalSegmentRotation.State Reopened := do
  let cache ← observed.openFiles resolved.path
  recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (pure (observed.lookup (resolved.file .wal)))))
    (optionalMetadataWith (pure (observed.lookup (resolved.file .walBoundary))))
    (observed.marked resolved cache) (bootstrap resolved cache)

private def runAt (observed : BootstrapAdmissionCalls files directory before)
    (bootstrap : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened) (resolved : DiskDirectory)
    (slot : DescriptorSlot) : EStateM IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  runOpenWithInstallation resolved slot.description observed.nextRef (observed.flock slot) observed.unlock
    (observed.recoverAt bootstrap resolved)

def run {input : FilePath} (observed : BootstrapAdmissionCalls files directory before)
    (bootstrap : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened)
    (admission : OpenAdmissionReports input directory observed.slot) :
    EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
    (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path))
    (observed.runAt bootstrap) before

/-- A reached marker probe dispatches the admitted open, retaining the
exact lock slot, initialized files and reached image. -/
theorem runSelected {input : FilePath} (calls : BootstrapAdmissionCalls files directory before)
    (bootstrap : DiskDirectory → files → EStateM IO.Error WalSegmentRotation.State Reopened)
    (admission : OpenAdmissionReports input directory calls.slot) {cache : files}
    (initialized : calls.openFiles directory.path before.image = .ok cache before.image)
    {marker : Option IO.FS.Metadata}
    (markerRead : optionalMetadataWith
      (pure (calls.lookup (directory.file .walBoundary)) : EStateM IO.Error WalSegmentRotation.State _)
      before.image = .ok marker before.image) :
    calls.run bootstrap admission = runOpenWithInstallation directory calls.slot.description calls.nextRef (.ok true)
      calls.unlock (if marker.isSome then calls.marked directory cache else bootstrap directory cache) before := by
  obtain ⟨flatName, flatMessage, flat⟩ := calls.flatAbsent
  have branch := runOpenWithInstallation_recoveryBranch directory calls.slot.description calls.nextRef before
    calls.unlock (calls.openFiles directory.path) (fun path => pure (calls.lookup path))
    (calls.marked directory) (bootstrap directory) cache initialized flatName flatMessage
    (by simp [flat, Pure.pure, EStateM.pure]) marker markerRead
  rw [run, admission.admits, runAt, calls.acquired, recoverAt, branch]

end BootstrapAdmissionCalls

namespace BootstrapOpenCalls

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}

def bootstrapAt (observed : BootstrapOpenCalls files directory before) (resolved : DiskDirectory)
    (cache : files) : EStateM IO.Error WalSegmentRotation.State Reopened :=
  bootstrapSegmentedWith resolved (fun path => liftExcept (observed.list path))
    (fun path => liftExcept (observed.readEmpty path)) (fun path => liftExcept (bootstrapMetadata observed.lookup path))
    (observed.createEmpty cache) (observed.write cache) (observed.sync cache) observed.renameFile

abbrev run {input : FilePath} (observed : BootstrapOpenCalls files directory before)
    (admission : OpenAdmissionReports input directory observed.slot) :=
  observed.toBootstrapAdmissionCalls.run observed.bootstrapAt admission

/-- The admitted calls expose the exact markerless worker, whether that
worker installs a table or stops at a reported error. -/
theorem runMarkerless {input : FilePath} (calls : BootstrapOpenCalls files directory before)
    (admission : OpenAdmissionReports input directory calls.slot) {cache : files}
    (initialized : calls.openFiles directory.path before.image = .ok cache before.image) :
    calls.run admission = runOpenWithInstallation directory calls.slot.description calls.nextRef (.ok true)
      calls.unlock (calls.bootstrapAt directory cache) before := by
  obtain ⟨_, _, _, marker⟩ := calls.markerAbsent
  exact calls.toBootstrapAdmissionCalls.runSelected calls.bootstrapAt admission initialized (marker := none)
    (by simp [optionalMetadataWith, Bind.bind, EStateM.bind, marker, Pure.pure, EStateM.pure])

/-- The reached listing, empty segment probe and staging guard authorize
the same first publication callback on the observed cache. -/
theorem reachesPublication (calls : BootstrapOpenCalls files directory before) (cache : files)
    {entries : Array IO.FS.DirEntry} (listed : calls.list directory.path = .ok entries)
    (clear : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false) :
    calls.bootstrapAt directory cache before.image =
      bootstrapEmptyWith directory before.image.observeSuccessor (calls.createEmpty cache) (calls.write cache)
        (calls.sync cache) calls.renameFile before.image := by
  have admitted := prepareBootstrapWith_admitted directory calls.list calls.readEmpty (bootstrapMetadata calls.lookup)
    listed clear calls.zeroRead calls.staged.1 calls.allowed
  unfold bootstrapAt bootstrapSegmentedWith
  rw [prepareBootstrapWith_liftReports, admitted]
  rfl

end BootstrapOpenCalls

abbrev BootstrapOpenReports.run {files : Type} {input : FilePath} {directory : DiskDirectory}
    {before : LockedFileState WalSegmentRotation.State} (observed : BootstrapOpenReports files directory before)
    (admission : OpenAdmissionReports input directory observed.slot) :=
  observed.toBootstrapOpenCalls.run admission

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
  obtain ⟨after, bootstrap, returned, vacant, held, ready, _⟩ :=
    SegmentedDatabaseTrace.fromHealthyBootstrap directory observed.slot.description observed.nextRef before valid
      acquisition observed.unlock observed.list observed.readEmpty (bootstrapMetadata observed.lookup)
      observed.listed observed.clear observed.zeroRead observed.staged.1 observed.allowed
      (observed.createEmpty observed.cache) (observed.write observed.cache) (observed.sync observed.cache)
      observed.renameFile allowCollection observed.rotation observed.marker
  refine ⟨after, bootstrap, ?_, observed.live, observed.lockObject, observed.markerAbsent.1, vacant, held, ready, .start⟩
  exact (observed.toBootstrapOpenCalls.runMarkerless admission observed.initialized).trans returned

end Alvoki.Storage.DiskSession
