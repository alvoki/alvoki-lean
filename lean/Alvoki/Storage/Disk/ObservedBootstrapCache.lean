import Alvoki.Storage.Disk.DiskBootstrapAdmission
import Alvoki.Storage.Disk.DirectoryCacheCapture

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev BootstrapHandle := DescriptorInventory × DescriptorSlot × Nat

private def bootstrapHeld (before : LockedFileState WalSegmentRotation.State)
    (directory : DiskDirectory) (slot : DescriptorSlot) : LockedFileState WalSegmentRotation.State :=
  { before with owners := before.owners.set (directory.file .lock) (some slot.description) }

/-- Project the actual directory open into the markerless driver's
file-image callbacks. Its captured handle and initial census are supplied by
the observed open of the directory while the admitted lock slot is live. -/
structure BootstrapCacheOpen {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    (calls : BootstrapAdmissionCalls (Cache BootstrapHandle) directory before) where
  initial : DescriptorInventory
  cached : DescriptorSlot
  view : DirectoryReadNamespace
  root : DeviceInode
  opened : DirectoryCacheOpenReports directory initial calls.slot cached
    (bootstrapHeld before directory calls.slot) view root
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (initial.inode calls.slot.description)
  projected : calls.openFiles directory.path before.image =
    match runSyncFilesOpen (opened.opened directory.path) (initial, bootstrapHeld before directory calls.slot) with
    | .ok cache (_, reached) => .ok cache reached.image
    | .error cause (_, reached) => .error cause reached.image

namespace BootstrapCacheOpen

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapAdmissionCalls (Cache BootstrapHandle) directory before}

def reached (observed : BootstrapCacheOpen calls) : DescriptorInventory :=
  observed.initial.insert observed.cached observed.opened.free

def cache (observed : BootstrapCacheOpen calls) : Cache BootstrapHandle :=
  ⟨some (observed.reached, observed.cached, 0), none, []⟩

/-- The actual initialization returns the observed directory slot and
allocates empty active and pending references. The reached census
retains the append-open lock slot and also identifies the directory. -/
theorem captures (observed : BootstrapCacheOpen calls) :
    calls.openFiles directory.path before.image = .ok observed.cache before.image ∧
    calls.slot ∈ observed.reached.slots ∧ observed.cached ∈ observed.reached.slots ∧
    observed.cached.description ≠ calls.slot.description ∧
    observed.view.modelObject observed.root = observed.reached.inode observed.cached.description := by
  obtain ⟨returned, lock, directorySlot, fresh, object, _⟩ := observed.opened.captures
  refine ⟨?_, lock, directorySlot, fresh, object⟩
  rw [observed.projected, returned]
  rfl

end BootstrapCacheOpen

/-- The checked listing starts at the cache's reached descriptor census
and observes that directory. The reported namespace has no conflicting
bootstrap names. The prior flat-WAL and marker probes are separate. -/
structure BootstrapCheckedListing {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    (captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls) where
  lifetime : HeldDirectoryReadLifetime captured.reached calls.slot
  sameDirectorySlot : lifetime.directorySlot = captured.cached
  sameView : lifetime.namespaceView = captured.view
  sameRoot : lifetime.root = captured.root
  scan : HeldDirectoryScan lifetime
  listed : calls.list directory.path = (CheckedDirectoryReadReport.scanned scan.scan).result directory.path
  noConflict : ∀ name ∈ captured.view.names captured.root, conflictsWithBootstrap name = false

namespace BootstrapCheckedListing

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

theorem entries (listed : BootstrapCheckedListing captured) :
    let entries := listed.scan.scan.entries directory.path
    calls.list directory.path = .ok entries ∧
    entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false := by
  obtain ⟨returned, names⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    listed.scan.eof listed.scan.closed listed.scan.complete
  rw [listed.scan.sameRoot, listed.sameRoot, listed.sameView] at names
  refine ⟨listed.listed.trans returned, Array.any_eq_false'.mpr ?_⟩
  intro entry present
  exact Bool.eq_false_iff.mp (listed.noConflict entry.fileName (names.mem_iff.mp
    (List.mem_map.mpr ⟨entry, by simpa using present, rfl⟩)))

/-- The stable name under the listed root denotes the lock object of the
admitted append-open slot. -/
theorem canonicalLock (listed : BootstrapCheckedListing captured) :
    ∃ lock, captured.view.child captured.root "LOCK" = some lock ∧
      captured.bindings (directory.file .lock) = some (captured.view.modelObject lock) := by
  have binding := listed.lifetime.lockEntry
  rw [listed.sameView, listed.sameRoot] at binding
  refine ⟨listed.lifetime.lock, binding, ?_⟩
  rw [← listed.sameView, listed.lifetime.identifiesLock]
  exact captured.lockObject

theorem retained (listed : BootstrapCheckedListing captured) :
    calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
    listed.scan.afterClose.references listed.scan.stream.description = [] := by
  have custody := listed.scan.custody
  exact ⟨custody.lockRetained, listed.sameDirectorySlot ▸ custody.cacheRetained, custody.streamClosed⟩

/-- Construct the existing markerless proof packet from raw callbacks and
the reached cache and listing results, without separate initialized cache
and admitted listing equalities. -/
def toOpenReports (listed : BootstrapCheckedListing captured)
    (rotation : calls.RotationHealthy captured.cache) (marker : calls.MarkerHealthy captured.cache) :
    BootstrapOpenReports (Cache BootstrapHandle) directory before where
  toBootstrapOpenCalls := calls
  descriptors := captured.reached
  live := captured.captures.2.1
  bindings := captured.bindings
  lockObject := captured.lockObject
  cache := captured.cache
  initialized := captured.captures.1
  entries := listed.scan.scan.entries directory.path
  listed := listed.entries.1
  clear := listed.entries.2
  rotation := rotation
  marker := marker

end BootstrapCheckedListing

/-- The admitted markerless path uses the directory cache and checked
listing derived from the same open and descriptor census. Reported zero
segment and marker publication effects then install the empty writer. -/
theorem SegmentedBatchDatabaseTrace.fromBootstrapWithCapturedCache
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    (captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls) (listed : BootstrapCheckedListing captured)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (rotation : calls.RotationHealthy captured.cache) (marker : calls.MarkerHealthy captured.cache)
    (allowCollection : Bool) :
    let observed := listed.toOpenReports rotation marker
    calls.openFiles directory.path before.image = .ok captured.cache before.image ∧
    calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      observed.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer := by
  intro observed
  obtain ⟨after, bootstrap, ran, _, _, _, _, _, ready, trace⟩ :=
    SegmentedBatchDatabaseTrace.fromObservedBootstrap observed admission valid allowCollection
  exact ⟨captured.captures.1, listed.retained.1, listed.retained.2.1, after, bootstrap, ran, ready, trace⟩

end Alvoki.Storage.DiskSession
