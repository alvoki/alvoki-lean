import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev keeperName := renderWalSegmentName 0
private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"
private abbrev markerBytes := WAL.Boundary.encode 0

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

/-- The keeper barrier has settled the old live names. A failed flush can
report its exact visible stage bytes without changing those names. -/
private def scratchImage (before : WalSegmentRotation.State) (bytes : ByteArray) : WalSegmentRotation.State :=
  { metadata := { before.metadata.syncDirectory with
      staged := fun
        | .walBoundary => some (bytes, false)
        | .manifest => before.metadata.staged .manifest }
    successor := .durable }

private abbrev atStage (before : WalSegmentRotation.State) : WalSegmentRotation.State :=
  ⟨before.metadata.syncDirectory, .durable⟩

/-- The guarded stage has returned one exclusive description and the
write succeeded. The raw flush error is followed by dropping that
unretained handle. The byte prefix and physical lookup describe the
regular, single-link staging inode after the reported finalizer effects. -/
structure BootstrapMarkerFlushError (keeper : BootstrapZeroKeeperRoute listed) where
  tryCreate : FilePath → EStateM IO.Error Files (Except IO.Error Handle)
  statStale : FilePath → EStateM IO.Error Files (Except IO.Error IO.FS.Metadata)
  unlinkStale : FilePath → EStateM IO.Error Files (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error Files Handle
  write : Handle → ByteArray → EStateM IO.Error Files Unit
  flush : Handle → EStateM IO.Error Files Unit
  drop : Handle → EStateM IO.Error Files Unit
  between : List LockReferenceDrop
  slot : DescriptorSlot
  free : ∀ old ∈ (keeper.settledInventory.afterDrops between).slots, old.address ≠ slot.address
  fresh : (keeper.settledInventory.afterDrops between).references slot.description = []
  lockAtOpen : calls.slot ∈ (keeper.settledInventory.afterDrops between).slots
  directoryAtOpen : captured.cached ∈ (keeper.settledInventory.afterDrops between).slots
  afterOpen : Files
  opening : BootstrapMarkerStageOpen tryCreate (removeStaleStagingWith statStale unlinkStale) create
    (directory.file .stagedWalBoundary) (atStage before.image, keeper.settledImage)
    ((keeper.settledInventory.afterDrops between).insert slot free, slot, 0) afterOpen
  afterWrite : Files
  wrote : write ((keeper.settledInventory.afterDrops between).insert slot free, slot, 0)
    markerBytes afterOpen = .ok () afterWrite
  beforeFlush : List LockReferenceDrop
  fileLive : slot ∈ (((keeper.settledInventory.afterDrops between).insert slot free).afterDrops beforeFlush).slots
  lockLive : calls.slot ∈ (((keeper.settledInventory.afterDrops between).insert slot free).afterDrops beforeFlush).slots
  directoryLive : captured.cached ∈ (((keeper.settledInventory.afterDrops between).insert slot free).afterDrops beforeFlush).slots
  cause : IO.Error
  stopped : Files
  failed : flush ((keeper.settledInventory.afterDrops between).insert slot free, slot, 0) afterWrite = .error cause stopped
  dropStatus : Except IO.Error Unit
  prefixBytes : Nat
  prefixBound : prefixBytes ≤ markerBytes.size
  reachedInodes : WalInodeImage
  dropped : drop ((keeper.settledInventory.afterDrops between).insert slot free, slot, 0) stopped =
    let reached := (scratchImage before.image (markerBytes.extract 0 prefixBytes), reachedInodes)
    match dropStatus with
    | .ok () => .ok () reached
    | .error error => .error error reached
  reachedView : DirectoryReadNamespace
  sameObjects : reachedView.modelObject = captured.view.modelObject
  child : RunChildLookup captured.root stageName reachedView
  lookupReachedStage : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  metadata : IO.FS.Metadata
  reachedStat : lookupReachedStage (directory.file .stagedWalBoundary) = .ok (metadata, child.child)
  regular : metadata.type = .file
  singleLink : metadata.numLinks = 1
  extent : metadata.byteSize.toNat = prefixBytes
  sameInode : reachedView.modelObject child.child = (keeper.settledInventory.afterDrops between).inode slot.description
  reachedMarkerInode : reachedInodes.active = reachedView.modelObject child.child
  reachedBytes : reachedInodes.visible reachedInodes.active = markerBytes.extract 0 prefixBytes
  keeperSeparate : captured.view.modelObject keeper.keeperChild ≠ reachedInodes.active
  offTargetNames : ∀ name, name ≠ stageName →
    reachedView.child captured.root name = keeper.keeperView.child captured.root name
  crashNames : String → List (Option DeviceInode)
  offTargetCrashNames : ∀ name, name ≠ stageName → crashNames name = [keeper.keeperView.child captured.root name]
  offTargetBytes : ∀ inode, inode ≠ reachedInodes.active →
    reachedInodes.visible inode = keeper.settledImage.visible inode ∧
    reachedInodes.crashBytes inode = keeper.settledImage.crashBytes inode
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  projectWrite :
    calls.write captured.cache (directory.file .stagedWalBoundary) markerBytes (atStage before.image) =
      bootstrapMarkerProjection (stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes
        (writeFreshStagedWith tryCreate (removeStaleStagingWith statStale unlinkStale) create
          (fun handle bytes => withDataErrorDrop drop handle (write handle bytes))
          (fun handle => withDataErrorDrop drop handle (flush handle)))
        (captured.cache, atStage before.image, keeper.settledImage))

namespace BootstrapMarkerFlushError

variable {keeper : BootstrapZeroKeeperRoute listed}

abbrev inventory (observed : BootstrapMarkerFlushError keeper) : DescriptorInventory :=
  (keeper.settledInventory.afterDrops observed.between).insert observed.slot observed.free

abbrev handle (observed : BootstrapMarkerFlushError keeper) : Handle := (observed.inventory, observed.slot, 0)

abbrev reached (observed : BootstrapMarkerFlushError keeper) : WalSegmentRotation.State :=
  scratchImage before.image (markerBytes.extract 0 observed.prefixBytes)

noncomputable abbrev stage (observed : BootstrapMarkerFlushError keeper) :=
  writeFreshStagedWith observed.tryCreate (removeStaleStagingWith observed.statStale observed.unlinkStale)
    observed.create (fun handle bytes => withDataErrorDrop observed.drop handle (observed.write handle bytes))
    (fun handle => withDataErrorDrop observed.drop handle (observed.flush handle))

/-- The reported drop may change the data even if it also reports an
error. It supplies the reached scratch image and preserves the flush cause. -/
theorem finalizedFlush (observed : BootstrapMarkerFlushError keeper) :
    withDataErrorDrop observed.drop observed.handle (observed.flush observed.handle) observed.afterWrite =
      .error observed.cause (observed.reached, observed.reachedInodes) := by
  rw [withDataErrorDrop_error _ _ _ observed.failed, dataErrorDropState, observed.dropped]
  cases status : observed.dropStatus with
  | ok result => cases result; rfl
  | error _ => rfl

/-- Staging returns after the same handle's reported finalizer effects.
It propagates the flush cause and leaves the pending cache untouched. -/
theorem stageError (observed : BootstrapMarkerFlushError keeper) :
    stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage
      (captured.cache, atStage before.image, keeper.settledImage) =
      .error observed.cause (captured.cache, observed.reached, observed.reachedInodes) := by
  have wrote :
      withDataErrorDrop observed.drop observed.handle (observed.write observed.handle markerBytes) observed.afterOpen =
        .ok () observed.afterWrite := by simp only [withDataErrorDrop, observed.wrote]
  exact stageFreshWithCache_error captured.cache _ _ observed.stage
    (observed.opening.flushError wrote observed.finalizedFlush)

/-- The same previously completed keeper barrier and cache enter the
failed native staging schedule. -/
theorem physicalPrefix (observed : BootstrapMarkerFlushError keeper) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    (keeper.groupedSync #[directory.path] *>
      stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage)
        (captured.cache, keeper.fileSyncedState, input) =
      .error observed.cause (captured.cache, observed.reached, observed.reachedInodes) := by
  have keeperDone := keeper.reachesMarker
  simpa only [SeqRight.seqRight, EStateM.seqRight, keeperDone, atStage, BootstrapZeroKeeperRoute.settledImage]
    using observed.stageError

/-- The pre-flush description identifies the regular file observed
after finalization. The settled keeper and absent marker are unchanged
at the same root. The descriptor memberships are at the flush call. -/
theorem physicalKeeper (observed : BootstrapMarkerFlushError keeper) :
    let atFlush := observed.inventory.afterDrops observed.beforeFlush
    observed.slot ∈ atFlush.slots ∧ calls.slot ∈ atFlush.slots ∧ captured.cached ∈ atFlush.slots ∧
    observed.slot.description ≠ calls.slot.description ∧ observed.slot.description ≠ captured.cached.description ∧
    observed.reachedView.modelObject captured.root = captured.reached.inode captured.cached.description ∧
    observed.reachedView.child captured.root stageName = some observed.child.child ∧
    observed.lookupReachedStage (directory.file .stagedWalBoundary) = .ok (observed.metadata, observed.child.child) ∧
    observed.metadata.type = .file ∧ observed.metadata.numLinks = 1 ∧ observed.metadata.byteSize.toNat = observed.prefixBytes ∧
    observed.prefixBytes ≤ markerBytes.size ∧
    observed.reachedInodes.active = atFlush.inode observed.slot.description ∧
    observed.child.child ≠ keeper.keeperChild ∧
    observed.reachedView.child captured.root keeperName = some keeper.keeperChild ∧
    observed.reachedView.child captured.root markerName = none ∧
    observed.crashNames keeperName = [some keeper.keeperChild] ∧ observed.crashNames markerName = [none] ∧
    observed.reachedInodes.visible keeper.settledImage.active = ByteArray.empty ∧
    observed.reachedInodes.crashBytes keeper.settledImage.active = [ByteArray.empty] ∧
    observed.reachedInodes.visible observed.reachedInodes.active = markerBytes.extract 0 observed.prefixBytes := by
  intro atFlush
  obtain ⟨_, _, keeperBound, keeperIdentity⟩ := keeper.settledCustody
  have separate := keeperIdentity ▸ observed.keeperSeparate
  have staged := observed.child.binds
  rw [observed.child.atRoot, observed.child.atName] at staged
  have keeperNotStage : keeperName ≠ stageName := by decide
  have markerNotStage : markerName ≠ stageName := by decide
  have freshDescription (old : DescriptorSlot)
      (live : old ∈ (keeper.settledInventory.afterDrops observed.between).slots) :
      observed.slot.description ≠ old.description := by
    intro alias
    have used := (keeper.settledInventory.afterDrops observed.between).mem_references.mpr
      ⟨old, live, rfl, alias.symm⟩
    rw [observed.fresh] at used
    exact List.not_mem_nil used
  obtain ⟨visible, crash⟩ := observed.offTargetBytes keeper.settledImage.active separate
  refine ⟨observed.fileLive, observed.lockLive, observed.directoryLive,
    freshDescription calls.slot observed.lockAtOpen, freshDescription captured.cached observed.directoryAtOpen,
    ?_, staged, observed.reachedStat, observed.regular, observed.singleLink, observed.extent, observed.prefixBound,
    observed.reachedMarkerInode.trans observed.sameInode, ?_,
    (observed.offTargetNames keeperName keeperNotStage).trans keeperBound,
    (observed.offTargetNames markerName markerNotStage).trans observed.canonicalAbsent,
    (observed.offTargetCrashNames keeperName keeperNotStage).trans (congrArg (fun child => [child]) keeperBound),
    (observed.offTargetCrashNames markerName markerNotStage).trans (congrArg (fun child => [child]) observed.canonicalAbsent),
    visible.trans keeper.settledVisible, crash.trans keeper.settledEmpty.2, observed.reachedBytes⟩
  · rw [observed.sameObjects]
    exact captured.captures.2.2.2.2
  · intro same
    apply observed.keeperSeparate
    calc
      captured.view.modelObject keeper.keeperChild = captured.view.modelObject observed.child.child :=
        congrArg captured.view.modelObject same.symm
      _ = observed.reachedView.modelObject observed.child.child := congrFun observed.sameObjects.symm _
      _ = observed.reachedInodes.active := observed.reachedMarkerInode.symm

/-- The bootstrap worker returns at the failed stage. The complete
directory and file barriers for the keeper have already run. -/
theorem worker (observed : BootstrapMarkerFlushError keeper) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.cause observed.reached ∧
    BootstrapValid observed.reached := by
  have failed := observed.projectWrite.trans (congrArg bootstrapMarkerProjection observed.stageError)
  have outcome := bootstrapEmptyWith_writeStagedError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy failed rfl rfl rfl
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans outcome.1, outcome.2⟩

def final (observed : BootstrapMarkerFlushError keeper) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerFlushError keeper) : IO.Error :=
  match calls.unlock with | .success => observed.cause | .failure cleanup _ => cleanup

/-- The opener returns the precise scratch prefix after local lock
cleanup. Its original marker is still absent in the live and crash views. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerFlushError keeper)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧ BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.metadata.crashImages = [before.image.metadata.active] ∧
    observed.final.image.successor = .durable ∧ observed.final.image.metadata.staged .walBoundary =
      some (markerBytes.extract 0 observed.prefixBytes, false) := by
  have recovered := (observed.worker valid).1
  have exactRun := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
    calls.unlock (calls.bootstrapAt directory captured.cache) before recovered
  refine ⟨?_, (observed.worker valid).2, calls.markerAbsent.1, rfl, rfl, rfl⟩
  rw [calls.runMarkerless admission captured.captures.1, exactRun]
  cases outcome : calls.unlock with
  | success => simp [final, returnedError, outcome]
  | failure cleanup released =>
    have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
    subst released
    simp [final, returnedError, outcome]

end BootstrapMarkerFlushError

end Alvoki.Storage.DiskSession
