import Alvoki.Storage.Disk.Proofs.Append.AppendCutSession
import Alvoki.Storage.Disk.DescriptorInventory
import Alvoki.Storage.Disk.WalSegmentCachedRetryCompletion

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Run the cached recovery worker with the observed checkpoint and WAL callbacks. -/
def cachedRetryRecovery {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} (reported : CachedRetryReadReports directory layout)
    (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) : EStateM IO.Error FileImage Reopened :=
  reopenMarkedBoundedWithCachedExtents directory
    (fun path => liftExcept (reported.inventory.reports.readOptional path))
    (fun path => liftExcept (checkpointRunSizeReport reported.inventory.reports path))
    (fun path size => liftExcept (readRunPrefix path size))
    (fun path => liftExcept (reported.list path))
    (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
    (fun path size => liftExcept (reported.readSeal path size))
    (fun path size physical => liftExcept (reported.readKeeper path size physical))
    removeFile write sync renameFile

/-- The installed result of a cached retry, including the exact repaired
image, lock description and replay of the selected checkpoint. -/
def CachedRetryInstalled {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} (reported : CachedRetryReadReports directory layout)
    (descriptors : DescriptorInventory) (slot : DescriptorSlot) (bindings : FilePath → Option Nat)
    (published : CheckpointPublication.Image) (liveRefs : List Nat)
    (result : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession) : Prop :=
  ∃ (opened : Reopened) (checkpoint : Option (PackedTable × UInt64)) (model : Sequential.SnapshotTable UInt64)
    (session : SegmentedSession) (final : LockedFileState FileImage),
    result = .ok session final ∧
    session.directory = directory ∧ session.descriptor = reported.inventory.descriptor ∧
    session.phase = .ready opened.installed ∧
    slot ∈ descriptors.slots ∧
    bindings (directory.file .lock) = some (descriptors.inode session.descriptor) ∧
    before.owners (directory.file .lock) = none ∧ final.owners = reported.inventory.owners ∧
    final.owners.Owns directory session.descriptor ∧
    session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs ∧
    final.image.Ready layout.target ∧ EffectTrace layout.target before.image final.image ∧
    SelectedIntegrityCheckpoint published.durable before.image.directory.active.manifest checkpoint ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
    opened.generation = (checkpoint.getD (.empty, 0)).2 ∧
    opened.walBytes.toNat = history.length * frameSize ∧ opened.keeper = layout.keeper.first ∧
    opened.table.committed.toNat = history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
    RepresentsWalHistory history model ∧ opened.table.pins.active = []

/-- Install the exact result of the healthy cached recovery schedule under
the lock observed for this attempt. The supplied slot is live at acquisition,
its open description refers to the canonical lock object, and the read
inventory belongs to the resulting owner map. The native observations have
to supply that identity and its continuity through the recovery callbacks. -/
theorem runOpenWithInstallation_cachedRetryCompletes
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} (reported : CachedRetryReadReports directory layout)
    (descriptors : DescriptorInventory) (slot : DescriptorSlot) (live : slot ∈ descriptors.slots)
    (bindings : FilePath → Option Nat)
    (lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description))
    (flock : DescriptorSlot → Except IO.Error Bool) (acquired : flock slot = .ok true)
    (acquisition : TryLockObserves before.owners directory (flock slot))
    (inventoryDescription : reported.inventory.descriptor = slot.description)
    (inventoryOwners : reported.inventory.owners = before.owners.set (directory.file .lock) (some slot.description))
    (nextRef : Nat) (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sizes : SizedCheckpointRunReports directory reported.inventory.reports before.image.directory.active.manifest
      published.durable)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok before.image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) =
      .ok before.image.directory.active.walBoundary)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] before.image = .ok () before.image.syncDirectory)
    (healthy : ∀ action prior next,
      ReachesAction layout.target before.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan removeFile throw write sync renameFile action prior = .ok () next) :
    CachedRetryInstalled (before := before) reported descriptors slot bindings published liveRefs
      (runOpenWithInstallation directory slot.description nextRef (flock slot) unlock
        (cachedRetryRecovery reported sizes.readPrefix removeFile write sync renameFile) before) := by
  let recover := cachedRetryRecovery reported sizes.readPrefix removeFile write sync renameFile
  obtain ⟨opened, image, checkpoint, model, durable, trace, recovered, selected, replay, generation, bytes,
    keeper, committed, bounds, refines, represents, noPins⟩ :=
    reported.completes keeperValid laterValid following accepted ordered sizes manifestRead markerRead
      removeFile write sync renameFile settles healthy
  have outcome : recover before.image = .ok opened image := recovered
  have acquiredLock : TryLockObserves before.owners directory (.ok true) := acquired ▸ acquisition
  obtain ⟨session, final, installed, path, description, phase, exactImage, vacant, held, distinct, freshPhase,
    freshSession⟩ := runOpenWithInstallation_ready liveRefs fresh acquiredLock (unlock := unlock) outcome
  have exactResult := installed
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired, outcome] at exactResult
  have exactOwners : final.owners = reported.inventory.owners :=
    (congrArg LockedFileState.owners (EStateM.Result.ok.inj exactResult).2).symm.trans inventoryOwners.symm
  have seenObject : bindings (directory.file .lock) = some (descriptors.inode session.descriptor) := by
    rw [description]
    exact lockObject
  exact ⟨opened, checkpoint, model, session, final, acquired.symm ▸ installed, path,
    description.trans inventoryDescription.symm, phase, live, seenObject, vacant, exactOwners, description ▸ held,
    distinct, freshPhase, freshSession, exactImage ▸ durable, exactImage ▸ trace, selected, replay, generation, bytes,
    keeper, committed, bounds, refines, represents, noPins⟩

/-- The exact cached installation supplies the append-ready witness used
to reconstruct a retained writer. -/
theorem CachedRetryInstalled.readyForAppend
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {reported : CachedRetryReadReports directory layout}
    {descriptors slot bindings published liveRefs result}
    (installed : CachedRetryInstalled reported descriptors slot bindings published liveRefs result)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ generation, AppendCutReady directory reported.inventory.descriptor liveRefs history published before.image
      layout.target generation result := by
  obtain ⟨opened, checkpoint, model, session, final, returned, path, descriptor, phase, _, _, _, _, held,
    distinct, freshPhase, freshSession, ready, effects, selected, replay, generation, bytes, keeper, committed,
    bounds, refines, represents, pins⟩ := installed
  have exactBytes : opened.walBytes.toNat = (WAL.encode history).size := by
    rw [bytes, WAL.encode_size, Nat.mul_comm]
  have payload : session.phase = .ready ⟨opened.table, opened.generation, (WAL.encode history).size, layout.target.first⟩ := by
    simpa only [Reopened.installed, exactBytes, keeper, CanonicalKeeperLayout.target] using phase
  exact ⟨opened.generation, layout.through, layout.chain.keeperBytes, accepted, ordered, checkpoint, opened.table,
    model, session, final, returned, selected, generation, replay, path, descriptor, payload, ready, effects.keepsSealed,
    descriptor ▸ held, committed, bounds, refines, represents, pins, distinct, freshPhase, freshSession⟩

/-- The selected manifest and durable run map determine the restored checkpoint. -/
theorem _root_.Alvoki.Storage.SelectedIntegrityCheckpoint.uniqueResult {durable : CheckpointPublication.RunFiles}
    {binding left right}
    (first : SelectedIntegrityCheckpoint durable binding left)
    (second : SelectedIntegrityCheckpoint durable binding right) : left = right := by
  cases first with
  | absent => cases second; rfl
  | @present bytes manifest files table decoded stored loaded =>
    cases second with
    | @present _ otherManifest otherFiles otherTable otherDecoded otherStored otherLoaded =>
      obtain rfl := Except.ok.inj (decoded.symm.trans otherDecoded)
      obtain rfl := Option.some.inj (stored.symm.trans otherStored)
      obtain rfl := Except.ok.inj (loaded.symm.trans otherLoaded)
      rfl

/-- Once both retries choose the same physical checkpoint binding and
the same WAL history and keeper, their installed data agree. Descriptor
and reference identities can still differ between the two opens. -/
theorem CachedRetryInstalled.sameInstalled {directory : DiskDirectory} {history : List WAL.Write}
    {leftBefore rightBefore : LockedFileState FileImage}
    {leftLayout : CanonicalKeeperLayout leftBefore.image history}
    {rightLayout : CanonicalKeeperLayout rightBefore.image history}
    {leftReports : CachedRetryReadReports directory leftLayout}
    {rightReports : CachedRetryReadReports directory rightLayout}
    {leftDescriptors rightDescriptors : DescriptorInventory} {leftSlot rightSlot : DescriptorSlot}
    {leftBindings rightBindings : FilePath → Option Nat} {leftRefs rightRefs : List Nat}
    {published : CheckpointPublication.Image}
    {leftResult rightResult : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession}
    (left : CachedRetryInstalled (before := leftBefore) leftReports leftDescriptors leftSlot
      leftBindings published leftRefs leftResult)
    (right : CachedRetryInstalled (before := rightBefore) rightReports rightDescriptors rightSlot
      rightBindings published rightRefs rightResult)
    (sameManifest : leftBefore.image.directory.active.manifest = rightBefore.image.directory.active.manifest)
    (sameKeeper : leftLayout.keeper.first = rightLayout.keeper.first) :
    ∃ leftSession leftFinal rightSession rightFinal installed,
      leftResult = .ok leftSession leftFinal ∧ rightResult = .ok rightSession rightFinal ∧
      leftSession.phase = .ready installed ∧ rightSession.phase = .ready installed := by
  obtain ⟨leftOpen, leftCheckpoint, _, leftSession, leftFinal, ranLeft, _, _, leftPhase,
    _, _, _, _, _, _, _, _, _, _, leftSelected, leftReplay, leftGeneration, leftBytes, leftKeeper, _⟩ := left
  obtain ⟨rightOpen, rightCheckpoint, _, rightSession, rightFinal, ranRight, _, _, rightPhase,
    _, _, _, _, _, _, _, _, _, _, rightSelected, rightReplay, rightGeneration, rightBytes, rightKeeper, _⟩ := right
  have checkpoint : leftCheckpoint = rightCheckpoint := leftSelected.uniqueResult (sameManifest.symm ▸ rightSelected)
  have table : leftOpen.table = rightOpen.table := by
    rw [checkpoint, rightReplay] at leftReplay
    exact (Except.ok.inj leftReplay).symm
  have equal : leftOpen.installed = rightOpen.installed := by
    simp only [WalSegmentRepair.Reopened.installed, table, leftGeneration, rightGeneration,
      checkpoint, leftBytes, rightBytes, leftKeeper, rightKeeper, sameKeeper]
  exact ⟨leftSession, leftFinal, rightSession, rightFinal, rightOpen.installed, ranLeft, ranRight,
    leftPhase.trans (congrArg DiskSession.Phase.ready equal), rightPhase⟩

end Alvoki.Storage.DiskSession
