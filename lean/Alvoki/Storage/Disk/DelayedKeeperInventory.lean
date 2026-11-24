import Alvoki.Storage.Disk.DescriptorInventory

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- A retained keeper sync uses the issuing slot from the descriptor
census for the actual drop interval. Its object follows from that census. -/
def DescriptorInventory.delayedKeeperSync (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    (description : Nat) (issuer : LockReference)
    (issuing : issuer ∈ (inventory.afterDrops drops).references description)
    (outcomes : List ByteArray) : DelayedKeeperSync where
  captured := ⟨description, inventory.inode description⟩
  references := inventory.held description (wasLive issuing)
  issuer := issuer
  drops := drops
  retained := by rwa [inventory.held_remaining]
  effectTarget := ⟨description, inventory.inode description⟩
  sameTarget := rfl
  outcomes := outcomes

/-- One census links the poisoned writer's final lock drop, the retained
keeper descriptor, and the repairing opener's live lock slot. The census
already includes the repair description when the drop interval starts.
The filesystem supplies the object bindings at the observed rename cut. -/
structure KeeperReplacementDropObservation {directory : DiskDirectory} {source : LockedFileState FileImage}
    {admits : Target → Prop} (cut : DelayedKeeperReplacementPowerLoss directory source admits) (writer : Nat) where
  inventory : DescriptorInventory
  writerLive : inventory.references writer ≠ []
  writerEnded : (inventory.afterDrops cut.report.drops).references writer = []
  issuing : cut.report.issuer ∈ (inventory.afterDrops cut.report.drops).references cut.report.captured.description
  oldKeeper : inventory.inode cut.report.captured.description = cut.previous.active
  repairSlot : LockReference
  repairLive : repairSlot ∈ (inventory.afterDrops cut.report.drops).references cut.attempt.descriptor
  bindings : FilePath → Option Nat
  lockBinding : bindings (directory.file .lock) = some (inventory.inode cut.attempt.descriptor)
  replacementBinding : bindings (directory.file (.walSegment cut.bounded.keeper)) = some cut.replacement

namespace KeeperReplacementDropObservation

variable {directory : DiskDirectory} {source : LockedFileState FileImage} {admits : Target → Prop}
  {cut : DelayedKeeperReplacementPowerLoss directory source admits} {writer : Nat}

def report (observed : KeeperReplacementDropObservation cut writer) : DelayedKeeperSync :=
  observed.inventory.delayedKeeperSync cut.report.drops cut.report.captured.description cut.report.issuer
    observed.issuing cut.report.outcomes

theorem last (observed : KeeperReplacementDropObservation cut writer) :
    (observed.inventory.held writer observed.writerLive).remaining cut.report.drops = [] := by
  rw [observed.inventory.held_remaining]
  exact observed.writerEnded

def release (observed : KeeperReplacementDropObservation cut writer) : SegmentedFailureRelease writer :=
  .references (observed.inventory.held writer observed.writerLive) cut.report.drops observed.last

/-- Use the same drop interval for the poisoned writer's actual release
and for the live old keeper's effect-time lookup. -/
theorem releasesWriter {before : SegmentedWriterState} (failure : SegmentedAppendFailure directory before)
    {cut : DelayedKeeperReplacementPowerLoss directory failure.released admits}
    (observed : KeeperReplacementDropObservation cut writer) (ready : before.RetainedReady directory writer) :
    observed.release.Observed (directory := directory) failure.poisoned
      ⟨failure.failed, before.owners.set (directory.file .lock) none⟩ :=
  (observed.inventory.held writer observed.writerLive).afterFileDrops_released ready.held observed.last

private theorem sameEffect (observed : KeeperReplacementDropObservation cut writer) (inodes : WalInodeImage) :
    observed.report.effect inodes = cut.report.effect inodes := by
  unfold DelayedKeeperSync.effect
  rw [cut.report.sameTarget, cut.oldTarget]
  change inodes.reportFileSync (observed.inventory.inode cut.report.captured.description) cut.report.outcomes = _
  rw [observed.oldKeeper]

/-- Reuse the reached rename and physical survivors with the keeper
report constructed from the shared census. -/
def observedCut (observed : KeeperReplacementDropObservation cut writer) :
    DelayedKeeperReplacementPowerLoss directory source admits :=
  { cut with
    report := observed.report
    oldTarget := observed.oldKeeper
    survived := by simpa only [observed.sameEffect] using cut.survived }

theorem sameReachedStates (observed : KeeperReplacementDropObservation cut writer) :
    observed.observedCut.during = cut.during ∧ observed.observedCut.crashed = cut.crashed := by
  have effect : observed.observedCut.during = cut.during := by
    simp only [DelayedKeeperReplacementPowerLoss.during, observedCut, observed.sameEffect]
  refine ⟨effect, ?_⟩
  unfold DelayedKeeperReplacementPowerLoss.crashed
  rw [effect]
  rfl

/-- At the rename cut the live repair slot owns the database lock. The
retained keeper's effect targets the old object, while the canonical
keeper pathname already names the replacement. -/
theorem effectTime (observed : KeeperReplacementDropObservation cut writer) :
    let census := observed.inventory.afterDrops cut.report.drops
    let effect := observed.report.effectTarget
    let repair := cut.attempt.descriptor
    let current := cut.previous.renameSynced cut.replacement cut.bounded.keeperBytes
    cut.report.issuer ∈ census.references effect.description ∧
      effect.description ≠ writer ∧ effect.inode = cut.previous.active ∧ effect.inode ≠ current.active ∧
      observed.bindings (directory.file (.walSegment cut.bounded.keeper)) = some current.active ∧
      observed.repairSlot ∈ census.references repair ∧
      repair ≠ writer ∧
      observed.bindings (directory.file .lock) = some (census.inode repair) ∧
      observed.observedCut.during.owners.Owns directory repair ∧
      ∃ (target : Target) (full : Plan), admits target ∧ cut.bounded.keeperBytes = target.trimmed ∧
        ReachesAction target source.image.syncDirectory full.finishActions (.replace .syncDirectory) cut.reached := by
  intro census effect repair current
  have separate : cut.report.captured.description ≠ writer := by
    intro same
    have issuing := observed.issuing
    rw [same, observed.writerEnded] at issuing
    exact List.not_mem_nil issuing
  have repairSeparate : repair ≠ writer := by
    intro same
    have live : observed.repairSlot ∈ census.references repair := observed.repairLive
    rw [same, show census.references writer = [] from observed.writerEnded] at live
    exact List.not_mem_nil live
  refine ⟨observed.issuing, separate, observed.oldKeeper, ?_, observed.replacementBinding,
    observed.repairLive, repairSeparate, observed.lockBinding, ?_, ?_⟩
  · change observed.inventory.inode cut.report.captured.description ≠ cut.replacement
    rw [observed.oldKeeper]
    exact cut.distinct
  · simp [LockOwners.Owns, DelayedKeeperReplacementPowerLoss.during, observedCut, LockOwners.set, repair]
  · obtain ⟨target, full, _, _, admitted, bytes, reaches, _, _, _, _, _, _⟩ :=
      observed.report.atBoundedReplacementBarrier cut.attempt directory source.image cut.previous cut.replacement
        cut.acquired cut.reports cut.reading cut.noLater cut.longer cut.barrier cut.renamed cut.projected
        observed.oldKeeper cut.distinct cut.freshInode cut.allowed
    exact ⟨target, full, admitted, bytes, reaches⟩

end KeeperReplacementDropObservation

end Alvoki.Storage.DiskSession
