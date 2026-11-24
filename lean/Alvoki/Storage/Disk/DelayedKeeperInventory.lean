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

/-- The repair descriptor names the original lock inode and either
survives the drop interval or is opened after it. A new open supplies a
free slot in a live process epoch and a fresh description. -/
inductive KeeperRepairSlot (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    (writer repair : Nat) where
  | retained (reference : LockReference)
      (live : reference ∈ (inventory.afterDrops drops).references repair)
      (sameLock : inventory.inode repair = inventory.inode writer)
  | opened (slot : DescriptorSlot) (identity : slot.description = repair)
      (free : ∀ old ∈ (inventory.afterDrops drops).slots, old.address ≠ slot.address)
      (running : LockReferenceDrop.exited slot.reference.process ∉ drops)
      (fresh : inventory.references repair = []) (sameLock : inventory.inode repair = inventory.inode writer)

namespace KeeperRepairSlot

variable {inventory : DescriptorInventory} {drops : List LockReferenceDrop} {writer repair : Nat}

def census : KeeperRepairSlot inventory drops writer repair → DescriptorInventory
  | .retained .. => inventory.afterDrops drops
  | .opened slot _ free .. => (inventory.afterDrops drops).insert slot free

def reference : KeeperRepairSlot inventory drops writer repair → LockReference
  | .retained reference .. => reference
  | .opened slot .. => slot.reference

theorem keepsInodes (slot : KeeperRepairSlot inventory drops writer repair) :
    slot.census.inode = inventory.inode := by
  cases slot <;> rfl

theorem lockInode (slot : KeeperRepairSlot inventory drops writer repair) :
    slot.census.inode repair = inventory.inode writer := by
  cases slot with
  | retained _ _ sameLock => exact sameLock
  | opened _ _ _ _ _ sameLock => exact sameLock

theorem live (slot : KeeperRepairSlot inventory drops writer repair) :
    slot.reference ∈ slot.census.references repair := by
  cases slot with
  | retained _ live _ => exact live
  | opened _ identity _ _ _ _ => simp [reference, census, DescriptorInventory.references_insert, identity]

theorem keepsExistingReferences (slot : KeeperRepairSlot inventory drops writer repair)
    {description : Nat} (present : inventory.references description ≠ []) :
    slot.census.references description = (inventory.afterDrops drops).references description := by
  cases slot with
  | retained _ _ _ => rfl
  | opened opened identity _ _ fresh _ =>
    have different : opened.description ≠ description := fun same => present ((identity.symm.trans same) ▸ fresh)
    simp [census, DescriptorInventory.references_insert, different]

/-- A newly opened repair lock has exactly its returned slot in the
reached census, and its object is the original lock inode. -/
theorem openedCensus (slot : DescriptorSlot) (identity : slot.description = repair)
    (free : ∀ old ∈ (inventory.afterDrops drops).slots, old.address ≠ slot.address)
    (running : LockReferenceDrop.exited slot.reference.process ∉ drops)
    (fresh : inventory.references repair = []) (sameLock : inventory.inode repair = inventory.inode writer) :
    let reached := (KeeperRepairSlot.opened slot identity free running fresh sameLock).census
    reached.references repair = [slot.reference] ∧ reached.inode repair = inventory.inode writer := by
  refine ⟨?_, sameLock⟩
  simp [census, DescriptorInventory.references_insert, identity, DescriptorInventory.references_afterDrops, fresh]

end KeeperRepairSlot

/-- The original census supplies the writer release and retained keeper.
The repair slot is observed in the table at the rename cut, along with
the filesystem's lock and replacement bindings. -/
structure KeeperReplacementDropObservation {directory : DiskDirectory} {source : LockedFileState FileImage}
    {admits : Target → Prop} (cut : DelayedKeeperReplacementPowerLoss directory source admits) (writer : Nat) where
  inventory : DescriptorInventory
  writerLive : inventory.references writer ≠ []
  writerEnded : (inventory.afterDrops cut.report.drops).references writer = []
  issuing : cut.report.issuer ∈ (inventory.afterDrops cut.report.drops).references cut.report.captured.description
  oldKeeper : inventory.inode cut.report.captured.description = cut.previous.active
  repair : KeeperRepairSlot inventory cut.report.drops writer cut.attempt.descriptor
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
    let census := observed.repair.census
    let effect := observed.report.effectTarget
    let repair := cut.attempt.descriptor
    let current := cut.previous.renameSynced cut.replacement cut.bounded.keeperBytes
    cut.report.issuer ∈ census.references effect.description ∧
      effect.description ≠ writer ∧ effect.inode = cut.previous.active ∧ effect.inode ≠ current.active ∧
      observed.bindings (directory.file (.walSegment cut.bounded.keeper)) = some current.active ∧
      observed.repair.reference ∈ census.references repair ∧ census.references writer = [] ∧
      repair ≠ writer ∧
      observed.bindings (directory.file .lock) = some (census.inode repair) ∧
      census.inode repair = observed.inventory.inode writer ∧
      observed.observedCut.during.owners.Owns directory repair ∧
      ∃ (target : Target) (full : Plan), admits target ∧ cut.bounded.keeperBytes = target.trimmed ∧
        ReachesAction target source.image.syncDirectory full.finishActions (.replace .syncDirectory) cut.reached := by
  intro census effect repair current
  have ended : census.references writer = [] :=
    (observed.repair.keepsExistingReferences observed.writerLive).trans observed.writerEnded
  have keeperRefs : census.references effect.description =
      (observed.inventory.afterDrops cut.report.drops).references cut.report.captured.description :=
    observed.repair.keepsExistingReferences (DescriptorInventory.wasLive observed.issuing)
  have issuer : cut.report.issuer ∈ census.references effect.description := keeperRefs.symm ▸ observed.issuing
  have repairLive : observed.repair.reference ∈ census.references repair := observed.repair.live
  have separate : cut.report.captured.description ≠ writer := by
    intro same
    have issuing := observed.issuing
    rw [same, observed.writerEnded] at issuing
    exact List.not_mem_nil issuing
  have repairSeparate : repair ≠ writer := by
    intro same
    rw [same, ended] at repairLive
    exact List.not_mem_nil repairLive
  refine ⟨issuer, separate, observed.oldKeeper, ?_, observed.replacementBinding,
    repairLive, ended, repairSeparate, ?_, observed.repair.lockInode, ?_, ?_⟩
  · change observed.inventory.inode cut.report.captured.description ≠ cut.replacement
    rw [observed.oldKeeper]
    exact cut.distinct
  · change observed.bindings (directory.file .lock) = some (observed.repair.census.inode repair)
    rw [observed.repair.keepsInodes]
    exact observed.lockBinding
  · simp [LockOwners.Owns, DelayedKeeperReplacementPowerLoss.during, observedCut, LockOwners.set, repair]
  · obtain ⟨target, full, _, _, admitted, bytes, reaches, _, _, _, _, _, _⟩ :=
      observed.report.atBoundedReplacementBarrier cut.attempt directory source.image cut.previous cut.replacement
        cut.acquired cut.reports cut.reading cut.noLater cut.longer cut.barrier cut.renamed cut.projected
        observed.oldKeeper cut.distinct cut.freshInode cut.allowed
    exact ⟨target, full, admitted, bytes, reaches⟩

end KeeperReplacementDropObservation

end Alvoki.Storage.DiskSession
