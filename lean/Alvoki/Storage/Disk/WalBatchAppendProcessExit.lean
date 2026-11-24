import Alvoki.Storage.Disk.WalBatchAppendPowerLoss

namespace Alvoki.Storage.DiskSession.FirstAppendCut

open System WAL.Boundary WalSegmentRepair

/-- Apply an observed process-table exit to the live batch append cut.
The drop leaves the observed file image intact. A cooperating open can
acquire the lock exactly when the complete census has no surviving slots. -/
theorem batchProcessExit (cut : FirstAppendCut) {directory writer before}
    (ready : before.RetainedReady directory writer) (batch : List WAL.Write)
    (references : HeldLockReferences writer) (process : Nat) :
    let live : LockedFileState FileImage := ⟨cut.physical before, before.owners⟩
    let exited := references.afterFileDrops [.exited process] directory live
    BoundedReopenTrace directory (fun target => target = before.target) live exited ∧
    exited.image = live.image ∧
    (TryLockObserves exited.owners directory (.ok true) ↔ references.remaining [.exited process] = []) ∧
    BatchRetryTarget before.history batch before.wal.active.first before.target ∧
    exited.image.directory.active = before.target.pair ∧
    let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ cut.visibleTail
    exited.image.keeper.active = some bytes ∧
    selectRetained before.installed.activeFirst (WAL.encode before.history).size.toUInt64 bytes =
      .ok before.wal.active.bytes := by
  intro live exited
  have held : live.owners.Owns directory writer := ready.held
  have admission : TryLockObserves exited.owners directory (.ok true) ↔
      references.remaining [.exited process] = [] := by
    change TryLockObserves (references.afterFileDrops [.exited process] directory live).owners directory (.ok true) ↔ _
    by_cases last : references.remaining [.exited process] = []
    · rw [references.afterFileDrops_released held last]
      simp [TryLockObserves, LockOwners.set, last]
    · rw [references.afterFileDrops_surviving last]
      constructor
      · intro reported
        change live.owners (directory.file .lock) = some writer at held
        rw [reported rfl] at held
        contradiction
      · exact fun gone => False.elim (last gone)
  obtain ⟨marker, selected⟩ := ready.selectPriorKeeper cut.visibleTail
  have old : BatchRetryTarget before.history batch before.wal.active.first before.target := by
    refine ⟨ready.active, before.history, .inl rfl, marker, ready.resumed.through, ?_⟩
    rw [ready.resumed.contents, ready.active]
  exact ⟨.referenceDrops .empty references [.exited process], rfl, admission, old, ready.resumed.ready.selected,
    rfl, selected⟩

end Alvoki.Storage.DiskSession.FirstAppendCut
