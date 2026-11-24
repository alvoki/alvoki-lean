import Alvoki.Storage.Disk.LockedRecoveryReads

namespace Alvoki.WAL.Boundary

open Storage

/-- The concrete inputs to the empty and marked recovery interpreters.
The marked interpreter covers settled, checkpoint-cut and write-cut recovery. -/
inductive RecoveryExecution where
  | empty (checkpoint : Except String (Option (PackedTable × UInt64)))
      (marker wal : Except String (Option ByteArray)) (reports : FreshOpenReports) (before : ReopenImage)
  | marked (checkpoint : Except String (Option (PackedTable × UInt64)))
      (marker wal : Except String (Option ByteArray)) (repair : Publication.Step → RepairReport)
      (aligned : AlignedSyncReport) (before : ReopenImage)

private def returnedOpen (result : EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat)) :
    Except String ((PackedTable × UInt64 × Nat) × ReopenImage) :=
  match result with
  | .ok installed after => .ok (installed, after)
  | .error cause _ => .error cause

/-- The outer lock schedule receives the installation and its image on
success, or the recovery error. The recovery interpreters retain their own
file-effect contracts on failure. -/
def RecoveryExecution.run : RecoveryExecution → Except String ((PackedTable × UInt64 × Nat) × ReopenImage)
  | .empty checkpoint marker wal reports before => (runFreshMarkedOpen checkpoint marker wal reports).run before
  | .marked checkpoint marker wal repair aligned before =>
    returnedOpen (runSharedMarkedOpen checkpoint marker wal repair aligned before)

private theorem returnedOpen_ok {result : EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat)}
    {installed : PackedTable × UInt64 × Nat} {after : ReopenImage} :
    returnedOpen result = .ok (installed, after) ↔ result = .ok installed after := by
  cases result <;> simp [returnedOpen]

/-- Each admitted boundary identifies one concrete evaluator and the same
successful result. -/
theorem RecoveryBoundary.exposesExecution
    {opened : (PackedTable × UInt64 × Nat) → ReopenImage → Prop} {manifest : Option ByteArray}
    {allowsHistory : List WAL.Write → Prop} (boundary : RecoveryBoundary opened manifest allowsHistory) :
    ∃ execution : RecoveryExecution, ∀ installed after,
      execution.run = .ok (installed, after) ↔ opened installed after := by
  cases boundary with
  | empty reads _ reports _ _ _ =>
    exact ⟨.empty reads.checkpointReads.result reads.walReads.marker reads.walReads.wal reports _, fun _ _ => Iff.rfl⟩
  | settled _ reads _ _ _ _ report =>
    exact ⟨.marked reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report .success _,
      fun _ _ => returnedOpen_ok⟩
  | checkpoint reads _ _ _ _ _ _ _ _ report =>
    exact ⟨.marked reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report .success _,
      fun _ _ => returnedOpen_ok⟩
  | interruptedWrite _ reads _ _ _ _ _ _ report aligned _ =>
    exact ⟨.marked reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report aligned _,
      fun _ _ => returnedOpen_ok⟩

/-- After a reported successful exclusive acquisition, the outer native
schedule runs the evaluator given by the admitted recovery boundary. The
caller supplies that boundary using ownership of this same canonical lock,
for example with `RecoveryReads.ofLockedPaths`. The theorem derives the
installation and settled image from the evaluator's completion. A stable
lock object and a live open file description remain primitive contracts. -/
theorem RecoveryBoundary.completesWithLock
    {opened : (PackedTable × UInt64 × Nat) → ReopenImage → Prop} {manifest : Option ByteArray}
    {allowsHistory : List WAL.Write → Prop} {directory : DiskDirectory} {descriptor : Nat}
    {owners : DiskSession.LockOwners} (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    (admitted : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      RecoveryBoundary opened manifest allowsHistory)
    (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    ∃ execution : RecoveryExecution, ∃ table generation after events installedOwners,
      (∀ installed image, execution.run = .ok (installed, image) ↔ opened installed image) ∧
      DiskSession.runOpen directory descriptor (.ok true) (execution.run.mapError cause) unlock owners =
        .ok ((table, generation, (WAL.encode events).size), after) installedOwners ∧
      installedOwners.Owns directory descriptor ∧ after.SettledFor manifest events ∧
      allowsHistory events ∧ table.committed.toNat = events.length := by
  have held : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor := by
    simp [DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
  have boundary := admitted held
  obtain ⟨execution, corresponds⟩ := boundary.exposesExecution
  obtain ⟨table, generation, after, events, completed, settled, allowed, count⟩ := boundary.completes
  have ran := (corresponds (table, generation, (WAL.encode events).size) after).mpr completed
  let installedOwners := owners.set (directory.file .lock) (some descriptor)
  have openedWithLock :
      DiskSession.runOpen directory descriptor (.ok true) (execution.run.mapError cause) unlock owners =
        .ok ((table, generation, (WAL.encode events).size), after) installedOwners := by
    rw [ran]
    rfl
  obtain ⟨_, installed, _, _⟩ := DiskSession.runOpen_success acquisition openedWithLock
  exact ⟨execution, table, generation, after, events, installedOwners, corresponds,
    openedWithLock, installed, settled, allowed, count⟩

end Alvoki.WAL.Boundary
