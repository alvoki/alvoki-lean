import Alvoki.Storage.Disk.IntegrityDatabaseTrace

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotPin)

/-- The shared native read guard returns canonical results for the active
pins of the final ready session. The lock and token comparison are observed
for that session, which can differ from the session installed at bootstrap. -/
theorem IntegrityDatabaseTrace.guardedReadsFromFresh {initial before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (reports : IntegrityBootstrapOpenReports initial before durable)
    {start after : ObservedMarkedState}
    (installed : reports.run = .ok ((start.writer.table, start.generation, start.writer.walBytes), start.writer.image)
      reports.toIntegrityOpenPaths.heldOwners)
    (observed : MarkedWriterState.observeReopen start.writer.table start.writer.image = some start.writer)
    (kept : start.durable = durable) {sessions : List MarkedSessionWrites}
    (trace : IntegrityDatabaseTrace reports.directory start sessions after)
    {descriptor : Nat} {owners : DiskSession.LockOwners} (held : owners.Owns reports.directory descriptor) :
    MarkedSessionRetention sessions after.writer.history ∧ owners.Owns reports.directory descriptor ∧
      ∃ reference, SnapshotWalReplay .empty after.writer.history reference ∧
        ∀ pin : SnapshotPin, pin ∈ after.writer.table.pins.active →
          ∀ {sameSession : Bool} {issuer current : Nat}, sameSession = decide (issuer = current) → issuer = current →
            (∀ key, DiskSession.runGuardedRead (.ready after.writer.table) sameSession
              (fun table => table.lookup pin.handle key) owners =
              .ok (some (reference.table.lookup key pin.sequence)) owners) ∧
            ∀ lo hi, DiskSession.runGuardedRead (.ready after.writer.table) sameSession
              (fun table => table.range pin.handle lo hi) owners =
              .ok (some (reference.table.range lo hi pin.sequence)) owners := by
  obtain ⟨retained, _, _, reference, replayed, reads⟩ := trace.canonicalReadsFromFresh reports installed observed kept
  refine ⟨retained, held, reference, replayed, fun pin active sameSession issuer current compared localIssuer => ?_⟩
  have localComparison : sameSession = true := compared.trans (decide_eq_true localIssuer)
  have guard {α : Type} (read : PackedTable → Option α) :
      DiskSession.runGuardedRead (.ready after.writer.table) sameSession read owners =
        .ok (read after.writer.table) owners := by
    rw [localComparison]
    rfl
  obtain ⟨point, range⟩ := reads pin active
  exact ⟨fun key => by rw [guard, point key], fun lo hi => by rw [guard, range lo hi]⟩

end Alvoki.WAL.Boundary
