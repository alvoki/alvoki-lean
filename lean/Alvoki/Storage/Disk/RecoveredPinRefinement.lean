import Alvoki.Storage.Disk.DiskRecoveryModel

namespace Alvoki.Storage

open Alvoki.Sequential (SnapshotPins SnapshotTable)

/-- A packed table holding the same data and floor refines the reference
model with the actual session's pin registry, provided those pins have valid
sequences. In particular this applies to a newly restored empty registry. -/
theorem PackedTable.SameData.refines_rebindPins {actual reference : PackedTable}
    {model : SnapshotTable UInt64} (same : actual.SameData reference)
    (refines : reference.Refines model)
    (committed : ∀ pin ∈ actual.pins.active, pin.sequence ≤ actual.committed) :
    ∃ rebound, actual.Refines rebound ∧ rebound.table = model.table ∧
      rebound.committed = model.committed ∧ rebound.pins.floor = model.pins.floor := by
  have floor := same.floor.trans (congrArg SnapshotPins.floor refines.pins)
  have sameCommit := same.committed.trans refines.committed
  obtain ⟨rebound, data, clock, registry⟩ :=
    model.exists_reboundPins actual.pins floor (fun pin mem => sameCommit ▸ committed pin mem)
  exact ⟨rebound, ⟨same.describe.trans (refines.table.trans data.symm), sameCommit.trans clock.symm,
    registry.symm⟩, data, clock, (congrArg SnapshotPins.floor registry).trans floor⟩

/-- The same suffix continues the original abstract history while the exact
replayed table refines a model with the newly loaded session's pin registry. -/
theorem replay_refines_recoveredPins {checkpoint loaded reopened : PackedTable}
    {model : SnapshotTable UInt64} {pending : List WAL.Write}
    (same : loaded.SameData checkpoint) (fresh : loaded.pins.active = [])
    (refines : checkpoint.Refines model) (played : replay loaded pending = .ok reopened) :
    ∃ abstract next, SnapshotWalReplay model pending abstract ∧ reopened.Refines next ∧
      next.table = abstract.table ∧ next.committed = abstract.committed ∧
      next.pins.floor = abstract.pins.floor ∧ next.pins.active = [] := by
  obtain ⟨reference, replayed, agrees⟩ := replay_sameData same.symm pending played
  obtain ⟨abstract, modeled, refined⟩ := replay_refines refines replayed
  have noPins : reopened.pins.active = [] := by rwa [replay_pins played]
  obtain ⟨next, nextRefines, table, committed, floor⟩ :=
    agrees.symm.refines_rebindPins refined (by simp [noPins])
  exact ⟨abstract, next, modeled, nextRefines, table, committed, floor,
    by rw [← nextRefines.pins, noPins]⟩

/-- Refine the actual table returned by an exact checkpoint load followed by
selected WAL recovery. The relation preserves replay against the old model
and gives the recovered writer its own refined abstract session. -/
theorem recoverSelectedCheckpoint_refines_recoveredPins {manifest : Option ByteArray}
    {files : List ByteArray} {checkpoint reopened : PackedTable} {model : SnapshotTable UInt64}
    {covered pending : List WAL.Write} (written : CheckpointForRecovery manifest files checkpoint)
    (refines : checkpoint.Refines model) (watermark : covered.length = checkpoint.committed.toNat)
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending))
    (opened : (manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun base =>
        recoverSelected base (WAL.encode (covered ++ pending))) = .ok reopened) :
    ∃ abstract next, SnapshotWalReplay model pending abstract ∧ reopened.Refines next ∧
      next.table = abstract.table ∧ next.committed = abstract.committed ∧
      next.pins.floor = abstract.pins.floor ∧ next.pins.active = [] := by
  obtain ⟨loaded, loads, same⟩ := written.loads
  have load : manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) = .ok loaded := by
    cases manifest <;> exact loads
  have fresh : loaded.pins.active = [] := by
    cases manifest with
    | none =>
      change Except.ok PackedTable.empty = .ok loaded at load
      cases load
      rfl
    | some bytes =>
      change (Manifest.decode bytes >>= fun header => loadRunSet header files) = .ok loaded at load
      cases decoded : Manifest.decode bytes with
      | error => rw [decoded] at load; contradiction
      | ok header =>
        rw [decoded] at load
        exact loadRunSet_clearsPins load
  rw [load] at opened
  change recoverSelected loaded (WAL.encode (covered ++ pending)) = .ok reopened at opened
  rw [recoverSelected_encoded loaded covered pending ordered (same.committed ▸ watermark)] at opened
  exact replay_refines_recoveredPins same fresh refines opened

end Alvoki.Storage
