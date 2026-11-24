import Alvoki.Storage.Disk.CheckpointHistory
import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.RecoveredPinRefinement

namespace Alvoki.WAL.Boundary
open Storage

/-- A fixed-checkpoint recovery returns the next refined writer, including
the fresh pin registry. Every acknowledgement extends the durable history
in order, and only the final ambiguous event may be dropped. -/
theorem MarkedSessionStep.refinesHistory {checkpoint : FixedMarkedCheckpoint}
    {initial after : MarkedWriterState} {writes : MarkedSessionWrites} {pending : List WAL.Write}
    (step : MarkedSessionStep checkpoint initial writes after)
    (ready : initial.ReadyFor checkpoint.manifest) (start : initial.history = checkpoint.covered ++ pending)
    (checkpointHistory : RepresentsWalHistory checkpoint.covered checkpoint.model) :
    ∃ suffix, after.ReadyFor checkpoint.manifest ∧ after.history = initial.history ++ suffix ∧
      writes.Retains suffix ∧ ∃ model, after.table.Refines model ∧
        RepresentsWalHistory after.history model ∧ after.table.pins.active = [] := by
  obtain ⟨suffix, nextReady, extended, retained, exactTable, _⟩ := step.refinesWithReplay ready start
  have split : after.history = checkpoint.covered ++ (pending ++ suffix) := by
    rw [extended, start, List.append_assoc]
  have ordered : WAL.OrdinalsFrom 1 (checkpoint.covered ++ (pending ++ suffix)) :=
    split ▸ nextReady.ordered
  unfold FixedMarkedCheckpoint.RecoveredTable at exactTable
  rw [split] at exactTable
  obtain ⟨abstract, next, replayed, refined, table, clock, floor, fresh⟩ :=
    recoverSelectedCheckpoint_refines_recoveredPins checkpoint.written checkpoint.represents
      checkpoint.watermark ordered exactTable
  have represented : RepresentsWalHistory after.history abstract := by
    rw [split]
    exact checkpointHistory.append replayed
  refine ⟨suffix, nextReady, extended, retained, next, refined, ?_, by rw [refined.pins, fresh]⟩
  exact represented.preserve clock (UInt64.le_of_eq floor.symm) (refined.rowsBounded nextReady.rowBounds)
    (fun snapshot _ key => by rw [table])

end Alvoki.WAL.Boundary
