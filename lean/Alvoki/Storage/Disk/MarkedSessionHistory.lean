import Alvoki.Storage.Disk.CheckpointHistory
import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.RecoveredPinRefinement

namespace Alvoki.WAL.Boundary
open Storage

/-- A writer recovered from exact checkpoint and WAL bytes represents the
same full history as the checkpoint followed by replay of its suffix. Its
abstract model has the pin registry of the actual recovered writer. -/
theorem FixedMarkedCheckpoint.RecoveredTable.refinesHistory
    {checkpoint : FixedMarkedCheckpoint} {writer : MarkedWriterState} {pending : List WAL.Write}
    (recovered : checkpoint.RecoveredTable writer) (ready : writer.ReadyFor checkpoint.manifest)
    (split : writer.history = checkpoint.covered ++ pending)
    (checkpointHistory : RepresentsWalHistory checkpoint.covered checkpoint.model) :
    ∃ model, writer.table.Refines model ∧ RepresentsWalHistory writer.history model ∧
      writer.table.pins.active = [] := by
  have ordered : WAL.OrdinalsFrom 1 (checkpoint.covered ++ pending) := split ▸ ready.ordered
  unfold FixedMarkedCheckpoint.RecoveredTable at recovered
  rw [split] at recovered
  obtain ⟨abstract, next, replayed, refined, table, clock, floor, fresh⟩ :=
    recoverSelectedCheckpoint_refines_recoveredPins checkpoint.written checkpoint.represents
      checkpoint.watermark ordered recovered
  have represented : RepresentsWalHistory writer.history abstract := by
    rw [split]
    exact checkpointHistory.append replayed
  refine ⟨next, refined, ?_, by rw [refined.pins, fresh]⟩
  exact represented.preserve clock (UInt64.le_of_eq floor.symm) (refined.rowsBounded ready.rowBounds)
    (fun snapshot _ key => by rw [table])

/-- A fixed-checkpoint recovery returns the next refined writer, including
the fresh pin registry. Every acknowledgement extends the durable history
in order, and only the final ambiguous event may be dropped. -/
theorem MarkedSessionStep.refinesHistory {checkpoint : FixedMarkedCheckpoint}
    {initial after : MarkedWriterState} {writes : MarkedSessionWrites} {pending : List WAL.Write}
    (step : MarkedSessionStep checkpoint.image.durable initial writes after)
    (ready : initial.ReadyFor checkpoint.manifest) (start : initial.history = checkpoint.covered ++ pending)
    (checkpointHistory : RepresentsWalHistory checkpoint.covered checkpoint.model) :
    ∃ suffix, after.ReadyFor checkpoint.manifest ∧ after.history = initial.history ++ suffix ∧
      writes.Retains suffix ∧ ∃ model, after.table.Refines model ∧
        RepresentsWalHistory after.history model ∧ after.table.pins.active = [] := by
  obtain ⟨suffix, nextReady, extended, retained, exactTable, _⟩ := step.refinesWithReplay ready start
  have split : after.history = checkpoint.covered ++ (pending ++ suffix) := by
    rw [extended, start, List.append_assoc]
  exact ⟨suffix, nextReady, extended, retained, exactTable.refinesHistory nextReady split checkpointHistory⟩

end Alvoki.WAL.Boundary
