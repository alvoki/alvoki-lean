import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.WAL.Boundary
open Storage

/-- The ready writer's table and byte count, together with its modeled
physical files and the history witnessing the WAL's contents. -/
structure MarkedWriterState where
  table : PackedTable
  walBytes : Nat
  image : ReopenImage
  history : List WAL.Write

structure MarkedWriterState.ReadyFor (state : MarkedWriterState)
    (manifest : Option ByteArray) : Prop where
  settled : state.image.SettledFor manifest state.history
  ordered : WAL.OrdinalsFrom 1 state.history
  count : state.history.length = state.table.committed.toNat
  length : state.walBytes = (WAL.encode state.history).size
  fits : state.walBytes < UInt64.size

/-- A sequence of reported successes in one ready session. Every operation
receives the physical output and the prepared in-memory table of the
preceding operation. The trace lists the frames it acknowledged. -/
inductive AcknowledgedWrites (initial : MarkedWriterState) :
    List WAL.Write → MarkedWriterState → Prop where
  | start : AcknowledgedWrites initial [] initial
  | write {submitted : List WAL.Write} {before : MarkedWriterState}
      {key : UInt64} {value : Option UInt64} {event : WAL.Write} {table : PackedTable}
      {effects : WriteEffects} {image : ReopenImage}
      (path : AcknowledgedWrites initial submitted before)
      (prepared : prepareWrite before.table key value = some (event, table))
      (fits : before.walBytes + WAL.frameSize < UInt64.size)
      (acknowledged : runWriteEffectsFrom before.history event effects before.image = .ok () image) :
      AcknowledgedWrites initial (submitted ++ [event])
        ⟨table, before.walBytes + WAL.frameSize, image, before.history ++ [event]⟩

/-- A ready session can take any number of acknowledged writes. Its exact
durable history extends by those writes in order, and replaying them gives
the table and committed count installed by the session. -/
theorem AcknowledgedWrites.refines {initial after : MarkedWriterState}
    {manifest : Option ByteArray} {submitted : List WAL.Write}
    (path : AcknowledgedWrites initial submitted after) (ready : initial.ReadyFor manifest) :
    after.ReadyFor manifest ∧ after.history = initial.history ++ submitted ∧
      replay initial.table submitted = .ok after.table := by
  induction path with
  | start => exact ⟨ready, by simp, rfl⟩
  | @write submitted before key value event table effects image path prepared fits acknowledged ih =>
    obtain ⟨prior, history, replayed⟩ := ih
    obtain ⟨_, count, ordered, _, length⟩ := prepareWrite_extends_history prior.ordered prior.count prepared
    refine ⟨⟨runWriteEffectsFrom_success prior.settled acknowledged, ordered, ?_, ?_, fits⟩, ?_, ?_⟩
    · simp [count]
    · simp [length, prior.length]
    · simp [history, List.append_assoc]
    · rw [replay_append replayed]
      simp [replay, replay_prepared prepared]

end Alvoki.WAL.Boundary
