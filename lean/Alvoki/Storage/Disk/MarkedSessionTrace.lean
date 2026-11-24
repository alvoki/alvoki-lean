import Alvoki.Storage.Disk.MarkedAdapterRefinement
import Alvoki.Storage.Disk.MarkedReopenStability

namespace Alvoki.WAL.Boundary
open Storage
open scoped List

/-- The checkpoint and its exact durable run bytes stay fixed across this trace. -/
structure FixedMarkedCheckpoint where
  manifest : Option ByteArray
  files : List ByteArray
  image : CheckpointPublication.Image
  walSequence : UInt64
  table : PackedTable
  model : Sequential.SnapshotTable UInt64
  covered : List WAL.Write
  written : CheckpointForRecovery manifest files table
  accepted : image.Accepts walSequence (fun header bytes =>
    CheckpointForRecovery (some (Manifest.encode header)) bytes table) manifest
  represents : table.Refines model
  watermark : covered.length = table.committed.toNat

/-- The acknowledged writes and the final write, if any, whose publication
reported an error. Entries record whole frames, including key and value. -/
structure MarkedSessionWrites where
  acknowledged : List WAL.Write
  ambiguous : Option WAL.Write

def MarkedSessionWrites.submitted (writes : MarkedSessionWrites) : List WAL.Write :=
  writes.acknowledged ++ writes.ambiguous.toList

def MarkedSessionWrites.Retains (writes : MarkedSessionWrites) (suffix : List WAL.Write) : Prop :=
  suffix = writes.acknowledged ∨
    ∃ event, writes.ambiguous = some event ∧ suffix = writes.acknowledged ++ [event]

/-- Account for the surviving suffix in session order. Each session keeps
exactly its acknowledgements and may keep its own ambiguous write once. -/
inductive MarkedSessionRetention : List MarkedSessionWrites → List WAL.Write → Prop where
  | start : MarkedSessionRetention [] []
  | append {sessions : List MarkedSessionWrites} {durable : List WAL.Write}
      {writes : MarkedSessionWrites} {suffix : List WAL.Write}
      (prior : MarkedSessionRetention sessions durable) (one : writes.Retains suffix) :
      MarkedSessionRetention (sessions ++ [writes]) (durable ++ suffix)

theorem MarkedSessionRetention.orderedSubmissions
    (retained : MarkedSessionRetention sessions durable) :
    sessions.flatMap MarkedSessionWrites.acknowledged <+ durable ∧
      durable <+ sessions.flatMap MarkedSessionWrites.submitted := by
  induction retained with
  | start => exact ⟨.slnil, .slnil⟩
  | @append sessions durable writes suffix prior one ih =>
    have bounds : writes.acknowledged <+ suffix ∧ suffix <+ writes.submitted := by
      rcases one with rfl | ⟨event, ambiguous, rfl⟩
      · exact ⟨List.Sublist.refl _, by simp [MarkedSessionWrites.submitted]⟩
      · exact ⟨by simp,
          by simp [MarkedSessionWrites.submitted, ambiguous]⟩
    constructor
    · simpa using ih.1.append bounds.1
    · simpa using ih.2.append bounds.2

/-- Successful modeled open from the given cut. The evidence records the
observed reads and reports and retains the concrete table and file image. -/
inductive MarkedSessionOpen (checkpoint : FixedMarkedCheckpoint)
    (cut : ReopenImage) (table : PackedTable) (after : ReopenImage) : Prop where
  | observed {before : ReopenImage} (attempts : MarkedReopenAttempts cut before)
      (checkpointReads : CheckpointReadObservations checkpoint.image before.directory.active.manifest)
      (walReads : MarkedWalReads before)
      {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
      (opened : runMarkedReopen
        (MarkedReopenReads.mk walReads
          (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
        report false aligned before = .ok table after) :
      MarkedSessionOpen checkpoint cut table after

/-- Recover the verification-only history and exact byte count from the
settled file image. The executable open does not run this second decode. -/
def MarkedWriterState.observeReopen (table : PackedTable) (image : ReopenImage) :
    Option MarkedWriterState := do
  let bytes ← image.wal.active
  let history ← (WAL.decodeOrdinals bytes).toOption
  return ⟨table, bytes.size, image, history⟩

private theorem MarkedWriterState.observeReopen_ready
    {table : PackedTable} {image : ReopenImage} {history : List WAL.Write} {manifest : Option ByteArray}
    (ready : (⟨table, (WAL.encode history).size, image, history⟩ : MarkedWriterState).ReadyFor manifest) :
    observeReopen table image = some ⟨table, (WAL.encode history).size, image, history⟩ := by
  have active : image.wal.active = some (WAL.encode history) := ready.settled.2.2.1
  have ordered : WAL.OrdinalsFrom 1 history := ready.ordered
  simp [observeReopen, active, WAL.decodeOrdinals_encode _ ordered, Except.toOption]

/-- A session performs confirmed writes and either reopens from their settled
files or attempts one more write whose error leads to recovery. In either
case the next session takes the table and files returned by that open. -/
inductive MarkedSessionStep (checkpoint : FixedMarkedCheckpoint) (initial : MarkedWriterState) :
    MarkedSessionWrites → MarkedWriterState → Prop where
  | clean {submitted : List WAL.Write} {writer next : MarkedWriterState}
      {table : PackedTable} {image : ReopenImage}
      (path : AcknowledgedWrites initial submitted writer)
      (opened : MarkedSessionOpen checkpoint writer.image table image)
      (observed : MarkedWriterState.observeReopen table image = some next) :
      MarkedSessionStep checkpoint initial ⟨submitted, none⟩ next
  | interrupted {submitted : List WAL.Write} {writer next : MarkedWriterState}
      {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable table : PackedTable}
      {effects : WriteEffects} {cut image : ReopenImage}
      (path : AcknowledgedWrites initial submitted writer)
      (prepared : prepareWrite writer.table key value = some (event, preparedTable))
      (fits : writer.walBytes + WAL.frameSize < UInt64.size)
      (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
      (opened : MarkedSessionOpen checkpoint cut table image)
      (observed : MarkedWriterState.observeReopen table image = some next) :
      MarkedSessionStep checkpoint initial ⟨submitted, some event⟩ next

/-- The exact checkpoint loader and selected WAL recover the writer's table. -/
def FixedMarkedCheckpoint.RecoveredTable (checkpoint : FixedMarkedCheckpoint)
    (state : MarkedWriterState) : Prop :=
  (checkpoint.manifest.elim (Except.ok PackedTable.empty)
    (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header checkpoint.files) >>= fun base =>
      recoverSelected base (WAL.encode state.history)) = .ok state.table

def FixedMarkedCheckpoint.RecoveredReads (checkpoint : FixedMarkedCheckpoint)
    (state : MarkedWriterState) : Prop :=
  ∃ abstract,
    SnapshotWalReplay checkpoint.model (state.history.drop checkpoint.covered.length) abstract ∧
    abstract.committed.toNat = state.history.length ∧
    ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ state.history.length →
      ∃ pin pinned, state.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
        (∀ lo hi, pinned.range pin.handle lo hi = some (abstract.table.range lo hi snapshot))

theorem MarkedSessionStep.refinesWithReplay {checkpoint : FixedMarkedCheckpoint}
    {initial after : MarkedWriterState}
    {writes : MarkedSessionWrites} {pending : List WAL.Write}
    (step : MarkedSessionStep checkpoint initial writes after)
    (ready : initial.ReadyFor checkpoint.manifest) (start : initial.history = checkpoint.covered ++ pending) :
    ∃ suffix, after.ReadyFor checkpoint.manifest ∧ after.history = initial.history ++ suffix ∧
      writes.Retains suffix ∧ checkpoint.RecoveredTable after ∧ checkpoint.RecoveredReads after := by
  cases step with
  | clean path opened observed =>
    cases opened with
    | observed attempts checkpointReads walReads opened =>
      obtain ⟨abstract, readyAfter, recovered, replay, count, reads⟩ :=
        reopenAfterSettledWrites_refines ready start path attempts checkpoint.accepted
          checkpointReads walReads opened checkpoint.written checkpoint.represents checkpoint.watermark
      have identified := Option.some.inj (observed.symm.trans
        (MarkedWriterState.observeReopen_ready readyAfter))
      subst after
      refine ⟨_, readyAfter, by simp [start, List.append_assoc], Or.inl rfl, recovered, abstract,
        ?_, count, reads⟩
      simpa only [List.append_assoc, List.drop_left] using replay
  | interrupted path prepared fits failed opened observed =>
    cases opened with
    | observed attempts checkpointReads walReads opened =>
      obtain ⟨history, abstract, readyAfter, choice, recovered, replay, count, reads⟩ :=
        reopenAfterAcknowledgedWrites_refines ready start path prepared fits failed attempts
          checkpoint.accepted checkpointReads walReads opened checkpoint.written
          checkpoint.represents checkpoint.watermark
      have identified := Option.some.inj (observed.symm.trans
        (MarkedWriterState.observeReopen_ready readyAfter))
      subst after
      rcases choice with rfl | rfl
      · exact ⟨_, readyAfter, by simp [start], Or.inl rfl, recovered, abstract, replay, count, reads⟩
      · exact ⟨_, readyAfter, by simp [start, List.append_assoc], Or.inr ⟨_, rfl, rfl⟩,
          recovered, abstract, replay, count, reads⟩

theorem MarkedSessionStep.refines {checkpoint : FixedMarkedCheckpoint} {initial after : MarkedWriterState}
    {writes : MarkedSessionWrites} {pending : List WAL.Write}
    (step : MarkedSessionStep checkpoint initial writes after)
    (ready : initial.ReadyFor checkpoint.manifest) (start : initial.history = checkpoint.covered ++ pending) :
    ∃ suffix, after.ReadyFor checkpoint.manifest ∧ after.history = initial.history ++ suffix ∧
      writes.Retains suffix ∧ checkpoint.RecoveredReads after := by
  obtain ⟨suffix, nextReady, extended, retained, _, reads⟩ := step.refinesWithReplay ready start
  exact ⟨suffix, nextReady, extended, retained, reads⟩

/-- A succession of writing and recovery sessions starts from a single
durable checkpoint. The output of each successful recovery is the input of
the next writer. -/
inductive MarkedSessionTrace (checkpoint : FixedMarkedCheckpoint) (initial : MarkedWriterState) :
    List MarkedSessionWrites → MarkedWriterState → Prop where
  | start : MarkedSessionTrace checkpoint initial [] initial
  | step (prior : MarkedSessionTrace checkpoint initial sessions before)
      (one : MarkedSessionStep checkpoint before writes after) :
      MarkedSessionTrace checkpoint initial (sessions ++ [writes]) after

/-- The durable history extends the starting prefix by a suffix accounted for
in session order. Every acknowledgement occurs in the suffix. Every frame
in the suffix comes from a submission. After a recovery, the returned table's
supported snapshot reads agree with abstract replay at the fixed checkpoint. -/
theorem MarkedSessionTrace.refines {checkpoint : FixedMarkedCheckpoint} {initial after : MarkedWriterState}
    {sessions : List MarkedSessionWrites} {pending : List WAL.Write}
    (trace : MarkedSessionTrace checkpoint initial sessions after)
    (ready : initial.ReadyFor checkpoint.manifest) (start : initial.history = checkpoint.covered ++ pending) :
    ∃ durable, after.ReadyFor checkpoint.manifest ∧ after.history = initial.history ++ durable ∧
      MarkedSessionRetention sessions durable ∧
      (sessions ≠ [] → checkpoint.RecoveredReads after) := by
  induction trace with
  | start => exact ⟨[], ready, by simp, .start, fun nonempty => False.elim (nonempty rfl)⟩
  | @step sessions before writes after prior one ih =>
    obtain ⟨durable, readyBefore, history, retained, _⟩ := ih
    have historyBefore : before.history = checkpoint.covered ++ (pending ++ durable) := by
      rw [history, start, List.append_assoc]
    obtain ⟨suffix, readyAfter, extended, survives, reads⟩ := one.refines readyBefore historyBefore
    exact ⟨durable ++ suffix, readyAfter, by rw [extended, history, List.append_assoc],
      .append retained survives, fun _ => reads⟩

end Alvoki.WAL.Boundary
