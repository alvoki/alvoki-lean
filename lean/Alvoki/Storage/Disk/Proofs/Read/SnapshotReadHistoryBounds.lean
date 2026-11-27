import Alvoki.Storage.Disk.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotTable Table)

/-- Successful reads record the sequence of a pin acquired at or before
this committed WAL length. A denied read has no snapshot sequence. -/
def RecordedSnapshotRead.BoundedBy (read : RecordedSnapshotRead) (committed : Nat) : Prop :=
  match read with
  | .lookup sequence _ _ | .range sequence _ _ _ => sequence.toNat ≤ committed
  | .lookupDenied _ _ | .rangeDenied _ _ _ => True

theorem RecordedSnapshotRead.BoundedBy.mono {read : RecordedSnapshotRead} {earlier later : Nat}
    (bounded : read.BoundedBy earlier) (ordered : earlier ≤ later) : read.BoundedBy later := by
  cases read <;> simp [RecordedSnapshotRead.BoundedBy] at * <;> omega

private theorem ObservedLocalPin.committedBound
    (observed : ObservedLocalPin directory descriptor writer)
    (ready : writer.RetainedReady directory descriptor) : observed.pin.sequence.toNat ≤ writer.history.length := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have bounded := model.pins_committed observed.pin (refined.pins ▸ observed.active)
  exact represented.committed_count ▸ UInt64.le_iff_toNat_le.mp bounded

theorem RecordedSnapshotRead.Observed.boundedBy {read : RecordedSnapshotRead}
    (observed : RecordedSnapshotRead.Observed directory descriptor writer read)
    (ready : writer.RetainedReady directory descriptor) : read.BoundedBy writer.history.length := by
  cases observed with
  | lookup pin _ | range pin _ => exact pin.committedBound ready
  | lookupDenied | rangeDenied => trivial

/-- The committed bound is established when the reader returns. Later
operations in the observed trace retain the history up to that bound. -/
theorem SegmentedClientReadTrace.responsesBounded
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) :
    ∀ read ∈ reads, read.BoundedBy last.history.length := by
  induction trace with
  | start => simp
  | advance previous step ih =>
    obtain ⟨_, _, history, _⟩ := step.preservesRetained (previous.writes.preservesRetained initialReady).1
    intro read recorded
    apply (ih read recorded).mono
    rw [history, List.length_append]
    omega
  | read previous actual ih =>
    intro read recorded
    rcases List.mem_append.mp recorded with older | newest
    · exact ih read older
    · obtain rfl := List.mem_singleton.mp newest
      exact actual.boundedBy (previous.writes.preservesRetained initialReady).1

/-- An acknowledged suffix cannot change any earlier response whose
snapshot sequence was committed before that suffix. -/
theorem RecordedSnapshotRead.agreesAfterSuffix {read : RecordedSnapshotRead}
    {before after : SnapshotTable UInt64} {history suffix : List WAL.Write}
    (base : SnapshotWalReplay .empty history before) (extended : SnapshotWalReplay before suffix after)
    (bounded : read.BoundedBy history.length) (same : read.agrees before) : read.agrees after := by
  have count : before.committed.toNat = history.length := by
    simpa only [show SnapshotTable.empty.committed.toNat = 0 from rfl, Nat.zero_add] using base.committed_count
  cases read with
  | lookup sequence key value =>
    have supported : sequence ≤ before.committed := UInt64.le_iff_toNat_le.mpr (count.symm ▸ bounded)
    have visible := extended.visibleEntry_before_suffix supported key
    change value = after.table.lookup key sequence
    rw [Table.lookup_eq_visibleEntry, visible, ← Table.lookup_eq_visibleEntry]
    exact same
  | range sequence lo hi entries =>
    have supported : sequence ≤ before.committed := UInt64.le_iff_toNat_le.mpr (count.symm ▸ bounded)
    have stable := Table.range_of_visibleEntry_eq lo hi sequence (extended.visibleEntry_before_suffix supported)
    change entries = after.table.range lo hi sequence
    exact same.trans stable.symm
  | lookupDenied | rangeDenied => exact same

/-- Extend the ledger by the retained part of the next submission. The
old committed snapshots still resolve in the extended replay. -/
theorem PendingClientReplay.appendSelection
    (prior : PendingClientReplay log reads history)
    (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (retains : submission.Retains suffix) (ordered : WAL.OrdinalsFrom 1 (history ++ suffix)) :
    PendingClientReplay (log ++ [submission]) reads (history ++ suffix) ∧
      ∀ read ∈ reads, read.BoundedBy (history ++ suffix).length := by
  obtain ⟨reference, replayed, kept, _, _, agrees⟩ := prior
  obtain ⟨after, replayedAfter⟩ := SnapshotWalReplay.fromEmpty _ ordered
  obtain ⟨previous, earlier, suffix⟩ := replayedAfter.split
  have selected := earlier.deterministic replayed
  subst previous
  have retained := kept.append retains
  refine ⟨⟨after, replayedAfter, retained, retained.orderedSubmissions.1, retained.orderedSubmissions.2, ?_⟩, ?_⟩
  · intro read recorded
    exact read.agreesAfterSuffix replayed suffix (bounded read recorded) (agrees read recorded)
  · intro read recorded
    exact (bounded read recorded).mono (by simp)

/-- Extend the same ledger by its exact acknowledged batch. -/
theorem PendingClientReplay.appendAcknowledged
    (prior : PendingClientReplay log reads history)
    (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (ordered : WAL.OrdinalsFrom 1 (history ++ batch)) :
    PendingClientReplay (log ++ [.acknowledgedBatch batch]) reads (history ++ batch) ∧
      ∀ read ∈ reads, read.BoundedBy (history ++ batch).length :=
  prior.appendSelection bounded (submission := .acknowledgedBatch batch) rfl ordered

/-- An uncertain submission retains either its whole group or none. -/
theorem PendingClientReplay.appendUncertain
    (prior : PendingClientReplay log reads history)
    (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (allowed : selected = history ∨ selected = history ++ batch)
    (ordered : WAL.OrdinalsFrom 1 selected) :
    PendingClientReplay (log ++ [.uncertainBatch batch]) reads selected ∧
      ∀ read ∈ reads, read.BoundedBy selected.length := by
  rcases allowed with rfl | rfl
  · simpa only [List.append_nil] using prior.appendSelection bounded
      (submission := .uncertainBatch batch) (.inl (show ([] : List WAL.Write) = [] from rfl))
      (by simpa only [List.append_nil] using ordered)
  · exact prior.appendSelection bounded (submission := .uncertainBatch batch) (.inr rfl) ordered

end Alvoki.Storage.DiskSession
