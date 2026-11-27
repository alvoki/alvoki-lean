import Alvoki.Storage.Table.PackedTable

namespace Alvoki.Storage

open Compaction (CheckedRun)
open Compaction.Model (retentionRowBound)

/-- Consecutive successful calls to the existing single-run rewrite, starting
at the given index. Each call uses the table returned by the previous call. -/
inductive PackedTable.RunRetentionSteps : Nat → Nat → PackedTable → PackedTable → Prop where
  | done (index : Nat) (table : PackedTable) : RunRetentionSteps index 0 table table
  | next {index count before reached after}
      (retained : before.retainRunVersions index = some reached)
      (rest : RunRetentionSteps (index + 1) count reached after) :
      RunRetentionSteps index (count + 1) before after

private theorem retainRunAt {table : PackedTable} (older : List CheckedRun)
    {source output : CheckedRun} {newer : List CheckedRun}
    (runs : table.runs = older ++ source :: newer)
    (written : source.retainVersions table.pins.floor = .ok output) :
    ∃ after, table.retainRunVersions older.length = some after ∧ after.runs = older ++ output :: newer := by
  unfold PackedTable.retainRunVersions
  rw [runs]
  rw [Sequential.replaceSuffix_at_prefix older (replacement := output :: newer)]
  · exact ⟨_, rfl, rfl⟩
  · change (source.retainVersions table.pins.floor).toOption.map (· :: newer) = some (output :: newer)
    simp [written, Except.toOption]

/-- A run rewrite keeps the memory, write clock and whole pin registry.
Consequently every step in the pass uses the original floor. -/
theorem PackedTable.RunRetentionSteps.preservesReads {index count before after}
    (pass : PackedTable.RunRetentionSteps index count before after) :
    after.memory = before.memory ∧ after.committed = before.committed ∧ after.pins = before.pins ∧
      ∀ snapshot, before.pins.floor ≤ snapshot → ∀ key start stop,
        after.lookupAt key snapshot = before.lookupAt key snapshot ∧
        after.rangeAt start stop snapshot = before.rangeAt start stop snapshot := by
  induction pass with
  | done => exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => ⟨rfl, rfl⟩⟩
  | next retained _ ih =>
    obtain ⟨memory, clock, pins, _⟩ := PackedTable.retainRunVersions_spec retained
    obtain ⟨memoryAfter, clockAfter, pinsAfter, readsAfter⟩ := ih
    refine ⟨memoryAfter.trans memory, clockAfter.trans clock, pinsAfter.trans pins, ?_⟩
    intro snapshot supported key start stop
    obtain ⟨point, range⟩ := PackedTable.retainRunVersions_reads retained supported key start stop
    obtain ⟨laterPoint, laterRange⟩ := readsAfter snapshot (pins.symm ▸ supported) key start stop
    exact ⟨laterPoint.trans point, laterRange.trans range⟩

private theorem completeRunRange (older pending newer : List CheckedRun) {before : PackedTable}
    (runs : before.runs = older ++ pending ++ newer) :
    ∃ after outputs,
      PackedTable.RunRetentionSteps older.length pending.length before after ∧
      pending.mapM (·.retainVersions before.pins.floor) = .ok outputs ∧
      after.runs = older ++ outputs ++ newer := by
  induction pending generalizing older before with
  | nil => exact ⟨before, [], .done _ _, rfl, runs⟩
  | cons source rest ih =>
    obtain ⟨output, written⟩ := source.retainVersions_complete before.pins.floor
    have input : before.runs = older ++ source :: (rest ++ newer) := by
      simpa only [List.append_assoc, List.cons_append] using runs
    obtain ⟨reached, retained, nextRuns⟩ := retainRunAt older input written
    have split : reached.runs = (older ++ [output]) ++ rest ++ newer := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using nextRuns
    obtain ⟨after, outputs, restPass, restRetained, endRuns⟩ := ih (older ++ [output]) split
    have pins := (PackedTable.retainRunVersions_spec retained).2.2.1
    rw [pins] at restRetained
    have more : PackedTable.RunRetentionSteps (older.length + 1) rest.length reached after := by
      simpa only [List.length_append, List.length_singleton] using restPass
    refine ⟨after, output :: outputs, .next retained more, ?_, ?_⟩
    · simp [List.mapM_cons, written, restRetained, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using endRuns

private theorem retainedByteSum {inputs outputs : List CheckedRun} {floor : UInt64}
    (written : inputs.mapM (·.retainVersions floor) = .ok outputs) :
    outputs.length = inputs.length ∧
    (outputs.map (·.run.bytes.size)).sum ≤
      16 * inputs.length + 32 * (inputs.map (fun run => retentionRowBound run.history.rows floor)).sum := by
  induction inputs generalizing outputs with
  | nil =>
    obtain rfl := Except.ok.inj written
    simp
  | cons source rest ih =>
    cases head : source.retainVersions floor with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at written
    | ok output =>
      cases tail : rest.mapM (·.retainVersions floor) with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at written
      | ok others =>
        have exact : output :: others = outputs := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using written
        obtain ⟨length, tailBound⟩ := ih tail
        have headBound := CheckedRun.retainVersions_byteSize_le head
        subst outputs
        simp only [List.length_cons, length, List.map_cons, List.sum_cons, Nat.mul_add] at *
        exact ⟨trivial, by omega⟩

/-- A finite maintenance pass can rewrite every run once at the original
floor. The resulting packed payload is bounded by all input rows above the
floor plus one boundary anchor for each represented key in each input run.
The caller schedules this sequence without intervening table changes. -/
theorem PackedTable.completeRunRetention (before : PackedTable) :
    ∃ after, PackedTable.RunRetentionSteps 0 before.runs.length before after ∧
      before.runs.mapM (·.retainVersions before.pins.floor) = .ok after.runs ∧
      after.runs.length = before.runs.length ∧
      (after.runs.map (·.run.bytes.size)).sum ≤
        16 * before.runs.length +
          32 * (before.runs.map (fun run => retentionRowBound run.history.rows before.pins.floor)).sum := by
  obtain ⟨after, outputs, pass, written, exactRuns⟩ := completeRunRange [] before.runs [] (before := before) (by simp)
  simp only [List.nil_append, List.append_nil] at exactRuns
  subst outputs
  exact ⟨after, pass, written, retainedByteSum written⟩

/-- A completed schedule has one endpoint because each rewrite is a
deterministic table operation. -/
theorem PackedTable.RunRetentionSteps.deterministic {index count before after other}
    (first : PackedTable.RunRetentionSteps index count before after)
    (second : PackedTable.RunRetentionSteps index count before other) : after = other := by
  induction first generalizing other with
  | done => cases second; rfl
  | next retained _ ih =>
    cases second with
    | next retained' rest =>
      have same := Option.some.inj (retained.symm.trans retained')
      cases same
      exact ih rest

/-- Every completed pass has the aggregate bound for the reached output. -/
theorem PackedTable.RunRetentionSteps.fullByteSize_le {before after : PackedTable}
    (pass : PackedTable.RunRetentionSteps 0 before.runs.length before after) :
    (after.runs.map (·.run.bytes.size)).sum ≤
      16 * before.runs.length +
        32 * (before.runs.map (fun run => retentionRowBound run.history.rows before.pins.floor)).sum := by
  obtain ⟨expected, ran, _, _, bytes⟩ := before.completeRunRetention
  exact (ran.deterministic pass) ▸ bytes

end Alvoki.Storage
