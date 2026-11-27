import Alvoki.Storage.Proofs.Table.PackedTableCompaction
import Alvoki.Storage.Proofs.Table.PackedTableLookup
import Alvoki.Storage.Disk.Proofs.Checkpoint.MarkedCheckpointPublication
import Alvoki.Storage.Disk.Proofs.Write.MarkedWriteTrace
import Alvoki.Storage.Disk.Proofs.WAL.WalReplayAgreement
import Alvoki.Storage.Disk.Proofs.WAL.WalReplayProvenance

namespace Alvoki.Storage
open Sequential

/-- A table represents its WAL history when its retained reads and clock
agree with replaying that history from empty. The agreement also covers
future snapshots so it can be used after appending more frames. -/
def RepresentsWalHistory (history : List WAL.Write) (table : SnapshotTable UInt64) : Prop :=
  ∃ reference, SnapshotWalReplay .empty history reference ∧
    table.committed = reference.committed ∧
    table.table.RowsBounded table.committed ∧ reference.table.RowsBounded reference.committed ∧
    ∀ snapshot : UInt64, table.pins.floor ≤ snapshot → ∀ key,
      table.table.visibleEntry key snapshot = reference.table.visibleEntry key snapshot

theorem RepresentsWalHistory.empty : RepresentsWalHistory [] .empty := by
  have bounded : (SnapshotTable.empty : SnapshotTable UInt64).table.RowsBounded 0 := by
    simp [SnapshotTable.empty, Table.RowsBounded, Table.histories, History.empty]
  exact ⟨.empty, .nil _, rfl, bounded, bounded, fun _ _ _ => rfl⟩

theorem RepresentsWalHistory.append {initial after : SnapshotTable UInt64}
    {history suffix : List WAL.Write} (represented : RepresentsWalHistory history initial)
    (applied : SnapshotWalReplay initial suffix after) : RepresentsWalHistory (history ++ suffix) after := by
  obtain ⟨reference, original, clock, bounded, referenceBounded, visible⟩ := represented
  have ordered : WAL.OrdinalsFrom (reference.committed.toNat + 1) suffix := clock ▸ applied.ordinals
  obtain ⟨referenceAfter, continued⟩ := SnapshotWalReplay.of_ordinals reference suffix ordered
  obtain ⟨nextClock, nextBound, referenceNextBound, nextVisible⟩ :=
    applied.visibleEntry_agrees continued clock bounded referenceBounded visible
  refine ⟨referenceAfter, original.append continued, nextClock, nextBound, referenceNextBound, ?_⟩
  intro snapshot retained
  rw [applied.pins] at retained
  exact nextVisible snapshot retained

theorem RepresentsWalHistory.committed_count {table : SnapshotTable UInt64}
    {history : List WAL.Write} (represented : RepresentsWalHistory history table) :
    table.committed.toNat = history.length := by
  obtain ⟨_, replayed, clock, _⟩ := represented
  rw [clock, replayed.committed_count]
  exact Nat.zero_add _

theorem RepresentsWalHistory.preserve {before after : SnapshotTable UInt64}
    {history : List WAL.Write} (represented : RepresentsWalHistory history before)
    (clock : after.committed = before.committed) (floor : before.pins.floor ≤ after.pins.floor)
    (bounded : after.table.RowsBounded after.committed)
    (visible : ∀ snapshot : UInt64, after.pins.floor ≤ snapshot → ∀ key,
      after.table.visibleEntry key snapshot = before.table.visibleEntry key snapshot) :
    RepresentsWalHistory history after := by
  obtain ⟨reference, replayed, sameClock, _, referenceBounded, agrees⟩ := represented
  exact ⟨reference, replayed, clock.trans sameClock, bounded, referenceBounded,
    fun snapshot retained key => (visible snapshot retained key).trans
      (agrees snapshot (UInt64.le_trans floor retained) key)⟩

/-- Preparing the actual new checkpoint retains the entire represented
history, while its manifest and ordered files witness the executable loader. -/
theorem WrittenCheckpoint.of_flushForCheckpoint_history {before checkpoint : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write}
    (prepared : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (refines : before.Refines model) (represents : RepresentsWalHistory history model)
    (bounded : before.RowBounds) (fits : checkpoint.runs.length < UInt64.size) (generation : UInt64) :
    ∃ after, WrittenCheckpoint (checkpointHeader checkpoint generation)
        (checkpoint.runs.map (·.run.bytes)) checkpoint ∧ checkpoint.Refines after ∧
      RepresentsWalHistory (history.take checkpoint.committed.toNat) after := by
  obtain ⟨written, committed, relation⟩ := of_flushForCheckpoint
    prepared refines fits bounded.runs bounded.memory generation
  have count : checkpoint.committed.toNat = history.length := by
    rw [committed, refines.committed, represents.committed_count]
  let after := if before.memory.rows.isEmpty then model else model.flush
  have stableClock : after.committed = model.committed := by unfold after; split <;> rfl
  have stableFloor : after.pins.floor = model.pins.floor := by unfold after; split <;> rfl
  have sameEntries (snapshot key : UInt64) :
      after.table.visibleEntry key snapshot = model.table.visibleEntry key snapshot := by
    unfold after
    split
    · rfl
    · simp only [SnapshotTable.flush, Table.visibleEntry, Table.flush, Table.histories]
      rw [across_append_empty]
  refine ⟨after, written, relation, ?_⟩
  rw [count, List.take_length]
  exact represents.preserve stableClock (UInt64.le_of_eq stableFloor.symm)
    (relation.rowsBounded written.rowBounds) (fun snapshot _ key => sameEntries snapshot key)

theorem CheckpointForRecovery.of_flushForCheckpoint_history {before checkpoint : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write}
    (prepared : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (refines : before.Refines model) (represents : RepresentsWalHistory history model)
    (bounded : before.RowBounds) (fits : checkpoint.runs.length < UInt64.size) (generation : UInt64) :
    ∃ after, CheckpointForRecovery (some (Manifest.encode (checkpointHeader checkpoint generation)))
        (checkpoint.runs.map (·.run.bytes)) checkpoint ∧ checkpoint.Refines after ∧
      RepresentsWalHistory (history.take checkpoint.committed.toNat) after := by
  obtain ⟨after, written, refined, represented⟩ := WrittenCheckpoint.of_flushForCheckpoint_history
    prepared refines represents bounded fits generation
  exact ⟨after, written.legacy, refined, represented⟩

theorem RepresentsWalHistory.reads {table reference : SnapshotTable UInt64}
    {history : List WAL.Write} (represented : RepresentsWalHistory history table)
    (replayed : SnapshotWalReplay .empty history reference) {snapshot : UInt64}
    (retained : table.pins.floor ≤ snapshot) :
    (∀ key, table.table.lookup key snapshot = reference.table.lookup key snapshot) ∧
    ∀ start stop, table.table.range start stop snapshot = reference.table.range start stop snapshot := by
  obtain ⟨expected, historyReplay, _, _, _, visible⟩ := represented
  have same := replayed.deterministic historyReplay
  subst expected
  refine ⟨?_, fun start stop => Table.range_of_visibleEntry_eq start stop snapshot (visible snapshot retained)⟩
  intro key
  rw [Table.lookup_eq_visibleEntry, Table.lookup_eq_visibleEntry, visible snapshot retained key]

theorem RepresentsWalHistory.packedPinnedReads {table : PackedTable} {model reference : SnapshotTable UInt64}
    {history : List WAL.Write} (represented : RepresentsWalHistory history model) (refines : table.Refines model)
    (replayed : SnapshotWalReplay .empty history reference) {pin : SnapshotPin}
    (active : pin ∈ table.pins.active) :
    (∀ key, table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
    ∀ start stop, table.range pin.handle start stop = some (reference.table.range start stop pin.sequence) := by
  have member : pin ∈ model.pins.active := refines.pins ▸ active
  obtain ⟨lookup, range⟩ := represented.reads replayed (model.pins.safe pin member)
  exact ⟨fun key => by rw [PackedTable.lookup_refines refines, model.lookup_pinned member, lookup],
    fun start stop => by rw [PackedTable.range_refines refines, model.range_pinned member, range]⟩

/-- Canonical replay of a WAL extension preserves reads at every sequence
already pinned by the preceding table, when the later table supports it. -/
theorem RepresentsWalHistory.packedPinnedReadsAfterAppend {before after : PackedTable}
    {beforeModel afterModel reference : SnapshotTable UInt64} {history suffix : List WAL.Write}
    (previous : RepresentsWalHistory history beforeModel)
    (next : RepresentsWalHistory (history ++ suffix) afterModel)
    (beforeRefines : before.Refines beforeModel) (afterRefines : after.Refines afterModel)
    (replayed : SnapshotWalReplay .empty (history ++ suffix) reference) {oldPin newPin : SnapshotPin}
    (oldActive : oldPin ∈ before.pins.active) (newActive : newPin ∈ after.pins.active)
    (sameSequence : newPin.sequence = oldPin.sequence) :
    (∀ key, after.lookup newPin.handle key = before.lookup oldPin.handle key) ∧
    ∀ start stop, after.range newPin.handle start stop = before.range oldPin.handle start stop := by
  obtain ⟨base, original, continued⟩ := replayed.split
  obtain ⟨oldLookup, oldRange⟩ := previous.packedPinnedReads beforeRefines original oldActive
  obtain ⟨newLookup, newRange⟩ := next.packedPinnedReads afterRefines replayed newActive
  have clock : beforeModel.committed = base.committed := by
    apply UInt64.toNat_inj.mp
    rw [previous.committed_count, original.committed_count]
    exact (Nat.zero_add _).symm
  have supported : oldPin.sequence ≤ base.committed :=
    clock ▸ beforeModel.pins_committed oldPin (beforeRefines.pins ▸ oldActive)
  have visible := continued.visibleEntry_before_suffix supported
  refine ⟨?_, ?_⟩
  · intro key
    rw [oldLookup, newLookup, sameSequence, Table.lookup_eq_visibleEntry,
      Table.lookup_eq_visibleEntry, visible key]
  · intro start stop
    rw [oldRange, newRange, sameSequence, Table.range_of_visibleEntry_eq start stop _ visible]

/-- Pins change the registry while preserving the represented table history. -/
theorem RepresentsWalHistory.acquireAt {before after : PackedTable} {model : SnapshotTable UInt64}
    {history : List WAL.Write} {snapshot : UInt64} {pin : SnapshotPin}
    (represented : RepresentsWalHistory history model) (refines : before.Refines model)
    (bounded : before.RowBounds) (acquired : before.acquireAt snapshot = some (pin, after)) :
    ∃ result, after.Refines result ∧ RepresentsWalHistory history result := by
  obtain ⟨result, selected, refined⟩ := PackedTable.acquireAt_refines refines acquired
  refine ⟨result, refined, ?_⟩
  unfold SnapshotTable.acquireAt at selected
  split at selected
  · contradiction
  · rename_i accepted
    cases selected
    obtain ⟨_, _, _, _, _, _, floor⟩ := SnapshotPins.acquire_spec accepted
    exact represented.preserve rfl (UInt64.le_of_eq floor.symm)
      (refined.rowsBounded (bounded.acquireAt acquired)) (fun _ _ _ => rfl)

/-- A supported acquisition preserves the WAL representation, so the
new pin reads from the same replay as the table before acquisition. -/
theorem RepresentsWalHistory.acquireReads {table : PackedTable} {model reference : SnapshotTable UInt64}
    {history : List WAL.Write} (represented : RepresentsWalHistory history model)
    (refined : table.Refines model) (bounded : table.RowBounds)
    (replayed : SnapshotWalReplay .empty history reference) {snapshot : UInt64}
    (floor : table.pins.floor ≤ snapshot) (committed : snapshot ≤ table.committed) :
    ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
      (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
      ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  have available : (table.acquireAt snapshot).isSome = true := by
    simpa only [PackedTable.acquireAt, Option.isSome_map] using
      (SnapshotPins.acquire_iff table.pins _ _).mpr ⟨floor, committed⟩
  obtain ⟨⟨pin, pinned⟩, acquired⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨_, pinnedRefined, pinnedHistory⟩ := represented.acquireAt refined bounded acquired
  have pinSpec := PackedTable.acquireAt_spec acquired
  exact ⟨pin, pinned, acquired,
    by simpa only [pinSpec.sequence] using pinnedHistory.packedPinnedReads pinnedRefined replayed pinSpec.active⟩

theorem RepresentsWalHistory.release {model : SnapshotTable UInt64} {history : List WAL.Write}
    (represented : RepresentsWalHistory history model) (handle : SnapshotHandle) :
    RepresentsWalHistory history (model.release handle) := by
  obtain ⟨reference, replayed, clock, bounded, referenceBounded, visible⟩ := represented
  exact ⟨reference, replayed, clock, bounded, referenceBounded, visible⟩

/-- Advancing the live floor keeps the clock and rows and narrows the
snapshots for which the table must agree with the same WAL. -/
theorem RepresentsWalHistory.advanceFloor {before after : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write} {floor : UInt64}
    (represented : RepresentsWalHistory history model) (refines : before.Refines model)
    (bounded : before.RowBounds) (advanced : before.advanceFloor floor = some after) :
    ∃ result, model.advanceFloor floor = some result ∧ after.Refines result ∧
      RepresentsWalHistory history result := by
  obtain ⟨result, moved, refined⟩ := PackedTable.advanceFloor_refines refines advanced
  refine ⟨result, moved, refined, ?_⟩
  unfold SnapshotTable.advanceFloor at moved
  split at moved
  · split at moved
    · contradiction
    · rename_i changed
      cases moved
      exact represented.preserve rfl (SnapshotPins.advance_spec changed).1
        (refined.rowsBounded (bounded.advanceFloor advanced)) (fun _ _ _ => rfl)
  · contradiction

/-- Compaction retains the same WAL history. At every snapshot supported
by the live floor, the compacted runs have the same winning entry. -/
theorem RepresentsWalHistory.compact {before after : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write} {index : Nat}
    (represented : RepresentsWalHistory history model) (refines : before.Refines model)
    (bounded : before.RowBounds) (compacted : before.compact index = some after) :
    ∃ result, model.compact index = some result ∧ after.Refines result ∧
      RepresentsWalHistory history result := by
  obtain ⟨result, merged, refined⟩ := PackedTable.compact_refines refines compacted
  refine ⟨result, merged, refined, ?_⟩
  unfold SnapshotTable.compact at merged
  obtain ⟨_, changed, rfl⟩ := Option.map_eq_some_iff.mp merged
  refine represented.preserve rfl (UInt64.le_refl _)
    (refined.rowsBounded (bounded.compact compacted)) ?_
  intro snapshot retained key
  simp only [Table.visibleEntry]
  rw [Table.compactAt_winner changed retained key]

/-- Retaining versions within one run changes the represented run history
while preserving the committed clock and every supported visible entry. -/
theorem RepresentsWalHistory.retainRunVersions {before after : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write} {index : Nat}
    (represented : RepresentsWalHistory history model) (refines : before.Refines model)
    (bounded : before.RowBounds) (retained : before.retainRunVersions index = some after) :
    ∃ result, after.Refines result ∧ RepresentsWalHistory history result := by
  obtain ⟨memory, clock, pins, _⟩ := PackedTable.retainRunVersions_spec retained
  obtain ⟨result, table, modelClock, modelPins⟩ := model.exists_replaceRuns after.describe.runs
  have sameMemory : after.describe.memory = model.table.memory :=
    memory.trans (congrArg Table.memory refines.table)
  have described : after.describe = result.table := by
    rw [table, ← sameMemory]
  have refined : after.Refines result :=
    ⟨described, clock.trans (refines.committed.trans modelClock.symm), pins.trans (refines.pins.trans modelPins.symm)⟩
  refine ⟨result, refined, represented.preserve modelClock (by rw [modelPins]; exact UInt64.le_refl _)
    (refined.rowsBounded (bounded.retainRunVersions retained)) ?_⟩
  intro snapshot supported key
  have aboveFloor : before.pins.floor ≤ snapshot := by rwa [refines.pins, ← modelPins]
  rw [← refined.table, ← refines.table]
  exact PackedTable.retainRunVersions_visibleEntry retained aboveFloor key

namespace CheckpointPublication
open WAL.Boundary

/-- If each admitted checkpoint represents its covered prefix, a successful
reopen after checkpoint cuts reads as replaying the whole original WAL.
The retained floor comes from whichever checkpoint was actually loaded. -/
theorem checkpointMarkedRetry_reopen_canonical {initial published : Image}
    {before reopenStart after : ReopenImage} {manifest : Option ByteArray}
    {history : List WAL.Write} {table : PackedTable} {reference : SnapshotTable UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint model, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
        checkpoint.Refines model ∧ RepresentsWalHistory (history.take checkpoint.committed.toNat) model)
    (checkpoints : Retry history.length.toUInt64 expected initial published)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopenStart)
    (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
    (walReads : MarkedWalReads reopenStart)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    (opened : runMarkedReopen
      (MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned reopenStart = .ok table after)
    (canonical : SnapshotWalReplay .empty history reference) :
    after.SettledFor reopenStart.directory.active.manifest history ∧
      table.committed.toNat = history.length ∧
      ∃ files checkpoint,
        CheckpointForRecovery reopenStart.directory.active.manifest files checkpoint ∧
        published.readDurableCheckpointRuns reopenStart.directory.active.manifest = some files ∧
        ∀ snapshot : UInt64, checkpoint.pins.floor ≤ snapshot → snapshot.toNat ≤ history.length →
          ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
            (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
            (∀ start stop, pinned.range pin.handle start stop =
              some (reference.table.range start stop snapshot)) := by
  obtain ⟨settledAfter, _, count, files, checkpoint, _, _, abstract, written, durable, _, _, _, _, _,
      covered, replayed, _, floor, reads⟩ := checkpointMarkedRetry_reopen_refines settled projects fits
        ordered initialValid RepresentsWalHistory.empty witness checkpoints attempts checkpointReads walReads opened
  have fullHistory : RepresentsWalHistory history abstract := by
    simpa only [List.take_append_drop] using covered.append replayed
  refine ⟨settledAfter, count, files, checkpoint, written, durable, ?_⟩
  intro snapshot retained supported
  obtain ⟨lookup, range⟩ := fullHistory.reads canonical (floor.symm ▸ retained)
  obtain ⟨pin, pinned, acquired, observedLookup, observedRange⟩ := reads snapshot retained supported
  exact ⟨pin, pinned, acquired, fun key => by rw [observedLookup, lookup],
    fun start stop => by rw [observedRange, range]⟩

end CheckpointPublication
end Alvoki.Storage

namespace Alvoki.WAL.Boundary
open Storage

/-- Acknowledged writes carry the same WAL-history relation into the exact
writer table that will supply the next checkpoint. -/
theorem AcknowledgedWrites.refinesHistory {initial after : MarkedWriterState}
    {manifest : Option ByteArray} {submitted : List WAL.Write}
    {model : Sequential.SnapshotTable UInt64}
    (path : AcknowledgedWrites initial submitted after) (ready : initial.ReadyFor manifest)
    (refines : initial.table.Refines model) (history : RepresentsWalHistory initial.history model) :
    after.ReadyFor manifest ∧ after.history = initial.history ++ submitted ∧
      ∃ next, SnapshotWalReplay model submitted next ∧ after.table.Refines next ∧
        RepresentsWalHistory after.history next := by
  obtain ⟨nextReady, extended, replayed⟩ := path.refines ready
  obtain ⟨next, written, refined⟩ := replay_refines refines replayed
  refine ⟨nextReady, extended, next, written, refined, ?_⟩
  rw [extended]
  exact history.append written

end Alvoki.WAL.Boundary
