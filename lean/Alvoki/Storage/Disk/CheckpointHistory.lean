import Alvoki.Storage.Disk.MarkedCheckpointPublication
import Alvoki.Storage.Disk.WalReplayAgreement
import Alvoki.Storage.Disk.WalReplayProvenance

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
theorem CheckpointForRecovery.of_flushForCheckpoint_history {before checkpoint : PackedTable}
    {model : SnapshotTable UInt64} {history : List WAL.Write}
    (prepared : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (refines : before.Refines model) (represents : RepresentsWalHistory history model)
    (bounded : before.RowBounds) (fits : checkpoint.runs.length < UInt64.size) (generation : UInt64) :
    ∃ after, CheckpointForRecovery (some (Manifest.encode (checkpointHeader checkpoint generation)))
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
