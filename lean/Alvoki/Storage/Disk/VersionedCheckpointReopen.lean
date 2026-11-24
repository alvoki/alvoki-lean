import Alvoki.Storage.Disk.VersionedCheckpointRetry
import Alvoki.Storage.Disk.VersionedMarkedRecovery
import Alvoki.Storage.Disk.MarkedReopenStability
import Alvoki.Storage.Disk.LockedMarkedRead
import Alvoki.Storage.Disk.LockedRecoveryReads
import Alvoki.Storage.Disk.LockedVersionedCheckpointRead

namespace Alvoki.Storage.CheckpointPublication
open WAL.Boundary Manifest

/-- Pair each selectable checkpoint with the same settled marker under which
it was published. This statement is independent of the manifest decoder. -/
private theorem Image.markedPair {image : Image} {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (settled : before.SettledFor manifest history) {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ (image.markedReopenImage before).directory.active ::
      (image.markedReopenImage before).directory.crashImages) :
    pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      (image.manifest.active = pair.manifest ∨ pair.manifest ∈ image.manifest.crashImages) := by
  rcases List.mem_cons.mp chosen with rfl | crash
  · exact ⟨congrArg DirectoryPublication.Bindings.walBoundary settled.1, .inl rfl⟩
  · obtain ⟨candidate, survives, rfl⟩ := List.mem_map.mp crash
    exact ⟨congrArg DirectoryPublication.Bindings.walBoundary settled.1, .inr survives⟩

/-- Versioned checkpoint retries followed by marked reopen attempts still
select a checkpoint covered by the original WAL. Successful read reports
then supply the exact old or new manifest and WAL to the shared open. -/
theorem VersionedRetry.markedReadInputs {initial published : Image}
    {before reopen : ReopenImage} {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Checkpoint → List ByteArray → Prop}
    (checkpoints : VersionedRetry history.length.toUInt64 expected initial published)
    (valid : initial.ValidVersioned history.length.toUInt64 expected)
    (settled : before.SettledFor manifest history)
    (fits : (WAL.encode history).size < UInt64.size)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopen) :
    published.AcceptsVersioned history.length.toUInt64 expected reopen.directory.active.manifest ∧
      reopen.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      reopen.wal.active = some (WAL.encode history) := by
  let lifted := published.markedReopenImage before
  have markers (pair : DirectoryPublication.Bindings)
      (chosen : pair ∈ lifted.directory.active :: lifted.directory.crashImages) :
      pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) :=
    (published.markedPair settled chosen).1
  have bound : MarkerBound lifted.directory :=
    ⟨_, _, markers _ (List.mem_cons_self ..), WAL.Boundary.decode_encode _, fun pair chosen =>
      ⟨_, _, markers pair chosen, WAL.Boundary.decode_encode _, Nat.le_refl _⟩⟩
  have path := attempts.toRetry bound
  obtain ⟨marker, manifestChoice⟩ := published.markedPair settled
    (path.chosen_pair_from_initial (List.mem_cons_self ..))
  have originalWal : lifted.wal.Valid (· = some (WAL.encode history)) := by
    obtain ⟨_, _, active, choices⟩ := settled
    change before.wal.Valid (· = some (WAL.encode history))
    refine ⟨by simp [choices], active, ?_⟩
    intro candidate survives
    exact (List.mem_singleton.mp (choices ▸ survives)).trans active
  exact ⟨checkpoints.accepts valid manifestChoice, marker,
    (path.preserves_exactWal markers originalWal fits).activeValid⟩

/-- Derive the exact marked installer arguments from one mixed-format
checkpoint and reopen trace that selects a present manifest. The I/O
premises concern the reported reads and aligned durability step. -/
theorem VersionedRetry.completes_marked {initial published : Image} {before reopen : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write} {bytes : ByteArray}
    (checkpoints : VersionedRetry history.length.toUInt64 (CheckpointRepresentsPrefix history) initial published)
    (valid : initial.ValidVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history))
    (settled : before.SettledFor manifest history)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopen)
    (visible : reopen.directory.active.manifest = some bytes)
    (reads : VersionedCheckpointFileReads published.durable (some bytes))
    (manifestRead : reads.readManifest = .ok (some bytes))
    (runReads : ∀ selected, VersionedCheckpoint.decode bytes = .ok selected →
      ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (walReads : MarkedWalReads reopen)
    (markerRead : walReads.marker = .ok reopen.directory.active.walBoundary)
    (walRead : walReads.wal = .ok reopen.wal.active)
    (report : Publication.Step → RepairReport) :
    ∃ selected files base table model, VersionedCheckpoint.decode bytes = .ok selected ∧
      (List.range selected.header.runCount.toNat).mapM
        (published.durable selected.header.generation) = some files ∧
      selected.ValidatesFiles files ∧ loadRunSet selected.header files = .ok base ∧
      replay base (history.drop selected.header.committed.toNat) = .ok table ∧
      runSharedMarkedOpen reads.result walReads.marker walReads.wal report .success reopen =
        .ok (table, selected.header.generation, (WAL.encode history).size) reopen.syncDirectory ∧
      reopen.syncDirectory.SettledFor (some bytes) history ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨accepted, marker, wal⟩ := checkpoints.markedReadInputs valid settled fits attempts
  rw [visible] at accepted
  have decodedWitness := accepted
  obtain ⟨selected, decoded, _⟩ := decodedWitness
  obtain ⟨files, base, table, durable, checked, loaded, _, replayed, opened, next, _, bounded, model, refined, history, pins⟩ :=
    WAL.Boundary.VersionedCheckpointFileReads.completes_marked reads visible decoded accepted manifestRead
      (runReads selected decoded) walReads (marker ▸ markerRead) (wal ▸ walRead) fits ordered report
  exact ⟨selected, files, base, table, model, decoded, durable, checked, loaded, replayed, opened, next,
    bounded, refined, history, pins⟩

/-- The installer uses the manifest that actually survived the retries. If
the first checkpoint was lost, the entire WAL is replayed at generation zero. -/
theorem VersionedRetry.installs_marked {initial published : Image} {before reopen : ReopenImage}
    {manifest selectedManifest : Option ByteArray} {history : List WAL.Write}
    (checkpoints : VersionedRetry history.length.toUInt64 (CheckpointRepresentsPrefix history) initial published)
    (valid : initial.ValidVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history))
    (settled : before.SettledFor manifest history)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopen)
    (visible : reopen.directory.active.manifest = selectedManifest)
    (reads : VersionedCheckpointFileReads published.durable selectedManifest)
    (manifestRead : reads.readManifest = .ok selectedManifest)
    (runReads : ∀ bytes selected, selectedManifest = some bytes → VersionedCheckpoint.decode bytes = .ok selected →
      ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (walReads : MarkedWalReads reopen)
    (markerRead : walReads.marker = .ok reopen.directory.active.walBoundary)
    (walRead : walReads.wal = .ok reopen.wal.active)
    (report : Publication.Step → RepairReport) :
    ∃ table generation model,
      ((selectedManifest.mapM fun bytes => (VersionedCheckpoint.decode bytes).map (·.header.generation)).map
        (·.getD 0) : Except String UInt64) = .ok generation ∧
      runSharedMarkedOpen reads.result walReads.marker walReads.wal report .success reopen =
        .ok (table, generation, (WAL.encode history).size) reopen.syncDirectory ∧
      reopen.syncDirectory.SettledFor selectedManifest history ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] := by
  cases selectedManifest with
  | none =>
    obtain ⟨_, marker, wal⟩ := checkpoints.markedReadInputs valid settled fits attempts
    obtain ⟨table, model, _, opened, next, bounded, refined, represented, pins⟩ :=
      WAL.Boundary.VersionedCheckpointFileReads.completes_marked_absent reads visible manifestRead
        walReads (marker ▸ markerRead) (wal ▸ walRead) fits ordered report
    exact ⟨table, 0, model, rfl, opened, next, bounded, refined, represented, pins⟩
  | some bytes =>
    obtain ⟨selected, _, _, table, model, decoded, _, _, _, _, opened, next, bounded, refined, represented, pins⟩ :=
      checkpoints.completes_marked valid settled fits ordered attempts visible reads manifestRead
        (fun selected decoded => runReads bytes selected rfl decoded) walReads markerRead walRead report
    refine ⟨table, selected.header.generation, model, ?_, opened, next, bounded, refined, represented, pins⟩
    simp [Option.mapM, decoded, Functor.map, Except.map]

/-- Use concrete locked path reports for the dual-format checkpoint read
and the same outer lock and marked installer schedule as the native adapter.
The native v2 reader uses the integrity case and the absent-manifest case. -/
theorem VersionedRetry.installs_marked_locked {initial published : Image} {before reopen : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (checkpoints : VersionedRetry history.length.toUInt64 (CheckpointRepresentsPrefix history) initial published)
    (valid : initial.ValidVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history))
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopen)
    {dir : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners dir (.ok true))
    {reports : OpenPathReadReports}
    (observes : (owners.set (dir.file .lock) (some descriptor)).Owns dir descriptor →
      reports.ObservesVersioned dir reopen published.durable)
    (manifestRead : ∃ value, reports.readOptional (dir.file .manifest) = .ok value)
    (runReads : ∀ bytes selected, reopen.directory.active.manifest = some bytes →
      VersionedCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, reports.readBin (dir.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ value, reports.readOptional (dir.file .walBoundary) = .ok value)
    (walRead : ∃ value, reports.readOptional (dir.file .wal) = .ok value)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let acquiredOwners := owners.set (dir.file .lock) (some descriptor)
    let held : acquiredOwners.Owns dir descriptor := by
      simp [DiskSession.LockOwners.Owns, DiskSession.LockOwners.set, acquiredOwners]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let recovered := runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report .success reopen
    initial.markedReopenImage before = before ∧ ∃ table generation model,
      ((reopen.directory.active.manifest.mapM fun bytes =>
        (VersionedCheckpoint.decode bytes).map (·.header.generation)).map
        (·.getD 0) : Except String UInt64) = .ok generation ∧
      DiskSession.runLockedMarkedOpen dir descriptor (.ok true) unlock cause recovered owners =
        .ok ((table, generation, (WAL.encode history).size), reopen.syncDirectory) acquiredOwners ∧
      owners (dir.file .lock) = none ∧ acquiredOwners.Owns dir descriptor ∧
      (⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩ : MarkedWriterState).ReadyFor
        reopen.directory.active.manifest ∧
      MarkedWriterState.observeReopen table reopen.syncDirectory =
        some ⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩ ∧
      table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  intro acquiredOwners held checkpointReads walReads recovered
  refine ⟨initial.markedReopenImage_start settled projects, ?_⟩
  have observedManifest := VersionedCheckpointFileReads.ofLockedPaths_manifest_success held observes manifestRead
  have observedRuns bytes selected visible decoded index within :=
    (runReads bytes selected visible decoded index within).imp
      (fun _ => VersionedCheckpointFileReads.ofLockedPaths_run_success held observes)
  have observedMarker : walReads.marker = .ok reopen.directory.active.walBoundary :=
    observedOptional_success markerRead (fun value read => (walReads.markerVisible value read).symm)
  have observedWal : walReads.wal = .ok reopen.wal.active :=
    observedOptional_success walRead (fun value read => (walReads.walVisible value read).symm)
  obtain ⟨table, generation, model, decoded, opened, next, bounded, refined, represented, pins⟩ :=
    checkpoints.installs_marked valid settled fits ordered attempts rfl checkpointReads
      observedManifest observedRuns walReads observedMarker observedWal report
  have outer : DiskSession.runOpen dir descriptor (.ok true)
      (.ok ((table, generation, (WAL.encode history).size), reopen.syncDirectory)) unlock owners =
        .ok ((table, generation, (WAL.encode history).size), reopen.syncDirectory) acquiredOwners := rfl
  have previous := (DiskSession.runOpen_success acquisition outer).1
  have installed : DiskSession.runLockedMarkedOpen dir descriptor (.ok true) unlock cause recovered owners =
      .ok ((table, generation, (WAL.encode history).size), reopen.syncDirectory) acquiredOwners := by
    change DiskSession.runLockedMarkedOpen dir descriptor (.ok true) unlock cause
      (runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report .success reopen) owners = _
    rw [opened]
    exact outer
  have count : history.length = table.committed.toNat := by
    rw [refined.committed, represented.committed_count]
  have ready : (⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩ : MarkedWriterState).ReadyFor
      reopen.directory.active.manifest :=
    ⟨next, ordered, count, rfl, fits, bounded⟩
  exact ⟨table, generation, model, decoded, installed, previous, held, ready,
    MarkedWriterState.observeReopen_ready ready,
    refined, represented, pins⟩

end Alvoki.Storage.CheckpointPublication
