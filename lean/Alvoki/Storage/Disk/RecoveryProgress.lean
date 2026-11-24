import Alvoki.Storage.Disk.FreshMarkedBootstrap
import Alvoki.Storage.Disk.LegacyBootstrapRetry
import Alvoki.Storage.Disk.MarkedCheckpointReopenProgress
import Alvoki.Storage.Disk.MarkedWriteReopenProgress

namespace Alvoki.WAL.Boundary

open Storage CheckpointPublication

/-- The locked reads for one attempt. A successful manifest lookup can
observe absence. Only the selected manifest's run indices must be readable. -/
structure RecoveryReads (image : Image) (before : ReopenImage) (manifest : Option ByteArray) where
  checkpointReads : CheckpointReadObservations image manifest
  walReads : MarkedWalReads before
  readManifest : checkpointReads.readManifest = .ok manifest
  readRuns : ∀ bytes header, manifest = some bytes →
    Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
      ∃ payload, checkpointReads.readRun header.generation index = .ok payload
  readMarker : walReads.marker = .ok before.directory.active.walBoundary
  readWal : walReads.wal = .ok before.wal.active

/-- Evidence before the final open. Each case identifies the interpreter
whose success must be proved and supplies that branch's required reports.
The last two indices specify the selected manifest and admissible histories. -/
inductive RecoveryBoundary :
    ((PackedTable × UInt64 × Nat) → ReopenImage → Prop) →
    Option ByteArray → (List WAL.Write → Prop) → Prop where
  | empty {image : Image} {before : ReopenImage}
      (reads : RecoveryReads image before before.directory.active.manifest)
      (valid : before.EmptyBootstrapValid) (reports : FreshOpenReports)
      (created : before.wal.active = none → reports.createWal = .ok ())
      (synced : reports.syncWalDirectory = .ok ())
      (published : before.directory.active.walBoundary = none → ∀ step, reports.marker step = .ok ()) :
      RecoveryBoundary
        (fun installed after =>
          (runFreshMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal reports).run before =
            .ok (installed, after)) none (· = [])
  | legacy {before : ReopenImage} {events : List WAL.Write} (fixed : FixedMarkedCheckpoint)
      (reads : RecoveryReads fixed.image before fixed.manifest)
      (valid : before.LegacyBootstrapValid fixed.manifest events)
      (covered : fixed.table.committed.toNat ≤ events.length)
      (fits : (WAL.encode events).size < UInt64.size) (reports : LegacyOpenReports)
      (success : match before.directory.active.walBoundary with
        | none => ∀ bytes, before.wal.active = some bytes → reports.Succeeds bytes.size (WAL.encode events).size
        | some _ => reports.aligned = .success) :
      RecoveryBoundary
        (fun installed after => ∃ loaded marker contents, reads.checkpointReads.result = .ok loaded ∧
          reads.walReads.marker = .ok marker ∧ reads.walReads.wal = .ok (some contents) ∧
          runLegacyRetryOpen loaded marker contents reports before = .ok installed after)
        fixed.manifest (· = events)
  | settled {initial before : ReopenImage} {pending : List WAL.Write} (fixed : FixedMarkedCheckpoint)
      (reads : RecoveryReads fixed.image before before.directory.active.manifest)
      (settled : initial.SettledFor fixed.manifest (fixed.covered ++ pending))
      (fits : (WAL.encode (fixed.covered ++ pending)).size < UInt64.size)
      (ordered : WAL.OrdinalsFrom 1 (fixed.covered ++ pending))
      (attempts : MarkedReopenAttempts initial before) (report : Publication.Step → RepairReport) :
      RecoveryBoundary
        (fun installed after =>
          runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report .success before =
            .ok installed after) fixed.manifest (· = fixed.covered ++ pending)
  | checkpoint {initial published : Image} {before reopenStart : ReopenImage}
      {manifest : Option ByteArray} {events : List WAL.Write}
      {expected : Manifest.Checkpoint → List ByteArray → Prop}
      (reads : RecoveryReads published reopenStart reopenStart.directory.active.manifest)
      (settled : before.SettledFor manifest events)
      (projects : initial.manifest = before.directory.project .manifest)
      (fits : (WAL.encode events).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 events)
      (initialValid : initial.Valid events.length.toUInt64 expected)
      (witness : ∀ header files, expected header files →
        ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint)
      (checkpoints : Retry events.length.toUInt64 expected initial published)
      (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopenStart)
      (report : Publication.Step → RepairReport) :
      RecoveryBoundary
        (fun installed after =>
          runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report .success reopenStart =
            .ok installed after) reopenStart.directory.active.manifest (· = events)
  | interruptedWrite {writer : MarkedWriterState} {pending : List WAL.Write}
      {key : UInt64} {value : Option UInt64} {event : WAL.Write} {next : PackedTable}
      {effects : WriteEffects} {cut before : ReopenImage} (fixed : FixedMarkedCheckpoint)
      (reads : RecoveryReads fixed.image before before.directory.active.manifest)
      (ready : writer.ReadyFor fixed.manifest)
      (history : writer.history = fixed.covered ++ pending)
      (prepared : prepareWrite writer.table key value = some (event, next))
      (fits : writer.walBytes + WAL.frameSize < UInt64.size)
      (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
      (attempts : MarkedReopenAttempts cut before)
      (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
      (durability : ∀ marker contents length, reads.walReads.marker = .ok (some marker) →
        reads.walReads.wal = .ok (some contents) → decode marker = .ok length →
        if length.toNat < contents.size then (∀ step, report step = .success) else aligned = .success) :
      RecoveryBoundary
        (fun installed after =>
          runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report aligned before =
            .ok installed after) fixed.manifest (fun events =>
              events = writer.history ∨ events = writer.history ++ [event])

private theorem RecoveryReads.shared_aligned_success {image : Image} {before : ReopenImage}
    (reads : RecoveryReads image before before.directory.active.manifest)
    {manifest : Option ByteArray} {events : List WAL.Write} {table : PackedTable}
    (settled : before.syncDirectory.SettledFor manifest events)
    (report : Publication.Step → RepairReport)
    (opened : runMarkedReopen
      (MarkedReopenReads.mk reads.walReads
        (reads.checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false .success before = .ok table before.syncDirectory) :
    ∃ generation,
      runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal
        report .success before = .ok (table, generation, (WAL.encode events).size) before.syncDirectory := by
  have marker := congrArg DirectoryPublication.Bindings.walBoundary settled.1
  change before.directory.active.walBoundary = some (encode (WAL.encode events).size.toUInt64) at marker
  have marked : before.directory.active.walBoundary ≠ none := by rw [marker]; simp
  let reopenReads := MarkedReopenReads.mk reads.walReads
    (reads.checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)
  change runMarkedReopen reopenReads.preflight report false .success before = _ at opened
  cases ready : reopenReads.preflight with
  | error message => rw [ready] at opened; contradiction
  | ok validated =>
    obtain ⟨actual, _⟩ := reopenReads.success_selectedWal ready opened
    have selected := Option.some.inj (actual.symm.trans settled.2.2.1)
    refine ⟨((reads.checkpointReads.result.toOption.getD none).getD (.empty, 0)).2, ?_⟩
    rw [reads.walReads.runSharedMarkedOpen_eq marked reads.checkpointReads report .success]
    change (match runMarkedReopen reopenReads.preflight report false .success before with
      | .error message after => EStateM.Result.error message after
      | .ok table after => EStateM.Result.ok
          (table, ((reads.checkpointReads.result.toOption.getD none).getD (.empty, 0)).2,
            (reopenReads.preflight.toOption.map (fun data : MarkedPreflight => data.selected.size)).getD 0) after) = _
    rw [opened, ready]
    simp only [Except.toOption, Option.map_some, Option.getD_some, selected]

private theorem RecoveryReads.complete_settled {initial before : ReopenImage} {pending : List WAL.Write}
    (fixed : FixedMarkedCheckpoint)
    (reads : RecoveryReads fixed.image before before.directory.active.manifest)
    (settled : initial.SettledFor fixed.manifest (fixed.covered ++ pending))
    (fits : (WAL.encode (fixed.covered ++ pending)).size < UInt64.size)
    (ordered : WAL.OrdinalsFrom 1 (fixed.covered ++ pending))
    (attempts : MarkedReopenAttempts initial before) (report : Publication.Step → RepairReport) :
    ∃ table generation,
      runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal report .success before =
        .ok (table, generation, (WAL.encode (fixed.covered ++ pending)).size) before.syncDirectory ∧
      before.syncDirectory.SettledFor fixed.manifest (fixed.covered ++ pending) ∧
      table.committed.toNat = (fixed.covered ++ pending).length := by
  obtain ⟨pair, wal⟩ := attempts.visible_of_settled settled fits
  have manifest : before.directory.active.manifest = fixed.manifest :=
    congrArg DirectoryPublication.Bindings.manifest pair
  have marker := congrArg DirectoryPublication.Bindings.walBoundary pair
  obtain ⟨base, loads, same⟩ := fixed.written.loads
  have durable := fixed.written.ordered_durable_runs fixed.accepted
  obtain ⟨loaded, checkpointLoaded, sameBase⟩ := reads.checkpointReads.completes reads.readManifest
    reads.readRuns (manifest.symm ▸ durable) (manifest.symm ▸ loads)
  let reopenReads := MarkedReopenReads.mk reads.walReads
    (reads.checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)
  have readCheckpoint : reopenReads.checkpoint = .ok base := by
    change reads.checkpointReads.result.map (fun data => (data.getD (.empty, 0)).1) = .ok base
    rw [checkpointLoaded]
    exact congrArg Except.ok sameBase
  have watermark : fixed.covered.length = base.committed.toNat := by
    rw [same.committed]
    exact fixed.watermark
  obtain ⟨table, opened, count⟩ := reopenReads.completes_exactWal readCheckpoint
    (reads.readMarker.trans (congrArg Except.ok marker)) (reads.readWal.trans (congrArg Except.ok wal))
    fits watermark ordered report
  have settledAfter : before.syncDirectory.SettledFor fixed.manifest (fixed.covered ++ pending) :=
    ⟨pair, rfl, wal, rfl⟩
  obtain ⟨generation, completed⟩ := reads.shared_aligned_success settledAfter report opened
  exact ⟨table, generation, completed, settledAfter, count⟩

/-- An admitted recovery boundary with successful required operations returns
the table and exact installed WAL size. It settles the selected manifest and
one admitted history, whose length agrees with the returned committed count. -/
theorem RecoveryBoundary.completes
    {opened : (PackedTable × UInt64 × Nat) → ReopenImage → Prop} {manifest : Option ByteArray}
    {allowsHistory : List WAL.Write → Prop}
    (boundary : RecoveryBoundary opened manifest allowsHistory) :
    ∃ table generation after events, opened (table, generation, (WAL.encode events).size) after ∧
      after.SettledFor manifest events ∧ allowsHistory events ∧
      table.committed.toNat = events.length := by
  cases boundary with
  | empty reads valid reports created synced published =>
    obtain ⟨after, fixed, opened, ready, absent, _⟩ := emptyBootstrapOpen_ready valid
      reads.checkpointReads reads.walReads reads.readManifest reads.readMarker reads.readWal reports created synced published
    exact ⟨.empty, 0, after, [], opened, absent ▸ ready.settled, rfl, rfl⟩
  | legacy fixed reads valid covered fits reports success =>
    obtain ⟨loaded, marker, contents, table, after, checkpointRead, markerRead, walRead,
      opened, _, ready, _⟩ := legacyBootstrapRetry_completes fixed valid covered fits
        reads.checkpointReads reads.readManifest reads.readRuns reads.walReads reads.readMarker reads.readWal reports success
    exact ⟨table, (loaded.getD (.empty, 0)).2, after, _,
      ⟨loaded, marker, contents, checkpointRead, markerRead, walRead, opened⟩, ready.settled, rfl, ready.count.symm⟩
  | settled fixed reads settled fits ordered attempts report =>
    obtain ⟨table, generation, opened, settled, count⟩ :=
      reads.complete_settled fixed settled fits ordered attempts report
    exact ⟨table, generation, _, _, opened, settled, rfl, count⟩
  | checkpoint reads settled projects fits ordered initialValid witness checkpoints attempts report =>
    obtain ⟨table, opened, settled, count⟩ :=
      checkpointMarkedRetry_reopen_completes settled projects fits ordered initialValid witness checkpoints
        attempts reads.checkpointReads reads.walReads reads.readManifest reads.readRuns reads.readMarker reads.readWal report
    obtain ⟨generation, completed⟩ := reads.shared_aligned_success settled report opened
    exact ⟨table, generation, _, _, completed, settled, rfl, count⟩
  | interruptedWrite fixed reads ready history prepared fits failed attempts report aligned durability =>
    obtain ⟨events, table, generation, after, opened, _, settled, allowed, count, _⟩ :=
      reopenAfterWriteError_completes fixed ready history prepared fits failed attempts
        reads.checkpointReads reads.walReads reads.readManifest reads.readRuns reads.readMarker reads.readWal report aligned
        durability
    exact ⟨table, generation, after, events, opened, settled, allowed, count⟩

end Alvoki.WAL.Boundary
