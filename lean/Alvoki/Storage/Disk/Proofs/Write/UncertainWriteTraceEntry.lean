import Alvoki.Storage.Disk.Proofs.Recovery.LockedMarkedRead
import Alvoki.Storage.Disk.LockedRecoveryReads

namespace Alvoki.WAL.Boundary

open Storage

/-- An uncertain submission from a ready state has a healthy retry that
enters the whole-file mixed trace with the exact recovered installation.
The write-effect reports describe the whole-file publication model. Read reports
must agree with the same directory under its newly acquired lock. A retry
from a live writer requires the old owner to have released the lock. -/
theorem ObservedMarkedState.Valid.reopenAfterWriteErrorWithLock {state : ObservedMarkedState}
    (valid : state.Valid) {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite state.writer.table key value = some (event, preparedTable))
    (fits : state.writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom state.writer.history event effects state.writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.Observes directory before state.durable)
    (manifestRead : ∃ result, paths.readOptional (directory.file .manifest) = .ok result)
    (runReads : ∀ bytes header, before.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, paths.readBin (directory.file (.run header.generation index)) = .ok payload)
    (markerRead : ∃ result, paths.readOptional (directory.file .walBoundary) = .ok result)
    (walRead : ∃ result, paths.readOptional (directory.file .wal) = .ok result)
    (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
    (durability : ∀ marker contents length,
      (paths.readOptional (directory.file .walBoundary)).mapError toString = .ok (some marker) →
      (paths.readOptional (directory.file .wal)).mapError toString = .ok (some contents) →
      decode marker = .ok length →
      if length.toNat < contents.size then (∀ step, report step = .success) else aligned = .success)
    (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let observed := observes held
    let reopened := runSharedMarkedOpen observed.checkpointReads.result observed.walReads.marker
      observed.walReads.wal report aligned before
    ∃ next : ObservedMarkedState, ∃ installedOwners,
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) installedOwners ∧
      installedOwners.Owns directory descriptor ∧
      MarkedDatabaseStep state ⟨[], some event⟩ next ∧ next.Valid ∧
      next.generation = state.generation ∧ next.durable = state.durable ∧
      (next.writer.history = state.writer.history ∨ next.writer.history = state.writer.history ++ [event]) ∧
      next.writer.table.pins.active = [] := by
  dsimp only
  obtain ⟨checkpoint, durable, represented⟩ := valid
  obtain ⟨pending, history⟩ := represented.coveredPrefix
  let heldOwners := owners.set (directory.file .lock) (some descriptor)
  have held : heldOwners.Owns directory descriptor := by
    simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
  let reads : RecoveryReads checkpoint.image before before.directory.active.manifest :=
    .ofLockedPaths held (fun owned => durable.symm ▸ observes owned) manifestRead runReads markerRead walRead
  obtain ⟨events, table, generation, after, reopened, readGeneration, settled, retained, _, marked⟩ :=
    reopenAfterWriteError_completes checkpoint represented.ready history prepared fits failed attempts
      reads.checkpointReads reads.walReads reads.readManifest reads.readRuns reads.readMarker reads.readWal
      report aligned durability
  have generationMatches : generation = state.generation :=
    Except.ok.inj (readGeneration.symm.trans represented.generationMatches)
  have ordered : WAL.OrdinalsFrom 1 events := by
    rcases retained with rfl | rfl
    · exact represented.ready.ordered
    · exact (prepareWrite_extends_history represented.ready.ordered represented.ready.count prepared).2.2.1
  let writer : MarkedWriterState := ⟨table, (WAL.encode events).size, after, events⟩
  have decoded : MarkedWriterState.observeReopen table after = some writer := by
    simp [MarkedWriterState.observeReopen, settled.2.2.1, WAL.decodeOrdinals_encode _ ordered,
      Except.toOption, writer]
  have opened : MarkedSessionOpen state.durable cut table after := durable ▸
    MarkedSessionOpen.ofSharedOpen attempts marked reads.checkpointReads reads.walReads reopened
  have step : MarkedSessionStep state.durable state.writer ⟨[], some event⟩ writer :=
    .interrupted .start prepared fits failed opened decoded
  obtain ⟨_, ready, _, _, fresh⟩ := ObservedMarkedState.Valid.sessionStep ⟨checkpoint, durable, represented⟩ step
  have locked : DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause
        (runSharedMarkedOpen (observes held).checkpointReads.result (observes held).walReads.marker
          (observes held).walReads.wal report aligned before) owners =
      .ok ((table, generation, (WAL.encode events).size), after) heldOwners := by
    change runSharedMarkedOpen (observes held).checkpointReads.result (observes held).walReads.marker
      (observes held).walReads.wal report aligned before =
        .ok (table, generation, (WAL.encode events).size) after at reopened
    rw [reopened]
    rfl
  have owns := (DiskSession.runOpen_success acquisition locked).2.1
  refine ⟨state.withWriter writer, heldOwners, ?_, owns, .reopen step, ready, rfl, rfl, retained, fresh⟩
  simpa only [ObservedMarkedState.withWriter, writer, generationMatches] using locked

end Alvoki.WAL.Boundary
