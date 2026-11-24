import Alvoki.Storage.Disk.MarkedCheckpointPublication
import Alvoki.Storage.Disk.MarkedReopenStability

namespace Alvoki.Storage.CheckpointPublication

open WAL.Boundary

/-- At any admitted checkpoint cut and subsequent reopen or crash choice,
successful primitive reads and an aligned sync suffice for the shared marked
open to complete. An absent manifest needs no run reads. The checkpoint
cut supplies the loader witness, and the same durable WAL needs no repair. -/
theorem checkpointMarkedRetry_reopen_completes {initial published : Image}
    {before reopenStart : ReopenImage} {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint)
    (checkpoints : Retry history.length.toUInt64 expected initial published)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopenStart)
    (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
    (walReads : MarkedWalReads reopenStart)
    (manifestRead : checkpointReads.readManifest = .ok reopenStart.directory.active.manifest)
    (runReads : ∀ bytes header, reopenStart.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, checkpointReads.readRun header.generation index = .ok payload)
    (markerRead : walReads.marker = .ok reopenStart.directory.active.walBoundary)
    (walRead : walReads.wal = .ok reopenStart.wal.active)
    (report : Publication.Step → RepairReport) :
    ∃ table, runMarkedReopen
        (MarkedReopenReads.mk walReads
          (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
        report false .success reopenStart = .ok table reopenStart.syncDirectory ∧
      reopenStart.syncDirectory.SettledFor reopenStart.directory.active.manifest history ∧
      table.committed.toNat = history.length := by
  obtain ⟨_, _, files, checkpoint, marker, _, written, _, durable, coveredLength, markerExact,
      markerVisible, _, _⟩ :=
    checkpointMarkedRetry_recoveryInputs (invariant := fun _ => True)
      settled projects fits initialValid trivial
      (fun header files valid => by
        obtain ⟨checkpoint, written⟩ := witness header files valid
        exact ⟨checkpoint, written, trivial⟩)
      checkpoints attempts (List.mem_cons_self ..) (List.mem_cons_self ..)
  obtain ⟨base, loads, same⟩ := written.loads
  obtain ⟨loaded, checkpointLoaded, sameBase⟩ :=
    checkpointReads.completes manifestRead runReads durable loads
  let reads := MarkedReopenReads.mk walReads
    (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)
  have checkpointRead : reads.checkpoint = .ok base := by
    change checkpointReads.result.map (fun result => (result.getD (.empty, 0)).1) = .ok base
    rw [checkpointLoaded]
    exact congrArg Except.ok sameBase
  have cutValid := checkpoint_retry_valid initialValid checkpoints
  have bound := published.markedReopenImage_markerBound settled cutValid
  have selectedInitial : (published.markedReopenImage before).wal.Valid (· = some (WAL.encode history)) := by
    change before.wal.Valid (· = some (WAL.encode history))
    obtain ⟨_, _, active, choices⟩ := settled
    exact ⟨by simp [choices], active, fun _ survives => (List.mem_singleton.mp (choices ▸ survives)).trans active⟩
  have visibleWal := ((attempts.toRetry bound).preserves_exactWal
    (fun _ member => (published.markedReopenImage_selectable settled cutValid member).1)
    selectedInitial fits).activeValid
  let covered := history.take checkpoint.committed.toNat
  let pending := history.drop checkpoint.committed.toNat
  have splitHistory : covered ++ pending = history := List.take_append_drop ..
  have watermark : covered.length = base.committed.toNat := by
    simp [covered, List.length_take, Nat.min_eq_left coveredLength, same.committed]
  have readMarker : reads.marker =
      .ok (some (WAL.Boundary.encode (WAL.encode (covered ++ pending)).size.toUInt64)) := by
    change walReads.marker = _
    rw [markerRead, markerVisible, markerExact, splitHistory]
  have readWal : reads.wal = .ok (some (WAL.encode (covered ++ pending))) := by
    change walReads.wal = _
    rw [walRead, visibleWal, splitHistory]
  obtain ⟨table, opened, count⟩ := reads.completes_exactWal checkpointRead readMarker readWal
    (splitHistory.symm ▸ fits) watermark (splitHistory.symm ▸ ordered) report
  rw [splitHistory] at count
  refine ⟨table, opened, ⟨?_, rfl, visibleWal, rfl⟩, count⟩
  change (⟨reopenStart.directory.active.manifest, reopenStart.directory.active.walBoundary⟩ :
    DirectoryPublication.Bindings) = ⟨_, _⟩
  rw [markerVisible, markerExact]

end Alvoki.Storage.CheckpointPublication
