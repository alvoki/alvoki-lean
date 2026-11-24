import Alvoki.Storage.Disk.DiskRecoveryModel

namespace Alvoki.WAL.Boundary
open Storage

private def observe (result : Except String α) : EStateM String ReopenImage α := fun image =>
  match result with
  | .ok value => .ok value image
  | .error message => .error message image

/-- Execute the native open's shared continuation with locked file reads
and reported durability effects. In the marked branch, open can neither
create a WAL nor publish a new marker. Installation records the table,
checkpoint generation and WAL length supplied to the native installer. -/
def runSharedMarkedOpen (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) (repair : Publication.Step → RepairReport)
    (aligned : AlignedSyncReport) : EStateM String ReopenImage (PackedTable × UInt64 × Nat) := do
  let loaded ← observe checkpoint
  withRecoveredOpen loaded (observe marker) (observe wal) observe
    (fun message => throw message)
    (fun _ => throw "marked open cannot create a WAL")
    (fun selected => Publication.run (performRepair repair selected))
    (fun _ => performAlignedSync false aligned)
    (fun _ => throw "marked open cannot publish the first marker")
    (fun table generation size => pure (table, generation, size))

/-- In an already marked directory a successful marker lookup cannot be
absent. Read errors, invalid contents, a missing WAL and failed durability
operations return exactly the model's error and post-effect image. Success
also records the generation and exact length passed to the native installer.
This is an equality for the reported callbacks, before the native allocation
of the ready handle. -/
theorem runSharedMarkedOpen_eq (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) (notAbsent : marker ≠ .ok none)
    (repair : Publication.Step → RepairReport) (aligned : AlignedSyncReport) (before : ReopenImage) :
    let preflight := markedReopenPreflight (checkpoint.map fun loaded => (loaded.getD (.empty, 0)).1) marker wal
    runSharedMarkedOpen checkpoint marker wal repair aligned before =
      match runMarkedReopen preflight repair false aligned before with
      | .error message after => .error message after
      | .ok table after =>
        .ok (table, ((checkpoint.toOption.getD none).getD (.empty, 0)).2,
          (preflight.toOption.map (·.selected.size)).getD 0) after := by
  cases checkpoint with
  | error message => rfl
  | ok loaded =>
    rcases marker with error | (_ | marker)
    · rfl
    · exact False.elim (notAbsent rfl)
    · simp only [runSharedMarkedOpen, observe, markedReopenPreflight, runMarkedReopen,
        withRecoveredOpen, withOpenWal, Option.mapM, Functor.map, Except.map, EStateM.map,
        Bind.bind, Except.bind, EStateM.bind, Pure.pure, Except.pure]
      cases decoded : decode marker with
      | error message => rfl
      | ok count =>
        rcases wal with error | (_ | bytes)
        · rfl
        · simp [observe, EStateM.bind] <;> rfl
        · cases recovered : recoverMarked (loaded.getD (.empty, 0)).1 count bytes with
          | error message =>
            simp [recovered, EStateM.bind, EStateM.pure, observe]
          | ok selectedTable =>
            obtain ⟨selected, table⟩ := selectedTable
            simp [recovered, EStateM.bind, EStateM.pure, observe, Except.toOption]
            split <;> simp_all

/-- The locked visible marker contract supplies the branch condition. The
checkpoint result comes from the shared manifest and ordered-run loader. -/
theorem MarkedWalReads.runSharedMarkedOpen_eq {before : ReopenImage} (reads : MarkedWalReads before)
    (marked : before.directory.active.walBoundary ≠ none)
    {image : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations image before.directory.active.manifest)
    (repair : Publication.Step → RepairReport) (aligned : AlignedSyncReport) :
    let checkpoint := checkpointReads.result
    let preflight := (MarkedReopenReads.mk reads (checkpoint.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
    runSharedMarkedOpen checkpoint reads.marker reads.wal repair aligned before =
      match runMarkedReopen preflight repair false aligned before with
      | .error message after => .error message after
      | .ok table after =>
        .ok (table, ((checkpoint.toOption.getD none).getD (.empty, 0)).2,
          (preflight.toOption.map (·.selected.size)).getD 0) after :=
  Boundary.runSharedMarkedOpen_eq checkpointReads.result _ _
    (fun absent => marked (reads.markerVisible _ absent)) repair aligned before

/-- Invert a successful shared open into the observations and durability
result used by the marked refinement. The returned generation is zero for
an absent checkpoint and otherwise comes from the accepted manifest. -/
theorem MarkedWalReads.runSharedMarkedOpen_success {before after : ReopenImage} (reads : MarkedWalReads before)
    (marked : before.directory.active.walBoundary ≠ none)
    {image : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations image before.directory.active.manifest)
    {repair : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    {table : PackedTable} {generation : UInt64} {walBytes : Nat}
    (opened : runSharedMarkedOpen checkpointReads.result reads.marker reads.wal repair aligned before =
      .ok (table, generation, walBytes) after) :
    let preflight := (MarkedReopenReads.mk reads
      (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
    ∃ loaded validated, checkpointReads.result = .ok loaded ∧ preflight = .ok validated ∧
      runMarkedReopen preflight repair false aligned before = .ok table after ∧
      generation = (loaded.getD (.empty, 0)).2 ∧ walBytes = validated.selected.size := by
  let preflight := (MarkedReopenReads.mk reads
    (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
  rw [reads.runSharedMarkedOpen_eq marked checkpointReads repair aligned] at opened
  change (match runMarkedReopen preflight repair false aligned before with
    | .error message after => EStateM.Result.error message after
    | .ok table after => EStateM.Result.ok (table, ((checkpointReads.result.toOption.getD none).getD (.empty, 0)).2,
      (preflight.toOption.map (·.selected.size)).getD 0) after) =
      EStateM.Result.ok (table, generation, walBytes) after at opened
  cases checkpoint : checkpointReads.result with
  | error message =>
    have failed : preflight = .error message := by
      simp [preflight, MarkedReopenReads.preflight, markedReopenPreflight, Except.map, checkpoint,
        Bind.bind, Except.bind]
    rw [failed] at opened
    contradiction
  | ok loaded =>
    cases accepted : preflight with
    | error message => rw [accepted] at opened; contradiction
    | ok validated =>
      rw [accepted] at opened
      cases ran : runMarkedReopen (.ok validated) repair false aligned before with
      | error message cut => rw [ran] at opened; contradiction
      | ok installed cut =>
        rw [ran] at opened
        simp only [checkpoint, Except.toOption, Option.getD_some, Option.map_some] at opened
        have acceptedLoaded : (MarkedReopenReads.mk reads
            ((Except.ok loaded).map fun loaded => (loaded.getD (.empty, 0)).1)).preflight = .ok validated := by
          simpa only [preflight, checkpoint] using accepted
        cases opened
        exact ⟨loaded, validated, rfl, acceptedLoaded, acceptedLoaded.symm ▸ ran, rfl, rfl⟩

end Alvoki.WAL.Boundary
