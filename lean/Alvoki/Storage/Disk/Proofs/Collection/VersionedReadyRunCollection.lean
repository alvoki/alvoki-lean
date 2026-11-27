import Alvoki.Storage.Disk.OptionalFileRead
import Alvoki.Storage.Disk.Proofs.Session.VersionedReadyMaintenance
import Alvoki.Storage.Disk.Proofs.Collection.VersionedRunCollection

namespace Alvoki.WAL.Boundary
open System Storage CheckpointPublication Manifest

/-- Collection updates the observed durable run map. The live writer,
including its table, pins, WAL and history, is the same writer. -/
def ObservedMarkedState.withDurableRuns (state : ObservedMarkedState) (runs : RunFiles) :
    ObservedMarkedState :=
  { state with durable := runs }

/-- The native collector's manifest preflight, inventory selection and
filesystem callback schedule over reported effects. -/
def _root_.Alvoki.Storage.LockedRunInventory.runIntegrityCollection {dir : DiskDirectory}
    {regularAt : FilePath → Prop} (inventory : LockedRunInventory dir regularAt) (installed : UInt64)
    (observed : Option ByteArray) (held : List UInt64)
    (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit) :
    EStateM IO.Error RunUnlinkImage Unit := do
  let current ← match validateIntegrityRunCollectionGeneration installed observed with
    | .ok generation => pure generation
    | .error message => throw (IO.userError message)
  let selected ← selectRunFilesWith dir current (retainRunGeneration installed held)
    (fun path => pure (inventory.kindAt path)) inventory.names
  RunCollection.run selected perform

namespace ObservedMarkedState.VersionedReady

private theorem selectedGeneration {state : ObservedMarkedState} (valid : state.VersionedReady)
    {bytes : ByteArray} {selected : VersionedCheckpoint}
    (visible : state.writer.image.directory.active.manifest = some bytes)
    (decoded : VersionedCheckpoint.decode bytes = .ok selected) : selected.header.generation = state.generation := by
  simpa [visible, decoded, Option.mapM, Functor.map, Except.map] using valid.generationMatches

/-- A successful read of the ready writer's actual manifest supplies the
strict collection preflight. An absent manifest gives generation zero. -/
theorem collectionPreflight {state : ObservedMarkedState} (valid : state.VersionedReady)
    (integrity : state.HasIntegrityManifest) :
    validateIntegrityRunCollectionGeneration state.generation state.writer.image.directory.active.manifest =
      .ok (state.writer.image.directory.active.manifest.map (fun _ => state.generation)) := by
  cases visible : state.writer.image.directory.active.manifest with
  | none =>
    apply validateIntegrityRunCollectionGeneration_none.mpr
    refine ⟨rfl, ?_⟩
    simpa [visible, Option.mapM, Functor.map, Except.map, Pure.pure, Except.pure] using valid.generationMatches.symm
  | some bytes =>
    obtain ⟨selected, decoded⟩ := integrity bytes visible
    have matching := valid.selectedGeneration visible (VersionedCheckpoint.decode_integrity decoded)
    exact validateIntegrityRunCollectionGeneration_some.mpr
      ⟨selected, decoded, congrArg some matching.symm, matching.symm⟩

/-- Only the guaranteed bindings used by the selected checkpoint need to
survive. The concrete namespace can contain other bindings or unsettled
obsolete names outside the observed writer's guaranteed map. This preserves
the ready writer's invariant with a new map. Resuming a live handle requires
the same-session path in `collectReported`. -/
theorem afterRunCollection {state : ObservedMarkedState} (valid : state.VersionedReady)
    (integrity : state.HasIntegrityManifest) {before after : RunUnlinkImage} {approved : List RunAddress}
    (known : ∀ generation index bytes, state.durable generation index = some bytes →
      before.guaranteed generation index = some bytes)
    (older : ∀ name ∈ approved, name.1 < state.generation)
    (retry : RunUnlinkRetry approved before after) :
    (state.withDurableRuns after.guaranteed).VersionedReady ∧
      (state.withDurableRuns after.guaranteed).HasIntegrityManifest := by
  refine ⟨⟨valid.ready, valid.live, ?_, valid.generationMatches⟩, integrity⟩
  change (state.withDurableRuns after.guaranteed).publicationInput.AcceptsVersioned
    state.writer.history.length.toUInt64 (CheckpointRepresentsPrefix state.writer.history)
    state.writer.image.directory.active.manifest
  have accepted := valid.selected
  cases visible : state.writer.image.directory.active.manifest with
  | none => trivial
  | some bytes =>
    rw [visible] at accepted
    obtain ⟨selected, decoded, files, runs⟩ := accepted
    have generation := valid.selectedGeneration visible decoded
    refine ⟨selected, decoded, files, runs.withKeptRuns ?_⟩
    intro index inside
    have recorded : state.durable selected.header.generation index = some files[index] :=
      (runs.durable index inside).trans (List.getElem?_eq_getElem inside)
    have unapproved : (selected.header.generation, index) ∉ approved := by
      intro chosen
      exact UInt64.lt_irrefl _ (by simpa only [generation] using older _ chosen)
    exact (retry.keepsKnown (known _ _ _ recorded) unapproved).trans recorded.symm

/-- Model the guarded part of native collection under the ready writer's
directory lock. The observed manifest and successful read-only inventory
come from that directory. The unlink and directory-sync callback reports
use the same owned paths in one uninterrupted handle session. Either
reported endpoint keeps the writer ready with the original pins and
canonical reads, and records the concrete kept run map. -/
theorem collectReported {state : ObservedMarkedState} (valid : state.VersionedReady)
    (integrity : state.HasIntegrityManifest) {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {before : RunUnlinkImage}
    (known : ∀ generation index bytes, state.durable generation index = some bytes →
      before.guaranteed generation index = some bytes)
    {observed : Option ByteArray} (manifest : OptionalPathRead state.writer.image.directory.active.manifest)
    (manifestRead : manifest.result (dir.file .manifest) = .ok observed)
    (held : List UInt64) (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit)
    (reports : RunUnlinkEffectContract perform) :
    match inventory.runIntegrityCollection state.generation observed held perform before with
    | .ok _ after | .error _ after =>
      (state.withDurableRuns after.guaranteed).VersionedReady ∧
        (state.withDurableRuns after.guaranteed).HasIntegrityManifest := by
  unfold LockedRunInventory.runIntegrityCollection
  have manifestAgrees := (manifest.resultVisible (dir.file .manifest) manifestRead).symm
  rw [manifestAgrees, valid.collectionPreflight integrity]
  simp only [pure_bind, selectRunFilesWith_pure]
  let selected := selectRunFiles dir (state.writer.image.directory.active.manifest.map (fun _ => state.generation))
    (retainRunGeneration state.generation held) inventory.kindAt inventory.names
  have older : ∀ name ∈ selected, name.1 < state.generation := by
    rintro ⟨generation, index⟩ chosen
    exact (retainRunGeneration_false_iff.mp (mem_selectRunFiles_iff.mp chosen).2.2.1).1
  have retry := (RunUnlinkRetry.start (approved := selected) before).runSchedule selected
    (fun _ chosen => chosen) perform reports
  split at retry <;> rename_i after execution <;> rw [execution] <;>
    exact valid.afterRunCollection integrity known older retry

end ObservedMarkedState.VersionedReady
end Alvoki.WAL.Boundary
