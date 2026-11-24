import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.VersionedCheckpointRead

namespace Alvoki.Manifest

/-- Only the integrity version adds a run-payload check. -/
def VersionedCheckpoint.ValidatesFiles (manifest : VersionedCheckpoint) (files : List ByteArray) : Prop :=
  match manifest with
  | .legacy _ => True
  | .integrity manifest => manifest.validateRuns files = true

theorem VersionedCheckpoint.decoded_case {bytes : ByteArray} {selected : VersionedCheckpoint}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected) :
    match selected with
    | .legacy header => Manifest.decode bytes = .ok header
    | .integrity manifest => IntegrityCheckpoint.decode bytes = .ok manifest := by
  unfold VersionedCheckpoint.decode at decoded
  split at decoded
  · contradiction
  split at decoded
  · cases parsed : IntegrityCheckpoint.decode bytes with
    | error => simp [parsed, Functor.map, Except.map] at decoded
    | ok manifest =>
      simp [parsed, Functor.map, Except.map] at decoded
      subst selected
      rfl
  · cases parsed : Manifest.decode bytes with
    | error => simp [parsed, Functor.map, Except.map] at decoded
    | ok header =>
      simp [parsed, Functor.map, Except.map] at decoded
      subst selected
      rfl

end Alvoki.Manifest

namespace Alvoki.Storage
open Manifest

/-- The raw manifest selects the typed header and run validation for its
format. Both checks refer to the same exact durable run set. -/
def CheckpointPublication.Image.AcceptsVersioned (image : CheckpointPublication.Image) (walSequence : UInt64)
    (expected : Checkpoint → List ByteArray → Prop) : Option ByteArray → Prop
  | none => True
  | some bytes => ∃ selected, VersionedCheckpoint.decode bytes = .ok selected ∧
      ∃ files, image.AcceptsRunSet walSequence (fun header files => expected header files ∧ selected.ValidatesFiles files)
        selected.header files

theorem CheckpointPublication.Image.acceptsVersioned_decoded_iff
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {selected : VersionedCheckpoint} (decoded : VersionedCheckpoint.decode bytes = .ok selected) :
    image.AcceptsVersioned walSequence expected (some bytes) ↔ ∃ files,
      image.AcceptsRunSet walSequence (fun header files => expected header files ∧ selected.ValidatesFiles files)
        selected.header files := by
  simp [Image.AcceptsVersioned, decoded]

theorem CheckpointPublication.Image.acceptsVersioned_legacy_iff
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {header : Checkpoint} (decoded : Manifest.decode bytes = .ok header) :
    image.AcceptsVersioned walSequence expected (some bytes) ↔ image.Accepts walSequence expected (some bytes) := by
  rw [Image.accepts_decoded_iff decoded, Image.acceptsVersioned_decoded_iff (VersionedCheckpoint.decode_legacy decoded)]
  simp [VersionedCheckpoint.header, VersionedCheckpoint.ValidatesFiles]

theorem CheckpointPublication.Image.acceptsVersioned_integrity_iff
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {manifest : IntegrityCheckpoint} (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) :
    image.AcceptsVersioned walSequence expected (some bytes) ↔ ∃ files,
      image.AcceptsRunSet walSequence (fun header files => expected header files ∧ manifest.validateRuns files = true)
        manifest.header files :=
  Image.acceptsVersioned_decoded_iff (VersionedCheckpoint.decode_integrity decoded)

theorem CheckpointPublication.Image.acceptsVersioned_runs
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {selected : VersionedCheckpoint}
    (accepted : image.AcceptsVersioned walSequence expected (some bytes))
    (decoded : VersionedCheckpoint.decode bytes = .ok selected) :
    ∃ files, (List.range selected.header.runCount.toNat).mapM (image.durable selected.header.generation) = some files ∧
      expected selected.header files ∧ selected.ValidatesFiles files ∧ selected.header.committed ≤ walSequence := by
  obtain ⟨files, runs⟩ := (Image.acceptsVersioned_decoded_iff decoded).mp accepted
  exact ⟨files, runs.ordered, runs.witness.1, runs.witness.2, runs.covered⟩

/-- Reuse the existing locked observations and supply the same run read
contract for the version that adds payload metadata. -/
structure VersionedCheckpointFileReads (durable : UInt64 → Nat → Option ByteArray)
    (manifest : Option ByteArray) extends CheckpointFileReads durable manifest where
  integrityRunDurable : ∀ bytes selected, manifest = some bytes → IntegrityCheckpoint.decode bytes = .ok selected →
    ∀ index, index < selected.header.runCount.toNat → ∀ value expected,
      readRun selected.header.generation index = .ok value →
      durable selected.header.generation index = some expected → value = expected

def VersionedCheckpointFileReads.result {durable : UInt64 → Nat → Option ByteArray} {manifest : Option ByteArray}
    (reads : VersionedCheckpointFileReads durable manifest) : Except String (Option (PackedTable × UInt64)) :=
  readVersionedCheckpoint reads.readManifest reads.readRun id

private theorem VersionedCheckpointFileReads.selectedRunDurable
    {durable : UInt64 → Nat → Option ByteArray} {manifest : Option ByteArray} {bytes : ByteArray}
    (reads : VersionedCheckpointFileReads durable manifest) (visible : manifest = some bytes)
    {selected : VersionedCheckpoint}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    {index : Nat} (within : index < selected.header.runCount.toNat) {value expected : ByteArray}
    (read : reads.readRun selected.header.generation index = .ok value)
    (known : durable selected.header.generation index = some expected) : value = expected := by
  have parsed := VersionedCheckpoint.decoded_case decoded
  cases selected with
  | legacy header => exact reads.runDurable bytes header visible parsed index within value expected read known
  | integrity manifest =>
    exact reads.integrityRunDurable bytes manifest visible parsed index within value expected read known

/-- The successful ordered read loop returns the exact durable bytes for
the generation and indices selected by either manifest version. -/
theorem VersionedCheckpointFileReads.selected_runs_success
    {durable : CheckpointPublication.RunFiles} {manifest : Option ByteArray} {bytes : ByteArray}
    {selected : VersionedCheckpoint} {files : List ByteArray}
    (reads : VersionedCheckpointFileReads durable manifest) (visible : manifest = some bytes)
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (runReads : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (stored : (List.range selected.header.runCount.toNat).mapM (durable selected.header.generation) = some files) :
    (List.range selected.header.runCount.toNat).mapM (reads.readRun selected.header.generation) = .ok files := by
  obtain ⟨observed, ordered⟩ := ordered_reads_succeed
    (indices := List.range selected.header.runCount.toNat)
    (fun index member => runReads index (List.mem_range.mp member))
  have same := observed_ordered_runs
    (fun _ member _ _ => reads.selectedRunDurable visible decoded (List.mem_range.mp member)) stored ordered
  exact same ▸ ordered

/-- A valid selected checkpoint loads from its exact durable file list when
the indicated reads report success and the structural loader accepts it. -/
theorem VersionedCheckpointFileReads.completes_selected
    {durable : CheckpointPublication.RunFiles} {manifest : Option ByteArray}
    {bytes : ByteArray} {selected : VersionedCheckpoint}
    {files : List ByteArray} {base : PackedTable}
    (reads : VersionedCheckpointFileReads durable manifest)
    (manifestRead : reads.readManifest = .ok (some bytes))
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (runReads : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (stored : (List.range selected.header.runCount.toNat).mapM (durable selected.header.generation) = some files)
    (validated : selected.ValidatesFiles files) (loaded : loadRunSet selected.header files = .ok base) :
    reads.result = .ok (some (base, selected.header.generation)) := by
  have visible := (reads.manifestVisible _ manifestRead).symm
  have ordered := reads.selected_runs_success visible decoded runReads stored
  have versioned : loadVersionedRunSet selected files = .ok base := by
    cases selected with
    | legacy => exact loaded
    | integrity manifest => exact loadVersionedRunSet_integrity_iff.mpr ⟨validated, loaded⟩
  simp [VersionedCheckpointFileReads.result, readVersionedCheckpoint, manifestRead, decoded,
    readCheckpointRunBytes_eq_mapM, ordered, versioned, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A successful versioned read uses exactly the accepted durable run map.
The selected v2 descriptor table was checked on those same observed bytes. -/
theorem VersionedCheckpointFileReads.loaded_lineage
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {selected : VersionedCheckpoint}
    (reads : VersionedCheckpointFileReads image.durable (some bytes))
    (accepted : image.AcceptsVersioned walSequence expected (some bytes))
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    {table : PackedTable} {generation : UInt64} (opened : reads.result = .ok (some (table, generation))) :
    ∃ files, (List.range selected.header.runCount.toNat).mapM (image.durable selected.header.generation) = some files ∧
      (List.range selected.header.runCount.toNat).mapM (reads.readRun selected.header.generation) = .ok files ∧
      expected selected.header files ∧ selected.ValidatesFiles files ∧ loadRunSet selected.header files = .ok table ∧
      generation = selected.header.generation ∧ selected.header.committed ≤ walSequence := by
  obtain ⟨files, durable, spec, validated, covered⟩ := image.acceptsVersioned_runs accepted decoded
  have visible : reads.readManifest = .ok (some bytes) := by
    cases observed : reads.readManifest with
    | error message =>
      simp [VersionedCheckpointFileReads.result, readVersionedCheckpoint, observed, Bind.bind, Except.bind] at opened
    | ok given => exact congrArg Except.ok (reads.manifestVisible given observed)
  simp only [VersionedCheckpointFileReads.result, readVersionedCheckpoint, visible, decoded, id,
    readCheckpointRunBytes_eq_mapM, Bind.bind, Except.bind] at opened
  cases loaded : (List.range selected.header.runCount.toNat).mapM (reads.readRun selected.header.generation) with
  | error message => rw [loaded] at opened; contradiction
  | ok observed =>
    have agrees (index : Nat) (member : index ∈ List.range selected.header.runCount.toNat)
        (value expected : ByteArray) (read : reads.readRun selected.header.generation index = .ok value)
        (known : image.durable selected.header.generation index = some expected) : value = expected :=
      reads.selectedRunDurable rfl decoded (List.mem_range.mp member) read known
    have same := observed_ordered_runs agrees durable loaded
    subst observed
    rw [loaded] at opened
    change (do
      let restored ← loadVersionedRunSet selected files
      pure (some (restored, selected.header.generation))) = .ok (some (table, generation)) at opened
    have structural : loadVersionedRunSet selected files = loadRunSet selected.header files := by
      cases selected with
      | legacy => rfl
      | integrity manifest =>
        change manifest.validateRuns files = true at validated
        simp [loadVersionedRunSet, loadIntegrityRunSet, VersionedCheckpoint.header, validated]
    rw [structural] at opened
    cases interpreted : loadRunSet selected.header files with
    | error message => rw [interpreted] at opened; contradiction
    | ok restored =>
      rw [interpreted] at opened
      have exactLoaded := Option.some.inj (Except.ok.inj opened)
      cases exactLoaded
      exact ⟨files, durable, rfl, spec, validated, interpreted, rfl, covered⟩

end Alvoki.Storage
