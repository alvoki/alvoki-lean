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

private theorem legacyFloor {bytes : ByteArray} {header : Checkpoint}
    (decoded : Manifest.decode bytes = .ok header) : header.floor ≤ header.committed := by
  unfold Manifest.decode at decoded
  split at decoded
  · contradiction
  dsimp only at decoded
  split at decoded
  · contradiction
  split at decoded
  · contradiction
  split at decoded
  · contradiction
  rename_i floor
  cases decoded
  exact UInt64.not_lt.mp floor

theorem VersionedCheckpoint.decoded_floor {bytes : ByteArray} {selected : VersionedCheckpoint}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected) : selected.header.floor ≤ selected.header.committed := by
  have parsed := VersionedCheckpoint.decoded_case decoded
  cases selected with
  | legacy => exact legacyFloor parsed
  | integrity => exact (IntegrityCheckpoint.decode_spec parsed).2.1

end Alvoki.Manifest

namespace Alvoki.Storage
open Manifest

/-- Reuse the original publication witness for the selected format's
semantic header. The actual manifest must decode in its own version, and
the additional run-payload check applies to the same exact durable bytes. -/
def CheckpointPublication.Image.AcceptsVersioned (image : CheckpointPublication.Image) (walSequence : UInt64)
    (expected : Checkpoint → List ByteArray → Prop) : Option ByteArray → Prop
  | none => True
  | some bytes => ∃ selected, VersionedCheckpoint.decode bytes = .ok selected ∧
      image.Accepts walSequence (fun header files => expected header files ∧ selected.ValidatesFiles files)
        (some (Manifest.encode selected.header))

theorem CheckpointPublication.Image.acceptsVersioned_legacy_iff
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {header : Checkpoint} (decoded : Manifest.decode bytes = .ok header) :
    image.AcceptsVersioned walSequence expected (some bytes) ↔ image.Accepts walSequence expected (some bytes) := by
  have tagged := VersionedCheckpoint.decode_legacy decoded
  have raw := Manifest.decode_reencode decoded
  constructor
  · rintro ⟨selected, decodedVersion, accepted⟩
    have same := Except.ok.inj (decodedVersion.symm.trans tagged)
    subst selected
    simpa [VersionedCheckpoint.header, VersionedCheckpoint.ValidatesFiles, raw] using accepted
  · intro accepted
    refine ⟨.legacy header, tagged, ?_⟩
    simpa [VersionedCheckpoint.header, VersionedCheckpoint.ValidatesFiles, raw] using accepted

theorem CheckpointPublication.Image.acceptsVersioned_integrity_iff
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {manifest : IntegrityCheckpoint} (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) :
    image.AcceptsVersioned walSequence expected (some bytes) ↔
      image.Accepts walSequence (fun header files => expected header files ∧ manifest.validateRuns files = true)
        (some (Manifest.encode manifest.header)) := by
  have tagged := VersionedCheckpoint.decode_integrity decoded
  constructor
  · rintro ⟨selected, decodedVersion, accepted⟩
    have same := Except.ok.inj (decodedVersion.symm.trans tagged)
    subst selected
    exact accepted
  · intro accepted
    exact ⟨.integrity manifest, tagged, accepted⟩

theorem CheckpointPublication.Image.acceptsVersioned_runs
    {image : CheckpointPublication.Image} {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    {bytes : ByteArray} {selected : VersionedCheckpoint}
    (accepted : image.AcceptsVersioned walSequence expected (some bytes))
    (decoded : VersionedCheckpoint.decode bytes = .ok selected) :
    ∃ files, (List.range selected.header.runCount.toNat).mapM (image.durable selected.header.generation) = some files ∧
      expected selected.header files ∧ selected.ValidatesFiles files ∧ selected.header.committed ≤ walSequence := by
  obtain ⟨format, decodedFormat, witness⟩ := accepted
  have same := Except.ok.inj (decodedFormat.symm.trans decoded)
  rw [same] at witness
  obtain ⟨header, files, canonical, ⟨spec, checked⟩, covered, count, durable⟩ := witness
  have headerEq := Except.ok.inj
    (canonical.symm.trans (Manifest.decode_encode selected.header (VersionedCheckpoint.decoded_floor decoded)))
  rw [headerEq] at spec covered count durable
  have ordered : (List.range selected.header.runCount.toNat).mapM
      (image.durable selected.header.generation) = some files := by
    rw [count, List.range_eq_range']
    exact read_ordered_runs _ 0 files (by simpa using durable)
  exact ⟨files, ordered, spec, checked, covered⟩

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
    {durable : UInt64 → Nat → Option ByteArray} {bytes : ByteArray}
    (reads : VersionedCheckpointFileReads durable (some bytes)) {selected : VersionedCheckpoint}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    {index : Nat} (within : index < selected.header.runCount.toNat) {value expected : ByteArray}
    (read : reads.readRun selected.header.generation index = .ok value)
    (known : durable selected.header.generation index = some expected) : value = expected := by
  have parsed := VersionedCheckpoint.decoded_case decoded
  cases selected with
  | legacy header => exact reads.runDurable bytes header rfl parsed index within value expected read known
  | integrity manifest => exact reads.integrityRunDurable bytes manifest rfl parsed index within value expected read known

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
      reads.selectedRunDurable decoded (List.mem_range.mp member) read known
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
        simp [loadVersionedRunSet, VersionedCheckpoint.header, validated]
    rw [structural] at opened
    cases interpreted : loadRunSet selected.header files with
    | error message => rw [interpreted] at opened; contradiction
    | ok restored =>
      rw [interpreted] at opened
      have exactLoaded := Option.some.inj (Except.ok.inj opened)
      cases exactLoaded
      exact ⟨files, durable, rfl, spec, validated, interpreted, rfl, covered⟩

end Alvoki.Storage
