import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.Storage.CheckpointPublication
open Alvoki.WAL.Boundary

/-- During checkpoint publication the marked WAL is already durable. The
manifest's actual active and possible crash bindings therefore each pair with
the same marker. The lift keeps the input WAL and unrelated staging fields.
For a retry path, the claims concern the live and selectable bindings. -/
def Image.markedReopenImage (image : Image) (before : ReopenImage) : ReopenImage :=
  let pair := fun manifest => DirectoryPublication.Bindings.mk manifest before.directory.active.walBoundary
  ⟨⟨pair image.manifest.active, image.manifest.crashImages.map pair,
      fun entry => if entry = .manifest then image.manifest.staged else before.directory.staged entry⟩,
    before.wal⟩

/-- The lift starts from the input directory itself when the checkpoint model
uses its manifest projection and the WAL is settled. -/
theorem Image.markedReopenImage_start (image : Image) {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (settled : before.SettledFor manifest history)
    (projects : image.manifest = before.directory.project .manifest) :
    image.markedReopenImage before = before := by
  obtain ⟨active, durable, _, _⟩ := settled
  unfold markedReopenImage
  rw [projects]
  have sameActive : before.directory.active = ⟨manifest, before.directory.active.walBoundary⟩ := by
    rw [active]
  simp only [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, durable,
    List.map_cons, List.map_nil]
  have stage : (fun entry => if entry = .manifest then before.directory.staged .manifest else
      before.directory.staged entry) = before.directory.staged := by
    funext entry
    cases entry <;> simp
  rw [stage, show before.directory.active.manifest = manifest by rw [active], ← sameActive, ← durable]

/-- Every selectable metadata pair carries the same WAL marker and refers to
a complete durable checkpoint covered by that WAL's history. -/
theorem Image.markedReopenImage_selectable (image : Image) {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (valid : image.Valid history.length.toUInt64 expected)
    {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ (image.markedReopenImage before).directory.active ::
      (image.markedReopenImage before).directory.crashImages) :
    pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      image.Accepts history.length.toUInt64 expected pair.manifest := by
  rcases List.mem_cons.mp chosen with rfl | crash
  · exact ⟨congrArg DirectoryPublication.Bindings.walBoundary settled.1, valid.activeValid⟩
  · obtain ⟨candidate, survives, rfl⟩ := List.mem_map.mp crash
    exact ⟨congrArg DirectoryPublication.Bindings.walBoundary settled.1, valid.crashValid _ survives⟩

theorem Image.markedReopenImage_valid (image : Image) {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (fits : (WAL.encode history).size < UInt64.size)
    (valid : image.Valid history.length.toUInt64 expected) :
    (image.markedReopenImage before).Valid (fun _ => WAL.encode history) := by
  let lifted := image.markedReopenImage before
  have walActive : lifted.wal.active = some (WAL.encode history) := settled.2.2.1
  have walChoices : lifted.wal.crashImages = [lifted.wal.active] := settled.2.2.2
  have selectExact : select (WAL.encode history).size.toUInt64 (WAL.encode history) =
      .ok (WAL.encode history) := by
    simpa using select_encoded history ByteArray.empty fits
  have accepts (wal : Option ByteArray) (exactWal : wal = some (WAL.encode history)) :
      ∀ pair ∈ lifted.directory.active :: lifted.directory.crashImages,
        ∃ marker contents length, pair.walBoundary = some marker ∧ wal = some contents ∧
          WAL.Boundary.decode marker = .ok length ∧ select length contents = .ok (WAL.encode history) := by
    intro pair chosen
    exact ⟨_, _, _, (image.markedReopenImage_selectable settled valid chosen).1,
      exactWal, decode_encode _, selectExact⟩
  refine ⟨by rw [walChoices]; simp, accepts _ walActive, ?_⟩
  intro candidate survives
  rw [walChoices] at survives
  exact accepts _ ((List.mem_singleton.mp survives).trans walActive)

private theorem Image.markedReopenImage_markerBound (image : Image) {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (valid : image.Valid history.length.toUInt64 expected) :
    MarkerBound (image.markedReopenImage before).directory := by
  have visible := (image.markedReopenImage_selectable settled valid (List.mem_cons_self ..)).1
  refine ⟨_, _, visible, decode_encode _, ?_⟩
  intro pair chosen
  exact ⟨_, _, (image.markedReopenImage_selectable settled valid chosen).1,
    decode_encode _, Nat.le_refl _⟩

/-- The existing checkpoint schedule and its cuts determine the complete
manifest image. Lifting each result to the unchanged WAL preserves both the
WAL selection and the matching durable checkpoint read witnesses. -/
theorem checkpointMarkedRetry_valid {initial after : Image} {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (trace : Retry history.length.toUInt64 expected initial after) :
    initial.markedReopenImage before = before ∧
      (after.markedReopenImage before).Valid (fun _ => WAL.encode history) ∧
      ∀ pair ∈ (after.markedReopenImage before).directory.active ::
        (after.markedReopenImage before).directory.crashImages,
        pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
          after.Accepts history.length.toUInt64 expected pair.manifest := by
  have valid := checkpoint_retry_valid initialValid trace
  exact ⟨initial.markedReopenImage_start settled projects,
    after.markedReopenImage_valid settled fits valid,
    fun _ chosen => after.markedReopenImage_selectable settled valid chosen⟩

private theorem checkpointWatermark {image : Image} {sequence : UInt64}
    {manifest : Option ByteArray} {files : List ByteArray} {checkpoint : PackedTable}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (accepted : image.Accepts sequence expected manifest)
    (written : CheckpointForRecovery manifest files checkpoint) : checkpoint.committed ≤ sequence := by
  cases written with
  | absent => simp [PackedTable.empty]
  | written header checkpoint _ _ watermark _ floor _ =>
    obtain ⟨decoded, _, decode, _, covered, _, _⟩ := accepted
    have same := Except.ok.inj (decode.symm.trans (Manifest.decode_encode header floor))
    simpa only [same, watermark] using covered

/-- Checkpoint cuts followed by marked reopen attempts select the same WAL
and exact ordered checkpoint files. The selected checkpoint is covered by
the WAL watermark, and both the manifest acceptance and the checkpoint
invariant hold for the selected inputs. -/
theorem checkpointMarkedRetry_recoveryInputs {initial published : Image}
    {before after : ReopenImage} {manifest : Option ByteArray} {history : List WAL.Write}
    {expected : Manifest.Checkpoint → List ByteArray → Prop} {invariant : PackedTable → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (emptyValid : invariant .empty)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
        invariant checkpoint)
    (checkpoints : Retry history.length.toUInt64 expected initial published)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) after)
    {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataChosen : pair ∈ after.directory.active :: after.directory.crashImages)
    (walChosen : wal ∈ after.wal.active :: after.wal.crashImages) :
    initial.markedReopenImage before = before ∧
    published.Accepts history.length.toUInt64 expected pair.manifest ∧
    ∃ files checkpoint marker contents,
      CheckpointForRecovery pair.manifest files checkpoint ∧ invariant checkpoint ∧
      published.readDurableCheckpointRuns pair.manifest = some files ∧
      checkpoint.committed.toNat ≤ history.length ∧
      marker = WAL.Boundary.encode (WAL.encode history).size.toUInt64 ∧
      pair.walBoundary = some marker ∧ wal = some contents ∧
      (do let length ← WAL.Boundary.decode marker; select length contents) = .ok (WAL.encode history) := by
  have valid := checkpoint_retry_valid initialValid checkpoints
  have path := attempts.toRetry (published.markedReopenImage_markerBound settled valid)
  obtain ⟨boundary, accepted⟩ := published.markedReopenImage_selectable settled valid
    (path.chosen_pair_from_initial metadataChosen)
  obtain ⟨files, checkpoint, written, durable, property⟩ :=
    CheckpointForRecovery.of_durable_manifest_with accepted emptyValid witness
  obtain ⟨marker, contents, presentMarker, presentWal, selected⟩ := ReopenImage.select_chosen
    (reopenRetry_valid (published.markedReopenImage_valid settled fits valid) path)
    metadataChosen walChosen
  have watermark := UInt64.le_iff_toNat_le.mp (checkpointWatermark accepted written)
  have lengthFits : history.length < UInt64.size := by
    simp only [WAL.encode_size, WAL.frameSize] at fits
    omega
  rw [UInt64.toNat_ofNat_of_lt' lengthFits] at watermark
  exact ⟨initial.markedReopenImage_start settled projects, accepted, files, checkpoint, marker,
    contents, written, property, durable, watermark, Option.some.inj (presentMarker.symm.trans boundary),
    presentMarker, presentWal, selected⟩

/-- The full checkpoint schedule settles the new manifest with the same WAL
and installs the exact run bytes for the new generation. -/
theorem checkpointMarked_complete {initial : Image} {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write} (next : RunSet)
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest) :
    initial.markedReopenImage before = before ∧
    ∃ after, initial.execute next (steps next.files.length) = some after ∧
      (after.markedReopenImage before).SettledFor (some (Manifest.encode next.header)) history ∧
      ∀ index, after.durable next.header.generation index = next.files[index]? := by
  have start := initial.markedReopenImage_start settled projects
  obtain ⟨after, ran, published, durable, _⟩ := checkpoint_complete initial next
  obtain ⟨pair, _, walActive, walChoices⟩ := settled
  refine ⟨start, after, ran, ⟨?_, ?_, walActive, walChoices⟩, durable⟩
  · simp [Image.markedReopenImage, published, Publication.Image.settled, pair]
  · simp [Image.markedReopenImage, published, Publication.Image.settled]

end Alvoki.Storage.CheckpointPublication
