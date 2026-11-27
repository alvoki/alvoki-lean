import Alvoki.Storage.Proofs.Table.PackedTableLookup
import Alvoki.Storage.Disk.Proofs.Recovery.DiskRecoveryModel
import Alvoki.Storage.Disk.WalWritePublicationModel
import Alvoki.Storage.Disk.Proofs.WAL.WalReplayProvenance

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

/-- Every manifest choice at a checkpoint cut shares the same decoded marker.
This is the marker bound needed by each later observed reopen attempt. -/
theorem Image.markedReopenImage_markerBound (image : Image) {before : ReopenImage}
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

/-- After checkpoint cuts and reopen retries, the successful shared reopen
loads the exact ordered files named by the visible manifest and replays the
remaining part of the same WAL. The checkpoint witness relates its model to
the covered prefix. Fresh pins read that model's replay at the selected floor. -/
theorem checkpointMarkedRetry_reopen_refines {initial published : Image}
    {before reopenStart after : ReopenImage} {manifest : Option ByteArray}
    {history : List WAL.Write} {table : PackedTable}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    {representsPrefix : List WAL.Write → Sequential.SnapshotTable UInt64 → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (emptyValid : representsPrefix [] .empty)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint model, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
        checkpoint.Refines model ∧ representsPrefix (history.take checkpoint.committed.toNat) model)
    (checkpoints : Retry history.length.toUInt64 expected initial published)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopenStart)
    (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
    (walReads : MarkedWalReads reopenStart)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    (opened : runMarkedReopen
      (MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned reopenStart = .ok table after) :
    after.SettledFor reopenStart.directory.active.manifest history ∧
    published.Accepts history.length.toUInt64 expected reopenStart.directory.active.manifest ∧
    table.committed.toNat = history.length ∧
    ∃ files checkpoint base model abstract,
      CheckpointForRecovery reopenStart.directory.active.manifest files checkpoint ∧
      published.readDurableCheckpointRuns reopenStart.directory.active.manifest = some files ∧
      (match reopenStart.directory.active.manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      base.SameData checkpoint ∧
      recoverSelected base (WAL.encode history) = .ok table ∧
      replay base (history.drop checkpoint.committed.toNat) = .ok table ∧
      checkpoint.Refines model ∧ representsPrefix (history.take checkpoint.committed.toNat) model ∧
      SnapshotWalReplay model (history.drop checkpoint.committed.toNat) abstract ∧
      abstract.committed.toNat = history.length ∧ abstract.pins.floor = checkpoint.pins.floor ∧
      ∀ snapshot : UInt64, checkpoint.pins.floor ≤ snapshot → snapshot.toNat ≤ history.length →
        ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (abstract.table.range start stop snapshot)) := by
  have emptyCheckpoint : ∃ model, PackedTable.empty.Refines model ∧
      representsPrefix (history.take PackedTable.empty.committed.toNat) model :=
    ⟨.empty, PackedTable.empty_refines, by simpa [PackedTable.empty] using emptyValid⟩
  obtain ⟨_, accepted, files, checkpoint, selectedMarker, selectedContents, written,
    ⟨model, represents, prefixMatches⟩, durable, coveredLength, markerExact, markerAs, walAs, selects⟩ :=
    checkpointMarkedRetry_recoveryInputs
      (invariant := fun checkpoint => ∃ model, checkpoint.Refines model ∧
        representsPrefix (history.take checkpoint.committed.toNat) model)
      settled projects fits initialValid emptyCheckpoint
      (fun header files valid => by
        obtain ⟨checkpoint, model, written, represents, samePrefix⟩ := witness header files valid
        exact ⟨checkpoint, written, model, represents, samePrefix⟩)
      checkpoints attempts (List.mem_cons_self ..) (List.mem_cons_self ..)
  have bound := published.markedReopenImage_markerBound settled (checkpoint_retry_valid initialValid checkpoints)
  obtain ⟨base, marker, contents, selected, length, checkpointOpened, markerVisible,
    walVisible, decoded, selectedResult, replayed, directory, walActive, walChoices⟩ :=
    MarkedReopenReads.success _ ((attempts.toRetry bound).markerBound bound) opened
  have sameMarker := Option.some.inj (markerAs.symm.trans markerVisible)
  have sameContents := Option.some.inj (walAs.symm.trans walVisible)
  rw [sameMarker, sameContents, decoded] at selects
  have selectedEq := Except.ok.inj (selectedResult.symm.trans selects)
  subst selected
  change checkpointReads.result.map (fun loaded => (loaded.getD (.empty, 0)).1) = .ok base
    at checkpointOpened
  obtain ⟨loaded, loadResult, sameLoaded⟩ : ∃ loaded, checkpointReads.result = .ok loaded ∧
      (loaded.getD (.empty, 0)).1 = base := by
    cases loadResult : checkpointReads.result with
    | error => rw [loadResult] at checkpointOpened; contradiction
    | ok result =>
      rw [loadResult] at checkpointOpened
      exact ⟨result, rfl, Except.ok.inj checkpointOpened⟩
  have actualBase := checkpointReads.loaded_table durable loadResult
  rw [sameLoaded] at actualBase
  obtain ⟨referenceBase, expectedLoad, same⟩ := written.loads
  have sameBase := Except.ok.inj (actualBase.symm.trans expectedLoad)
  subst referenceBase
  let covered := history.take checkpoint.committed.toNat
  let suffix := history.drop checkpoint.committed.toNat
  have splitHistory : covered ++ suffix = history := List.take_append_drop ..
  have count : covered.length = base.committed.toNat := by
    simp [covered, List.length_take, Nat.min_eq_left coveredLength, same.committed]
  have played : replay base suffix = .ok table :=
    (recoverSelected_encoded base covered suffix (splitHistory.symm ▸ ordered) count).symm.trans
      (splitHistory.symm ▸ replayed)
  have committed : table.committed.toNat = history.length := by
    rw [replay_committed_count suffix played, ← count, ← List.length_append, splitHistory]
  obtain ⟨reference, replay, agrees⟩ := replay_sameData same.symm suffix played
  obtain ⟨abstract, modeled, refined⟩ := replay_refines represents replay
  have keepsFloor : abstract.pins.floor = checkpoint.pins.floor := by
    rw [modeled.pins, represents.pins]
  refine ⟨⟨?_, ?_, walActive, walActive.symm ▸ walChoices⟩, accepted, committed,
    files, checkpoint, base, model, abstract, written, durable, actualBase, same, replayed, played,
    represents, prefixMatches, modeled, ?_, keepsFloor, ?_⟩
  · rw [directory]
    change (⟨reopenStart.directory.active.manifest, reopenStart.directory.active.walBoundary⟩ :
      DirectoryPublication.Bindings) = ⟨_, _⟩
    rw [markerAs, markerExact]
  · rw [directory]
    rfl
  · rw [← refined.committed, agrees.committed, committed]
  · intro snapshot retained within
    have floor : reference.pins.floor ≤ snapshot := by
      simpa only [refined.pins, keepsFloor] using retained
    have upper : snapshot ≤ reference.committed := UInt64.le_iff_toNat_le.mpr (by
      simpa only [agrees.committed, committed] using within)
    simpa only [refined.table] using agrees.symm.acquireAt_reads floor upper

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
