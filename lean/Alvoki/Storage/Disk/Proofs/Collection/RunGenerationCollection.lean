import Alvoki.Storage.Disk.Proofs.Recovery.DiskRecoveryModel
import Alvoki.Storage.Disk.LegacyCheckpointRead

namespace Alvoki.Storage.CheckpointPublication

/-- Process retry can read the live manifest, and power-loss recovery can
read any one of the admitted durable manifests. -/
def Image.SelectsManifest (image : Image) (manifest : Option ByteArray) : Prop :=
  image.manifest.active = manifest ∨ manifest ∈ image.manifest.crashImages

/-- Under exclusive collection, a generation must be unreachable and
unheld. The caller protects generations used independently of the manifest,
such as by a file reader, backup or an in-flight publication reservation. -/
structure Image.Collectable (image : Image) (held : UInt64 → Prop) (generation : UInt64) : Prop where
  unreachable : image.Unreachable generation
  unheld : ¬ held generation

/-- After settlement, an absent manifest or a decoded checkpoint with a
matching live name rules out other generations for every recovery choice. -/
theorem Image.collectable_of_settled {image : Image} {held : UInt64 → Prop} {generation : UInt64}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (visible : image.manifest.active = none ∨ ∃ bytes header,
      image.manifest.active = some bytes ∧ Manifest.decode bytes = .ok header ∧ header.generation ≠ generation)
    (unheld : ¬ held generation) : image.Collectable held generation := by
  refine ⟨?_, unheld⟩
  intro bytes selectable header decoded
  have active : image.manifest.active = some bytes := selectable.elim id fun survives => by
    rw [settled] at survives
    exact (List.mem_singleton.mp survives).symm
  rcases visible with absent | ⟨visibleBytes, visibleHeader, visibleName, decodeVisible, different⟩
  · rw [absent] at active
    contradiction
  · have sameBytes := Option.some.inj (active.symm.trans visibleName)
    have sameHeader := Except.ok.inj (decoded.symm.trans (sameBytes ▸ decodeVisible))
    exact sameHeader.symm ▸ different

/-- A collection cut can drop the durability guarantee for any subset of
eligible run names. Other entries keep their exact bytes. A dropped guarantee
allows an interrupted unlink to leave the file physically present. -/
structure RunDeletion (held : UInt64 → Prop) (before after : Image) : Prop where
  manifest : after.manifest = before.manifest
  bindings : ∀ generation index, after.durable generation index = before.durable generation index ∨
    (before.Collectable held generation ∧ after.durable generation index = none)

/-- One modeled durable name removal. -/
def Image.dropRunName (image : Image) (generation : UInt64) (index : Nat) : Image :=
  { image with durable := fun gen idx =>
      if gen = generation ∧ idx = index then none else image.durable gen idx }

theorem RunDeletion.dropRunName {before : Image} {held : UInt64 → Prop} {generation : UInt64}
    (eligible : before.Collectable held generation) (index : Nat) :
    RunDeletion held before (before.dropRunName generation index) := by
  refine ⟨rfl, ?_⟩
  intro gen idx
  by_cases addressed : gen = generation ∧ idx = index
  · obtain ⟨rfl, rfl⟩ := addressed
    exact Or.inr ⟨eligible, by simp [Image.dropRunName]⟩
  · exact Or.inl (by simp [Image.dropRunName, addressed])

/-- A held generation retains every binding. The protection is for users of
run file names. A session pin that reads loaded immutable run bytes makes no
file lookup by itself. -/
theorem RunDeletion.keepsHeld {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {generation : UInt64} (protects : held generation)
    (index : Nat) : after.durable generation index = before.durable generation index := by
  rcases deleted.bindings generation index with same | ⟨eligible, _⟩
  · exact same
  · exact False.elim (eligible.unheld protects)

/-- If a selectable manifest decodes to this generation, every one of the
referenced generation's run bindings is identical across the deletion. -/
theorem RunDeletion.keepsSelected {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {bytes : ByteArray}
    (selected : before.SelectsManifest (some bytes)) {header : Manifest.Checkpoint}
    (decoded : Manifest.decode bytes = .ok header) :
    after.durable header.generation = before.durable header.generation := by
  funext index
  rcases deleted.bindings header.generation index with same | ⟨eligible, _⟩
  · exact same
  · exact False.elim (eligible.unreachable bytes selected header decoded rfl)

/-- Checkpoint acceptance after removal has the same witness and exact run
bindings for every selectable manifest. -/
theorem RunDeletion.accepts_iff {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {manifest : Option ByteArray}
    (selected : before.SelectsManifest manifest) {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop} :
    after.Accepts walSequence expected manifest ↔ before.Accepts walSequence expected manifest := by
  cases manifest with
  | none => rfl
  | some bytes =>
    constructor
    · rintro ⟨header, files, decoded, runs⟩
      exact ⟨header, files, decoded, runs.withKeptRuns (fun index _ =>
        congrFun (deleted.keepsSelected selected decoded).symm index)⟩
    · rintro ⟨header, files, decoded, runs⟩
      exact ⟨header, files, decoded, runs.withKeptRuns (fun index _ =>
        congrFun (deleted.keepsSelected selected decoded) index)⟩

theorem RunDeletion.valid {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (valid : before.Valid walSequence expected) : after.Valid walSequence expected := by
  rw [Image.Valid, deleted.manifest]
  refine ⟨valid.hasCrashImage, (deleted.accepts_iff (.inl rfl)).mpr valid.activeValid, ?_⟩
  intro candidate chosen
  exact (deleted.accepts_iff (.inr chosen)).mpr (valid.crashValid _ chosen)

/-- The manifest's exact ordered durable run read is unchanged. An absent
manifest reads no run names and a malformed manifest fails the same decode. -/
theorem RunDeletion.durableRuns_eq {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {manifest : Option ByteArray}
    (selected : before.SelectsManifest manifest) :
    after.readDurableCheckpointRuns manifest = before.readDurableCheckpointRuns manifest := by
  cases manifest with
  | none => rfl
  | some bytes =>
    cases decoded : Manifest.decode bytes with
    | error message => simp [Image.readDurableCheckpointRuns, decoded, Except.toOption]
    | ok header =>
      simp only [Image.readDurableCheckpointRuns, decoded, Except.toOption]
      change (List.range header.runCount.toNat).mapM (after.durable header.generation) =
        (List.range header.runCount.toNat).mapM (before.durable header.generation)
      rw [deleted.keepsSelected selected decoded]

private def Image.readKnownRun (image : Image) (generation : UInt64) (index : Nat) : Except String ByteArray :=
  match image.durable generation index with
  | some bytes => .ok bytes
  | none => .error "checkpoint run bytes are unavailable"

/-- Interpret the executable checkpoint loader on one selected manifest and
its guaranteed durable run bindings. The file lookup contract supplies
those bytes. Other native I/O errors are outside this interpretation. -/
def Image.loadSelectedCheckpoint (image : Image) (manifest : Option ByteArray) :
    Except String (Option (PackedTable × UInt64)) :=
  readCheckpoint (.ok manifest) image.readKnownRun id

/-- Both the successful value and the loader's validation error are unchanged
for the same selectable manifest and durable run bindings. -/
theorem RunDeletion.loadSelected_eq {held : UInt64 → Prop} {before after : Image}
    (deleted : RunDeletion held before after) {manifest : Option ByteArray}
    (selected : before.SelectsManifest manifest) :
    after.loadSelectedCheckpoint manifest = before.loadSelectedCheckpoint manifest := by
  cases manifest with
  | none => rfl
  | some bytes =>
    cases decoded : Manifest.decode bytes with
    | error message =>
      simp [Image.loadSelectedCheckpoint, readCheckpoint, Bind.bind, Except.bind, decoded]
    | ok header =>
      have sameRead : after.readKnownRun header.generation = before.readKnownRun header.generation := by
        unfold Image.readKnownRun
        rw [deleted.keepsSelected selected decoded]
      simp only [Image.loadSelectedCheckpoint, readCheckpoint, Bind.bind, Except.bind, id, decoded,
        readCheckpointRunBytes_eq_mapM, sameRead]

/-- A collection stretch uses a fixed protected set. Each interrupted unlink
batch can drop a subset of eligible run bindings. A crash chooses an admitted
manifest. A later publication must establish eligibility again. -/
inductive RunCollectionRetry (held : UInt64 → Prop) : Image → Image → Prop where
  | start (image : Image) : RunCollectionRetry held image image
  | remove (prior : RunCollectionRetry held initial before) (deleted : RunDeletion held before after) :
      RunCollectionRetry held initial after
  | crash (prior : RunCollectionRetry held initial before) (survives : manifest ∈ before.manifest.crashImages) :
      RunCollectionRetry held initial { before with manifest := .settled manifest }

theorem RunCollectionRetry.valid {held : UInt64 → Prop} {initial after : Image}
    (retry : RunCollectionRetry held initial after) {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (valid : initial.Valid walSequence expected) : after.Valid walSequence expected := by
  induction retry with
  | start => exact valid
  | remove _ deleted prior => exact deleted.valid prior
  | crash _ survives prior => exact Publication.Image.settled_valid (prior.crashValid _ survives)

theorem RunCollectionRetry.keepsHeld {held : UInt64 → Prop} {initial after : Image}
    (retry : RunCollectionRetry held initial after) {generation : UInt64} (protects : held generation)
    (index : Nat) : after.durable generation index = initial.durable generation index := by
  induction retry with
  | start => rfl
  | remove _ deleted prior => exact (deleted.keepsHeld protects index).trans prior
  | crash _ _ prior => exact prior

/-- Any manifest still selectable after collection and retries was already
selectable before collection and reads the same ordered bytes and checkpoint.
In-memory snapshot reads continue to use their existing table and pins. -/
theorem RunCollectionRetry.preservesSelected {held : UInt64 → Prop} {initial after : Image}
    (retry : RunCollectionRetry held initial after) {manifest : Option ByteArray}
    (selected : after.SelectsManifest manifest) : initial.SelectsManifest manifest ∧
      after.readDurableCheckpointRuns manifest = initial.readDurableCheckpointRuns manifest ∧
      after.loadSelectedCheckpoint manifest = initial.loadSelectedCheckpoint manifest := by
  induction retry with
  | start => exact ⟨selected, rfl, rfl⟩
  | @remove before _ _ deleted prior =>
    have earlier := (show before.SelectsManifest manifest from by
      simpa only [Image.SelectsManifest, deleted.manifest] using selected)
    obtain ⟨original, runs, loaded⟩ := prior earlier
    exact ⟨original, (deleted.durableRuns_eq earlier).trans runs, (deleted.loadSelected_eq earlier).trans loaded⟩
  | @crash before surviving _ survives prior =>
    have same : manifest = surviving := selected.elim Eq.symm List.mem_singleton.mp
    subst manifest
    exact prior (.inr survives)

/-- Subsequent selected-WAL replay has the same concrete result, including the
freshly loaded checkpoint and pins. This compares replay on the same WAL
prefix. Only run name removal is modeled by the collection steps. -/
theorem RunCollectionRetry.replay_eq {held : UInt64 → Prop} {initial after : Image}
    (retry : RunCollectionRetry held initial after) {manifest : Option ByteArray}
    (selected : after.SelectsManifest manifest) (wal : ByteArray) :
    (after.loadSelectedCheckpoint manifest >>= fun checkpoint =>
      recoverSelected (checkpoint.getD (.empty, 0)).1 wal) =
    (initial.loadSelectedCheckpoint manifest >>= fun checkpoint =>
      recoverSelected (checkpoint.getD (.empty, 0)).1 wal) := by
  rw [(retry.preservesSelected selected).2.2]

end Alvoki.Storage.CheckpointPublication
