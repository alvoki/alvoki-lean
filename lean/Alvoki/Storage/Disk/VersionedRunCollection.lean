import Alvoki.Storage.Disk.LockedRunCollection
import Alvoki.Storage.Disk.VersionedCheckpointPublication

namespace Alvoki.Storage.CheckpointPublication
open Manifest

/-- After the manifest binding settles, the decoded generation is the only
one that a live read or a crash can select. Decode the actual versioned bytes. -/
theorem Image.unreachableVersioned_iff_settled {image : Image} {bytes : ByteArray}
    {selected : VersionedCheckpoint} {generation : UInt64}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (visible : image.manifest.active = some bytes) (decoded : VersionedCheckpoint.decode bytes = .ok selected) :
    image.UnreachableVersioned generation ↔ selected.header.generation ≠ generation := by
  constructor
  · intro unreachable
    exact unreachable bytes (.inl visible) selected decoded
  · intro different candidate selectable observed observedDecode
    have active : image.manifest.active = some candidate := selectable.elim id fun survives => by
      rw [settled] at survives
      exact (List.mem_singleton.mp survives).symm
    obtain rfl := Option.some.inj (active.symm.trans visible)
    obtain rfl := Except.ok.inj (observedDecode.symm.trans decoded)
    exact different

/-- A successful v2 collector preflight identifies the installed generation
from the actual manifest bytes. An older generation cannot be selected. -/
theorem Image.olderUnreachable_afterIntegrityPreflight {image : Image} {bytes : ByteArray}
    {installed generation : UInt64} {current : Option UInt64}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (visible : image.manifest.active = some bytes)
    (checked : validateIntegrityRunCollectionGeneration installed image.manifest.active = .ok current)
    (older : generation < installed) : image.UnreachableVersioned generation := by
  rw [visible] at checked
  obtain ⟨selected, decoded, _, matching⟩ := validateIntegrityRunCollectionGeneration_some.mp checked
  apply (image.unreachableVersioned_iff_settled settled visible (VersionedCheckpoint.decode_integrity decoded)).mpr
  intro equal
  have same : selected.header.generation = generation := equal
  exact UInt64.lt_irrefl generation (by simpa only [matching, same] using older)

private theorem Image.acceptsVersioned_sameRuns {before after : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {bytes : ByteArray} {selected : VersionedCheckpoint}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (sameRuns : after.durable selected.header.generation = before.durable selected.header.generation) :
    after.AcceptsVersioned walSequence expected (some bytes) ↔
      before.AcceptsVersioned walSequence expected (some bytes) := by
  rw [Image.acceptsVersioned_decoded_iff decoded, Image.acceptsVersioned_decoded_iff decoded]
  constructor
  · rintro ⟨files, runs⟩
    exact ⟨files, runs.withKeptRuns (fun index _ => congrFun sameRuns.symm index)⟩
  · rintro ⟨files, runs⟩
    exact ⟨files, runs.withKeptRuns (fun index _ => congrFun sameRuns index)⟩

/-- Approved older addresses cannot affect any index of the selected
generation. The same exact ordered files still witness acceptance,
including the integrity check when the manifest is v2. -/
theorem RunUnlinkRetry.preservesVersionedCheckpoint {approved : List RunAddress} {files : RunFiles}
    {after : RunUnlinkImage} {manifest : Publication.Image} {bytes : ByteArray} {selected : VersionedCheckpoint}
    {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    (retry : RunUnlinkRetry approved (.settled files) after)
    (settled : manifest.crashImages = [manifest.active])
    (visible : manifest.active = some bytes) (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (older : ∀ address ∈ approved, address.1 < selected.header.generation)
    (valid : (⟨manifest, files⟩ : Image).ValidVersioned walSequence expected) :
    (after.project manifest).durable selected.header.generation = files selected.header.generation ∧
      (after.project manifest).ValidVersioned walSequence expected := by
  have sameRuns : (after.project manifest).durable selected.header.generation = files selected.header.generation := by
    funext index
    apply retry.keepsUnapproved (name := (selected.header.generation, index))
    exact fun chosen => UInt64.lt_irrefl _ (older _ chosen)
  have accepts : (after.project manifest).AcceptsVersioned walSequence expected (some bytes) :=
    (Image.acceptsVersioned_sameRuns decoded sameRuns).mpr (visible ▸ valid.activeValid)
  refine ⟨sameRuns, ⟨valid.hasCrashImage, visible.symm ▸ accepts, ?_⟩⟩
  intro candidate survives
  change candidate ∈ manifest.crashImages at survives
  rw [settled] at survives
  rw [List.mem_singleton.mp survives, visible]
  exact accepts

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage
open System Manifest CheckpointPublication

/-- The proposed versioned collector reuses the existing older-generation
policy at the generation read from the installed manifest. -/
theorem LockedRunInventory.selectOlderVersionedRuns_iff {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) (selected : VersionedCheckpoint) (held : List UInt64)
    {generation : UInt64} {index : Nat} :
    (generation, index) ∈ selectRunFiles dir (some selected.header.generation)
      (retainRunGeneration selected.header.generation held) inventory.kindAt inventory.names ↔
    renderRunFileName generation index ∈ inventory.names ∧ generation < selected.header.generation ∧
      generation ∉ held ∧ inventory.kindAt (dir.file (.run generation index)) = .ok .file :=
  inventory.selectOlderRunsAt_iff held rfl

/-- Run the shared inventory selector and unlink schedule after the
versioned preflight supplied the writer's installed generation. Any
primitive report preserves exact selected files and recovery acceptance. The
same approved older addresses can be used through a subsequent retry. -/
theorem LockedRunInventory.runVersionedOlderCollection_preserves {dir : DiskDirectory}
    {regularAt : FilePath → Prop} (inventory : LockedRunInventory dir regularAt)
    {before : RunUnlinkImage} {files : RunFiles} {manifest : Publication.Image}
    {bytes : ByteArray} {selected : VersionedCheckpoint} {approved : List RunAddress}
    {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    (held : List UInt64) (settled : manifest.crashImages = [manifest.active])
    (visible : manifest.active = some bytes) (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (valid : (⟨manifest, files⟩ : Image).ValidVersioned walSequence expected)
    (prior : RunUnlinkRetry approved (.settled files) before)
    (olderUnheld : ∀ address ∈ approved, address.1 < selected.header.generation ∧ address.1 ∉ held)
    (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit)
    (reports : RunUnlinkEffectContract perform)
    (coversSelected : ∀ address ∈ selectRunFiles dir (some selected.header.generation)
      (retainRunGeneration selected.header.generation held) inventory.kindAt inventory.names, address ∈ approved) :
    let run : EStateM IO.Error RunUnlinkImage Unit := do
      let addresses ← selectRunFilesWith dir (some selected.header.generation)
        (retainRunGeneration selected.header.generation held) (fun path => pure (inventory.kindAt path))
        inventory.names
      RunCollection.run addresses perform
    match run before with
    | .ok _ after | .error _ after =>
      RunUnlinkRetry approved (.settled files) after ∧
        (after.project manifest).durable selected.header.generation = files selected.header.generation ∧
        (after.project manifest).ValidVersioned walSequence expected := by
  dsimp only
  rw [selectRunFilesWith_pure, pure_bind]
  have preserves {after : RunUnlinkImage} (retry : RunUnlinkRetry approved (.settled files) after) :=
    retry.preservesVersionedCheckpoint settled visible decoded (fun name chosen => (olderUnheld name chosen).1) valid
  have retries := prior.runSchedule _ coversSelected perform reports
  split at retries <;> rename_i after execution <;> rw [execution] <;> exact ⟨retries, preserves retries⟩

end Alvoki.Storage
