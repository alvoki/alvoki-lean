import Alvoki.Storage.Disk.LegacyManifest
import Alvoki.Storage.Disk.RunFileSelection
import Alvoki.Storage.Disk.RunGenerationCollection

namespace Alvoki.Storage
open System CheckpointPublication

/-- Decode the generation for the v1 collection model. Absence and a
manifest naming generation zero remain distinct. -/
def runCollectionGeneration (manifest : Option ByteArray) : Except String (Option UInt64) :=
  (manifest.mapM Manifest.decode).map (Option.map (·.generation))

/-- The v1 model checks the same installed-generation condition as v2. -/
def validateRunCollectionGeneration (installed : UInt64) (manifest : Option ByteArray) :
    Except String (Option UInt64) :=
  validateObservedRunGeneration installed (runCollectionGeneration manifest)

theorem validateRunCollectionGeneration_ok_iff {installed : UInt64} {manifest : Option ByteArray}
    {current : Option UInt64} :
    validateRunCollectionGeneration installed manifest = .ok current ↔
      runCollectionGeneration manifest = .ok current ∧ current.getD 0 = installed :=
  validateObservedRunGeneration_ok_iff

/-- With the manifest settled and readable, reachability is exactly the
observed generation. Independent holders still take precedence. -/
theorem CheckpointPublication.Image.collectable_iff_generation {image : Image}
    {held : UInt64 → Prop} {current : Option UInt64} {generation : UInt64}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (observed : runCollectionGeneration image.manifest.active = .ok current) :
    image.Collectable held generation ↔ current ≠ some generation ∧ ¬ held generation := by
  cases visible : image.manifest.active with
  | none =>
    rw [visible] at observed
    cases Except.ok.inj observed
    exact ⟨fun eligible => ⟨by simp, eligible.unheld⟩,
      fun conditions => image.collectable_of_settled settled (.inl visible) conditions.2⟩
  | some bytes =>
    rw [visible] at observed
    cases decoded : Manifest.decode bytes with
    | error message =>
      simp [runCollectionGeneration, Option.mapM, Functor.map, Except.map, decoded] at observed
    | ok header =>
      simp [runCollectionGeneration, Option.mapM, Functor.map, Except.map, decoded] at observed
      subst current
      constructor
      · intro eligible
        exact ⟨fun equal => eligible.unreachable bytes (.inl visible) header decoded (Option.some.inj equal),
          eligible.unheld⟩
      · intro conditions
        exact image.collectable_of_settled settled
          (.inr ⟨bytes, header, visible, decoded, fun same => conditions.1 (congrArg some same)⟩) conditions.2

/-- Observations from one locked directory inventory. Listing supplies the
basenames. A successful regular lstat report identifies the stable binding
at that reconstructed path, including the no-follow property of lstat. -/
structure LockedRunInventory (dir : DiskDirectory) (regularAt : FilePath → Prop) where
  names : List String
  kindAt : FilePath → Except String IO.FS.FileType
  identifiesRegular : ∀ generation index, kindAt (dir.file (.run generation index)) = .ok .file →
    regularAt (dir.file (.run generation index))

/-- A selected address is a listed, exact regular run path and safe under the
collection invariant. The current generation is excluded at every index. -/
theorem LockedRunInventory.sound {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {image : Image}
    {current : Option UInt64} {held : UInt64 → Bool} {generation : UInt64} {index : Nat}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (observed : runCollectionGeneration image.manifest.active = .ok current)
    (selected : (generation, index) ∈ selectRunFiles dir current held inventory.kindAt inventory.names) :
    ∃ name ∈ inventory.names, parseRunFileName name = some (generation, index) ∧
      dir.file (.run generation index) = ⟨dir.path.toString ++ "/" ++ name⟩ ∧
      regularAt (dir.file (.run generation index)) ∧
      image.Collectable (fun generation => held generation = true) generation := by
  obtain ⟨listed, obsolete, unheld, regular⟩ := mem_selectRunFiles_iff.mp selected
  have parsed := parseRunFileName_render generation index
  refine ⟨_, listed, parsed, dir.file_eq_parsedRun parsed, inventory.identifiesRegular _ _ regular, ?_⟩
  exact (image.collectable_iff_generation settled observed).mpr ⟨obsolete, by simp [unheld]⟩

/-- Every listed eligible canonical run with a successful regular lstat is
selected. This isolates the inventory and metadata success premises needed
for progress of a later unlink protocol. -/
theorem LockedRunInventory.complete {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {image : Image}
    {current : Option UInt64} {held : UInt64 → Bool} {generation : UInt64} {index : Nat}
    (settled : image.manifest.crashImages = [image.manifest.active])
    (observed : runCollectionGeneration image.manifest.active = .ok current)
    (eligible : image.Collectable (fun generation => held generation = true) generation)
    (listed : renderRunFileName generation index ∈ inventory.names)
    (regular : inventory.kindAt (dir.file (.run generation index)) = .ok .file) :
    (generation, index) ∈ selectRunFiles dir current held inventory.kindAt inventory.names := by
  obtain ⟨obsolete, unheld⟩ := (image.collectable_iff_generation settled observed).mp eligible
  exact mem_selectRunFiles_iff.mpr ⟨listed, obsolete, Bool.eq_false_iff.mpr unheld, regular⟩

end Alvoki.Storage
