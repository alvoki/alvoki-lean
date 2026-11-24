import Alvoki.Storage.Disk.RunFileName
import Alvoki.Storage.Disk.RunGenerationCollection

namespace Alvoki.Storage
open System CheckpointPublication

/-- Decode the manifest's generation for selection. Absence and generation
zero are distinct. A malformed manifest cannot supply an observation. -/
def runCollectionGeneration (manifest : Option ByteArray) : Except String (Option UInt64) :=
  (manifest.mapM Manifest.decode).map (Option.map (·.generation))

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

/-- Select a canonical listed name using a separate lstat report. Query the
writer's reconstructed path so the selector stays in the locked directory. -/
def selectRunFile (dir : DiskDirectory) (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (name : String) : Option (UInt64 × Nat) := do
  let (generation, index) ← parseRunFileName name
  if current ≠ some generation ∧ held generation = false then
    let .ok .file := kindAt (dir.file (.run generation index)) | none
    return (generation, index)
  else none

theorem selectRunFile_eq_some_iff {dir : DiskDirectory} {current : Option UInt64} {held : UInt64 → Bool}
    {kindAt : FilePath → Except String IO.FS.FileType} {name : String} {generation : UInt64} {index : Nat} :
    selectRunFile dir current held kindAt name = some (generation, index) ↔
      parseRunFileName name = some (generation, index) ∧ current ≠ some generation ∧
      held generation = false ∧ kindAt (dir.file (.run generation index)) = .ok .file := by
  constructor
  · intro selected
    unfold selectRunFile at selected
    cases parsed : parseRunFileName name with
    | none => simp [parsed] at selected
    | some address =>
      obtain ⟨parsedGeneration, parsedIndex⟩ := address
      simp only [parsed, Bind.bind, Option.bind] at selected
      split at selected
      · rename_i eligible
        split at selected
        · rename_i regular
          cases selected
          exact ⟨rfl, eligible.1, eligible.2, regular⟩
        · contradiction
      · contradiction
  · rintro ⟨parsed, obsolete, unheld, regular⟩
    simp [selectRunFile, parsed, obsolete, unheld, regular, Bind.bind, Option.bind, Pure.pure]

/-- The candidate addresses from the finite directory inventory. -/
def selectRunFiles (dir : DiskDirectory) (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (names : List String) : List (UInt64 × Nat) :=
  names.filterMap (selectRunFile dir current held kindAt)

theorem mem_selectRunFiles_iff {dir : DiskDirectory} {current : Option UInt64} {held : UInt64 → Bool}
    {kindAt : FilePath → Except String IO.FS.FileType} {names : List String} {generation : UInt64} {index : Nat} :
    (generation, index) ∈ selectRunFiles dir current held kindAt names ↔
      renderRunFileName generation index ∈ names ∧ current ≠ some generation ∧
      held generation = false ∧ kindAt (dir.file (.run generation index)) = .ok .file := by
  rw [selectRunFiles, List.mem_filterMap]
  constructor
  · rintro ⟨name, listed, selected⟩
    obtain ⟨parsed, obsolete, unheld, regular⟩ := selectRunFile_eq_some_iff.mp selected
    exact ⟨parseRunFileName_sound parsed ▸ listed, obsolete, unheld, regular⟩
  · rintro ⟨listed, obsolete, unheld, regular⟩
    exact ⟨_, listed, selectRunFile_eq_some_iff.mpr ⟨parseRunFileName_render _ _, obsolete, unheld, regular⟩⟩

/-- Keep current and held generations at every index, including indices
beyond the current manifest's run count. -/
theorem not_mem_selectRunFiles_of_protected {dir : DiskDirectory} {current : Option UInt64}
    {held : UInt64 → Bool} {kindAt : FilePath → Except String IO.FS.FileType}
    {names : List String} {generation : UInt64} {index : Nat}
    (excluded : current = some generation ∨ held generation = true) :
    (generation, index) ∉ selectRunFiles dir current held kindAt names := by
  intro selected
  obtain ⟨_, obsolete, unheld, _⟩ := mem_selectRunFiles_iff.mp selected
  exact excluded.elim obsolete (fun pinned => by rw [pinned] at unheld; contradiction)

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
