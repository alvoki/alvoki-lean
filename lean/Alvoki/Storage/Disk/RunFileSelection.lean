import Alvoki.Storage.Disk.RunFileName
import Alvoki.Storage.Disk.Manifest

namespace Alvoki.Storage
open System

/-- Decode the manifest's generation for selection. Absence and generation
zero are distinct. A malformed manifest cannot supply an observation. -/
def runCollectionGeneration (manifest : Option ByteArray) : Except String (Option UInt64) :=
  (manifest.mapM Manifest.decode).map (Option.map (·.generation))

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

end Alvoki.Storage
