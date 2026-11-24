import Alvoki.Storage.Disk.RunFileName
import Alvoki.Storage.Disk.Manifest

namespace Alvoki.Storage
open System

/-- Decode the manifest's generation for selection. Absence and generation
zero are distinct. A malformed manifest cannot supply an observation. -/
def runCollectionGeneration (manifest : Option ByteArray) : Except String (Option UInt64) :=
  (manifest.mapM Manifest.decode).map (Option.map (·.generation))

/-- Check the observed v1 manifest against the generation of the ready writer.
The default generation of an absent manifest is zero. -/
def validateRunCollectionGeneration (installed : UInt64) (manifest : Option ByteArray) :
    Except String (Option UInt64) := do
  let current ← runCollectionGeneration manifest
  if current.getD 0 = installed then return current
  else throw "checkpoint generation changed before run collection"

theorem validateRunCollectionGeneration_ok_iff {installed : UInt64} {manifest : Option ByteArray}
    {current : Option UInt64} :
    validateRunCollectionGeneration installed manifest = .ok current ↔
      runCollectionGeneration manifest = .ok current ∧ current.getD 0 = installed := by
  cases decoded : runCollectionGeneration manifest with
  | error message => simp [validateRunCollectionGeneration, decoded, bind, Except.bind]
  | ok observed =>
    by_cases equal : observed.getD 0 = installed
    · simp [validateRunCollectionGeneration, decoded, bind, Except.bind, equal, pure, Except.pure]
      exact fun same => same ▸ equal
    · simp [validateRunCollectionGeneration, decoded, bind, Except.bind, equal]
      exact fun same => by simpa only [same] using equal

/-- Keep the writer's current generation, every newer generation, and all
explicit holds. This leaves failed future checkpoint attempts alone. -/
def retainRunGeneration (installed : UInt64) (held : List UInt64) (generation : UInt64) : Bool :=
  decide (installed ≤ generation) || held.contains generation

theorem retainRunGeneration_false_iff {installed generation : UInt64} {held : List UInt64} :
    retainRunGeneration installed held generation = false ↔ generation < installed ∧ generation ∉ held := by
  simp [retainRunGeneration, UInt64.not_le]

/-- Select a canonical listed name using a separate lstat report. Query the
writer's reconstructed path so the selector stays in the locked directory. -/
def selectRunFileWith [Monad m] (dir : DiskDirectory) (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → m (Except String IO.FS.FileType)) (name : String) :
    m (Option (UInt64 × Nat)) := do
  let some (generation, index) := parseRunFileName name | return none
  if current ≠ some generation ∧ held generation = false then
    let kind ← kindAt (dir.file (.run generation index))
    return match kind with
      | .ok .file => some (generation, index)
      | _ => none
  else return none

/-- Interpret recorded lookup results through the same selector. -/
def selectRunFile (dir : DiskDirectory) (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (name : String) : Option (UInt64 × Nat) :=
  selectRunFileWith (m := Id) dir current held kindAt name

theorem selectRunFile_eq_some_iff {dir : DiskDirectory} {current : Option UInt64} {held : UInt64 → Bool}
    {kindAt : FilePath → Except String IO.FS.FileType} {name : String} {generation : UInt64} {index : Nat} :
    selectRunFile dir current held kindAt name = some (generation, index) ↔
      parseRunFileName name = some (generation, index) ∧ current ≠ some generation ∧
      held generation = false ∧ kindAt (dir.file (.run generation index)) = .ok .file := by
  constructor
  · intro selected
    unfold selectRunFile selectRunFileWith at selected
    cases parsed : parseRunFileName name with
    | none => simp [parsed] at selected
    | some address =>
      obtain ⟨parsedGeneration, parsedIndex⟩ := address
      simp only [parsed, bind, pure] at selected
      split at selected
      · rename_i eligible
        split at selected
        · rename_i regular
          cases selected
          exact ⟨rfl, eligible.1, eligible.2, regular⟩
        · contradiction
      · contradiction
  · rintro ⟨parsed, obsolete, unheld, regular⟩
    simp [selectRunFile, selectRunFileWith, parsed, obsolete, unheld, regular, bind, pure]

/-- The candidate addresses from the finite directory inventory. -/
def selectRunFiles (dir : DiskDirectory) (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (names : List String) : List (UInt64 × Nat) :=
  names.filterMap (selectRunFile dir current held kindAt)

/-- Inspect eligible names in directory order. Finish all lookups before
handing any addresses to the unlink schedule. -/
def selectRunFilesWith [Monad m] (dir : DiskDirectory) (current : Option UInt64)
    (held : UInt64 → Bool) (kindAt : FilePath → m (Except String IO.FS.FileType))
    (names : List String) : m (List (UInt64 × Nat)) :=
  names.filterMapM (selectRunFileWith dir current held kindAt)

private theorem selectRunFileWith_pure [Monad m] [LawfulMonad m] (dir : DiskDirectory)
    (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (name : String) :
    selectRunFileWith (m := m) dir current held (fun path => pure (kindAt path)) name =
      pure (selectRunFile dir current held kindAt name) := by
  unfold selectRunFile selectRunFileWith
  cases parsed : parseRunFileName name with
  | none => rfl
  | some address =>
    obtain ⟨generation, index⟩ := address
    by_cases eligible : current ≠ some generation ∧ held generation = false <;>
      simp [eligible, bind, pure]

theorem selectRunFilesWith_pure [Monad m] [LawfulMonad m] (dir : DiskDirectory)
    (current : Option UInt64) (held : UInt64 → Bool)
    (kindAt : FilePath → Except String IO.FS.FileType) (names : List String) :
    selectRunFilesWith (m := m) dir current held (fun path => pure (kindAt path)) names =
      pure (selectRunFiles dir current held kindAt names) := by
  unfold selectRunFilesWith selectRunFiles
  induction names with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.filterMapM_cons, List.filterMap_cons, selectRunFileWith_pure, pure_bind, ih]
    cases selectRunFile dir current held kindAt name <;> simp

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
