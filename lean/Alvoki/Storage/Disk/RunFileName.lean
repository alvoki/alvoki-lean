import Alvoki.Storage.Disk.DiskPaths
import Std.Data.String.ToNat

namespace Alvoki.Storage
open System

private def runFileNumbers (name : String) : Option (Nat × Nat) := do
  let ["run", generation, withVersion] := (name.split '-').toList.map (·.copy) | none
  let [index, "v3"] := (withVersion.split '.').toList.map (·.copy) | none
  let generation ← generation.toNat?
  let index ← index.toNat?
  return (generation, index)

/-- Recognize a canonical run basename. Check the generation bound before
converting and require exactly the writer's spelling after decimal parsing.
The caller supplies the directory, regular-file observation and eligibility
for any future collection operation. -/
def parseRunFileName (name : String) : Option (UInt64 × Nat) := do
  let (generation, index) ← runFileNumbers name
  if generation < UInt64.size then
    let generation := generation.toUInt64
    if name = renderRunFileName generation index then some (generation, index) else none
  else none

theorem parseRunFileName_sound {name : String} {generation : UInt64} {index : Nat}
    (parsed : parseRunFileName name = some (generation, index)) : name = renderRunFileName generation index := by
  unfold parseRunFileName at parsed
  cases parts : runFileNumbers name with
  | none => simp [parts] at parsed
  | some numbers =>
    obtain ⟨parsedGeneration, parsedIndex⟩ := numbers
    simp only [parts, Bind.bind, Option.bind] at parsed
    split at parsed
    · split at parsed
      · rename_i canonical
        cases parsed
        exact canonical
      · contradiction
    · contradiction

private theorem decimal_excludes (n : Nat) {separator : Char} (notDigit : separator.isDigit = false) :
    separator ∉ n.repr.toList := by
  intro found
  rw [Nat.toList_repr] at found
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) found
  rw [notDigit] at digit
  contradiction

private theorem renderedParts (generation : UInt64) (index : Nat) :
    ((renderRunFileName generation index).split '-').toList.map (·.copy) =
      ["run", generation.toNat.repr, index.repr ++ ".v3"] := by
  have rendered : renderRunFileName generation index =
      String.intercalate (String.singleton '-') ["run", generation.toNat.repr, index.repr ++ ".v3"] := by
    simp only [renderRunFileName, String.intercalate_cons_cons, String.intercalate_singleton,
      String.append_assoc]
    rfl
  rw [rendered, String.toList_split_intercalate]
  · rfl
  · intro part included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl
    · decide
    · exact decimal_excludes _ (by decide)
    · simp [String.toList_append, -Nat.toList_repr, decimal_excludes index (by decide : '-'.isDigit = false)]

private theorem renderedIndexParts (index : Nat) :
    ((index.repr ++ ".v3").split '.').toList.map (·.copy) = [index.repr, "v3"] := by
  have rendered : index.repr ++ ".v3" = String.intercalate (String.singleton '.') [index.repr, "v3"] := by
    simp only [String.intercalate_cons_cons, String.intercalate_singleton, String.append_assoc]
    rfl
  rw [rendered, String.toList_split_intercalate]
  · rfl
  · intro part included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl
    · exact decimal_excludes _ (by decide)
    · decide

/-- Every name produced for a run round-trips at its exact generation and index. -/
theorem parseRunFileName_render (generation : UInt64) (index : Nat) :
    parseRunFileName (renderRunFileName generation index) = some (generation, index) := by
  have parts : runFileNumbers (renderRunFileName generation index) = some (generation.toNat, index) := by
    simp [runFileNumbers, renderedParts, renderedIndexParts, Bind.bind, Option.bind, Pure.pure]
  have fits := generation.toNat_lt
  have restored : generation.toNat.toUInt64 = generation := UInt64.ofNat_toNat
  simp [parseRunFileName, parts, Bind.bind, Option.bind, fits, restored]

theorem parseRunFileName_eq_some_iff {name : String} {generation : UInt64} {index : Nat} :
    parseRunFileName name = some (generation, index) ↔ name = renderRunFileName generation index := by
  exact ⟨parseRunFileName_sound, fun equal => equal ▸ parseRunFileName_render generation index⟩

/-- Appending an accepted basename to the locked database directory selects
exactly the same path as the writer's run address. -/
theorem DiskDirectory.file_eq_parsedRun (dir : DiskDirectory) {name : String}
    {generation : UInt64} {index : Nat} (parsed : parseRunFileName name = some (generation, index)) :
    dir.file (.run generation index) = ⟨dir.path.toString ++ "/" ++ name⟩ := by
  rw [parseRunFileName_sound parsed]
  rfl

/-- An accepted string is a basename with no path delimiter or embedded NUL. -/
theorem parseRunFileName_basename {name : String} {generation : UInt64} {index : Nat}
    (parsed : parseRunFileName name = some (generation, index)) :
    '/' ∉ name.toList ∧ '\x00' ∉ name.toList := by
  rw [parseRunFileName_sound parsed]
  change '/' ∉ ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList ∧
    '\x00' ∉ ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList
  simp [String.toList_append, -Nat.toList_repr, decimal_excludes _ (by decide : '/'.isDigit = false),
    decimal_excludes _ (by decide : '\x00'.isDigit = false)]

end Alvoki.Storage
