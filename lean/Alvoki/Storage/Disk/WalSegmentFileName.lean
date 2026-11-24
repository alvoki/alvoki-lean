import Alvoki.Storage.Disk.DiskPaths
import Std.Data.String.ToNat

namespace Alvoki.Storage

private theorem decimal_excludes (n : Nat) {separator : Char} (notDigit : separator.isDigit = false) :
    separator ∉ n.repr.toList := by
  intro found
  rw [Nat.toList_repr] at found
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) found
  rw [notDigit] at digit
  contradiction

/-- Accept exactly the writer's canonical spelling of the absolute segment start. -/
def parseWalSegmentName (name : String) : Option Nat := do
  let ["WAL", "segment", digits] := (name.split '-').toList.map (·.copy) | none
  let first ← digits.toNat?
  if name = renderWalSegmentName first then some first else none

private theorem renderedParts (first : Nat) :
    ((renderWalSegmentName first).split '-').toList.map (·.copy) = ["WAL", "segment", first.repr] := by
  have rendered : renderWalSegmentName first =
      String.intercalate (String.singleton '-') ["WAL", "segment", first.repr] := by
    simp only [renderWalSegmentName, String.intercalate_cons_cons, String.intercalate_singleton,
      String.append_assoc]
    rfl
  rw [rendered, String.toList_split_intercalate]
  · rfl
  · intro part included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl
    · decide
    · decide
    · exact decimal_excludes _ (by decide)

theorem parseWalSegmentName_render (first : Nat) :
    parseWalSegmentName (renderWalSegmentName first) = some first := by
  simp [parseWalSegmentName, renderedParts, Bind.bind, Option.bind]

theorem parseWalSegmentName_eq_some_iff {name : String} {first : Nat} :
    parseWalSegmentName name = some first ↔ name = renderWalSegmentName first := by
  refine ⟨?_, fun equal => equal ▸ parseWalSegmentName_render first⟩
  intro parsed
  unfold parseWalSegmentName at parsed
  split at parsed
  · simp only [Bind.bind, Option.bind] at parsed
    split at parsed
    · contradiction
    · dsimp only at parsed
      split at parsed
      · rename_i canonical
        cases parsed
        exact canonical
      · contradiction
  · contradiction

/-- An accepted basename names the same path as the writer's segment address. -/
theorem DiskDirectory.walSegment_path_of_parsed (dir : DiskDirectory) {name : String} {first : Nat}
    (parsed : parseWalSegmentName name = some first) :
    dir.file (.walSegment first) = ⟨dir.path.toString ++ "/" ++ name⟩ := by
  rw [parseWalSegmentName_eq_some_iff.mp parsed, dir.walSegment_path]

theorem DiskDirectory.walSegment_path_injective (dir : DiskDirectory) :
    Function.Injective (fun first => dir.file (.walSegment first)) := by
  intro left right same
  have names := congrArg System.FilePath.toString same
  simp only [dir.walSegment_path, String.append_right_inj] at names
  simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName names

theorem parseWalSegmentName_basename {name : String} {first : Nat}
    (parsed : parseWalSegmentName name = some first) : '/' ∉ name.toList ∧ '\x00' ∉ name.toList := by
  rw [parseWalSegmentName_eq_some_iff.mp parsed]
  simp [renderWalSegmentName, String.toList_append, -Nat.toList_repr,
    decimal_excludes _ (by decide : '/'.isDigit = false),
    decimal_excludes _ (by decide : '\x00'.isDigit = false)]

end Alvoki.Storage
