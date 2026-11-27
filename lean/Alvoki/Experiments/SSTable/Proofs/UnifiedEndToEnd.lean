import Alvoki.Experiments.SSTable.Proofs.UnifiedOpen
import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder

namespace ImmutableSSTable.Unified

/-- A successful run of the executable writer, interpreted with an exact
append sink, yields a table whose actual indexed operations represent the
input rows when the opened immutable source serves the emitted bytes. -/
theorem open_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {crc : Checksum} {layout : Layout} {rows : List Entry}
    {options : BuildOptions} {count : Nat} {bytes : ByteArray}
    (built : modelBuild crc layout rows options = .ok (count, bytes))
    (served : source.Serves bytes) :
    count = rows.length ∧
      ∃ table, openTableChecked source crc layout.tableId = pure table ∧ table.Represents rows := by
  obtain ⟨countMatches, imageFacts⟩ := modelBuild_ok built
  exact ⟨countMatches, imageFacts.open_represents served⟩

end ImmutableSSTable.Unified
