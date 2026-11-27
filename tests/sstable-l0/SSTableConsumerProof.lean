import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.L0.ReadErrors
import Alvoki.Experiments.SSTable.Proofs.UnifiedEndToEnd

open ExperimentalL0 ImmutableSSTable

theorem l0_lookup_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : Rows} {layout : Unified.Layout} {count : Nat} {bytes : ByteArray}
    {crc : Unified.Checksum} {options : Unified.BuildOptions}
    (built : Unified.modelBuild crc layout (rows.map (Entry.encode keyCodec mutationCodec))
      options = .ok (count, bytes))
    (served : source.Serves bytes) :
    ∃ table, Unified.openTableChecked source crc layout.tableId = pure table ∧
      ∀ key, (TypedTable.mk table keyCodec mutationCodec).lookup key =
        pure (lookupRows rows key) := by
  obtain ⟨_, table, opened, represents⟩ := Unified.open_built_table built served
  exact ⟨table, opened, typed_lookup_spec (typed_table_from_bytes represents)⟩

theorem l0_lookup_after_miss_error {tables : Tables (StorageM σ)} {key : UInt64}
    {first needed : UInt64} {tail : List UInt64} {before middle reached : σ} {message : String}
    (miss : tables.lookup first key before = .ok none middle)
    (failure : tables.lookup needed key middle = .error message reached) :
    lookupTables tables key (first :: needed :: tail) before = .error message reached :=
  (RequiredReadError.later miss (.here failure)).propagates
