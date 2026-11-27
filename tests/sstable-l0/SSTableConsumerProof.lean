import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.L0.ReadErrors
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadErrors

open ExperimentalL0 ImmutableSSTable ImmutableSSTable.Unified

/-- Instantiate the native component theorem with the actual L0 codecs.
The scoped caller supplies the acquired inode binding. -/
theorem l0_lookup_built_table [DecidableEq inode]
    {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath}
    {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before written : NativeWriteState writer inode} {count : Nat} {rows : Rows}
    {acquire : System.FilePath → IO.FS.Mode → EStateM String σ reader}
    {start acquired : σ} {held : reader} {inodeAt : reader → Option inode}
    (input : before.rows = rows.map (Entry.encode keyCodec mutationCodec))
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before =
      .ok count written)
    (opened : acquire readPath .read start = .ok held acquired)
    (selected : ∀ output identity, written.BoundTo path output identity →
      inodeAt held = some identity) :
    ∃ table,
      openCheckedWith ((written.readSnapshot inodeAt).primitives acquire)
        crc readPath layout.tableId start = .ok table acquired ∧
      ∀ key, (TypedTable.mk table keyCodec mutationCodec).lookup key =
        pure (lookupRows rows key) := by
  obtain ⟨_, table, checked, represents⟩ := buildFileWith_open_represents
    effects built opened selected
  rw [input] at represents
  exact ⟨table, checked, typed_lookup_spec (typed_table_from_bytes represents)⟩

theorem l0_lookup_after_miss_error {tables : Tables (StorageM σ)} {key : UInt64}
    {first needed : UInt64} {tail : List UInt64} {before middle reached : σ} {message : String}
    (miss : tables.lookup first key before = .ok none middle)
    (failure : tables.lookup needed key middle = .error message reached) :
    lookupTables tables key (first :: needed :: tail) before = .error message reached :=
  (RequiredReadError.later miss (.here failure)).propagates

/-- The selected data packet's positional read fails after routing succeeds.
The scoped adapter runs the typed lookup, so an older table is never probed. -/
theorem l0_lookup_selected_data_read_error
    {tables : Tables (StorageM σ)} {handle : Handle (StorageM σ)} {key : UInt64}
    {newer needed : UInt64} {older : List UInt64}
    {before start afterLeaf reached : σ} {message : String}
    {parent ref : Ref} {children : Array Ref}
    (miss : tables.lookup newer key before = .ok none start)
    (adapter : tables.lookup needed key start =
      (TypedTable.mk handle.table keyCodec mutationCodec).lookup key start)
    (rootChoice : findRef handle.root (fun r => decide (r.lastKey < keyCodec.encode key)) =
      some parent)
    (leafRead : handle.readLeaf parent start = .ok children afterLeaf)
    (dataChoice : findRef children (fun r => decide (r.lastKey < keyCodec.encode key)) = some ref)
    (bounds : checksumSize ≤ ref.size ∧ ref.size ≤ maxRowSize ∧
      ref.offset + ref.size ≤ maxFileSize)
    (failure : handle.source.readAt ref.offset ref.size afterLeaf = .error message reached) :
    lookupTables tables key (newer :: needed :: older) before = .error message reached := by
  have packet := readPacket_source_error (crc := handle.crc)
    (tableId := handle.layout.tableId) (kind := 1) bounds failure
  have routed := handle.locate_data_error rootChoice leafRead dataChoice
    (handle.readData_packet_error packet)
  have typedFailure := TypedTable.lookup_read_error
    (table := TypedTable.mk handle.table keyCodec mutationCodec)
    (handle.table_lookup_seek_error routed).1
  exact l0_lookup_after_miss_error miss (adapter.trans typedFailure)
