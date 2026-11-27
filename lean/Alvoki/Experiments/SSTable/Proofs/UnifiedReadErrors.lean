import Alvoki.Experiments.SSTable.UnifiedReader

namespace ImmutableSSTable

private theorem throw_state (message : String) (state : σ) :
    (throw message : EStateM String σ α) state = .error message state := rfl

attribute [local simp] throw_state

/-- A failed probe lies on the actual comparison path. Each preceding
probe supplies the state and comparison used for the next range. -/
inductive RequiredProbeError {σ : Type} (read : Nat → EStateM String σ Entry)
    (key : ByteArray) (message : String) (reached : σ) : Nat → Nat → σ → Prop where
  | here (range : lo < hi)
      (failed : read (lo + (hi - lo) / 2) start = .error message reached) :
      RequiredProbeError read key message reached lo hi start
  | right (range : lo < hi)
      (got : read (lo + (hi - lo) / 2) start = .ok row after)
      (less : row.key < key)
      (later : RequiredProbeError read key message reached (lo + (hi - lo) / 2 + 1) hi after) :
      RequiredProbeError read key message reached lo hi start
  | left (range : lo < hi)
      (got : read (lo + (hi - lo) / 2) start = .ok row after)
      (notLess : ¬ row.key < key)
      (later : RequiredProbeError read key message reached lo (lo + (hi - lo) / 2) after) :
      RequiredProbeError read key message reached lo hi start

theorem RequiredProbeError.propagates {read : Nat → EStateM String σ Entry}
    (path : RequiredProbeError read key message reached lo hi start) :
    seekBetween read key lo hi start = .error message reached := by
  induction path with
  | here range failed =>
    rw [seekBetween]
    simp [range, Bind.bind, EStateM.bind, failed]
  | right range got less _ ih =>
    rw [seekBetween]
    simpa [range, Bind.bind, EStateM.bind, got, less] using ih
  | left range got notLess _ ih =>
    rw [seekBetween]
    simpa [range, Bind.bind, EStateM.bind, got, notLess] using ih

namespace Unified

/-- All indexed packet kinds share this path. A callback failure is propagated
with its reached state. -/
theorem readPacket_source_error {source : Source (EStateM String σ)}
    (bounds : checksumSize ≤ size ∧ size ≤ maxRowSize ∧ offset + size ≤ endAt)
    (failed : source.readAt offset size start = .error message reached) :
    readPacket source crc tableId kind offset size endAt start = .error message reached := by
  simp [readPacket, bounds, Bind.bind, EStateM.bind, failed]

theorem readPacket_short_error {source : Source (EStateM String σ)}
    (bounds : checksumSize ≤ size ∧ size ≤ maxRowSize ∧ offset + size ≤ endAt)
    (received : source.readAt offset size start = .ok bytes reached) (short : bytes.size ≠ size) :
    readPacket source crc tableId kind offset size endAt start =
      .error "short SSTable packet read" reached := by
  simp [readPacket, bounds, Bind.bind, EStateM.bind, received, short]

theorem readPacket_decode_error {source : Source (EStateM String σ)}
    (bounds : checksumSize ≤ size ∧ size ≤ maxRowSize ∧ offset + size ≤ endAt)
    (received : source.readAt offset size start = .ok bytes reached) (exactSize : bytes.size = size)
    (failed : decodePacket crc tableId kind offset bytes = .error message) :
    readPacket source crc tableId kind offset size endAt start = .error message reached := by
  simp [readPacket, bounds, Bind.bind, EStateM.bind, received, exactSize, failed,
    liftDecode]

theorem readFooter_size_error {source : Source (EStateM String σ)}
    (failed : source.size start = .error message reached) :
    readFooter source crc start = .error message reached := by
  simp [readFooter, Bind.bind, EStateM.bind, failed]

theorem readFooter_extent_error {source : Source (EStateM String σ)}
    (sized : source.size start = .ok size reached)
    (bounds : ¬ (footerBodySize + checksumSize ≤ size ∧ size ≤ maxFileSize)) :
    readFooter source crc start = .error "invalid SSTable extent" reached := by
  simp [readFooter, Bind.bind, EStateM.bind, sized, bounds]

theorem readFooter_source_error {source : Source (EStateM String σ)}
    (sized : source.size start = .ok size afterSize)
    (bounds : footerBodySize + checksumSize ≤ size ∧ size ≤ maxFileSize)
    (failed : source.readAt (size - (footerBodySize + checksumSize)) (footerBodySize + checksumSize)
      afterSize = .error message reached) :
    readFooter source crc start = .error message reached := by
  simp [readFooter, Bind.bind, EStateM.bind, sized, bounds, failed]

theorem readFooter_short_error {source : Source (EStateM String σ)}
    (sized : source.size start = .ok size afterSize)
    (bounds : footerBodySize + checksumSize ≤ size ∧ size ≤ maxFileSize)
    (received : source.readAt (size - (footerBodySize + checksumSize)) (footerBodySize + checksumSize)
      afterSize = .ok bytes reached)
    (short : bytes.size ≠ footerBodySize + checksumSize) :
    readFooter source crc start = .error "short SSTable footer read" reached := by
  simp [readFooter, Bind.bind, EStateM.bind, sized, bounds, received, short]

theorem readFooter_packet_error {source : Source (EStateM String σ)}
    (sized : source.size start = .ok size afterSize)
    (bounds : footerBodySize + checksumSize ≤ size ∧ size ≤ maxFileSize)
    (received : source.readAt (size - (footerBodySize + checksumSize)) (footerBodySize + checksumSize)
      afterSize = .ok bytes reached)
    (exactSize : bytes.size = footerBodySize + checksumSize)
    (failed : decodePacket crc 0 4 0 bytes = .error message) :
    readFooter source crc start = .error message reached := by
  simp [readFooter, Bind.bind, EStateM.bind, sized, bounds, received, exactSize, failed,
    liftDecode]

theorem readFooter_decode_error {source : Source (EStateM String σ)}
    (sized : source.size start = .ok size afterSize)
    (bounds : footerBodySize + checksumSize ≤ size ∧ size ≤ maxFileSize)
    (received : source.readAt (size - (footerBodySize + checksumSize)) (footerBodySize + checksumSize)
      afterSize = .ok bytes reached)
    (exactSize : bytes.size = footerBodySize + checksumSize)
    (decoded : decodePacket crc 0 4 0 bytes = .ok body)
    (failed : decodeFooterBody body = .error message) :
    readFooter source crc start = .error message reached := by
  simp [readFooter, Bind.bind, EStateM.bind, sized, bounds, received, exactSize, decoded, failed,
    liftDecode, Pure.pure, EStateM.pure]

theorem openTableChecked_footer_error {source : Source (EStateM String σ)}
    (failed : readFooter source crc start = .error message reached) :
    openTableChecked source crc expectedId start = .error message reached := by
  simp [openTableChecked, openChecked, Bind.bind, EStateM.bind, failed]

/-- Identity rejection happens after the footer and before the root read. -/
theorem openTableChecked_identity_error {source : Source (EStateM String σ)}
    (footerRead : readFooter source crc start = .ok (footer, endAt) reached)
    (mismatch : footer.layout.tableId ≠ expectedId) :
    openTableChecked source crc expectedId start = .error "SSTable table ID mismatch" reached := by
  simp [openTableChecked, openChecked, Bind.bind, EStateM.bind, footerRead,
    mismatch]

theorem openTableChecked_root_error {source : Source (EStateM String σ)}
    (footerRead : readFooter source crc start = .ok (footer, endAt) afterFooter)
    (identity : footer.layout.tableId = expectedId) (nonempty : footer.count ≠ 0)
    (extent : footer.rootOffset + footer.rootSize = endAt)
    (failed : readPacket source crc expectedId 3 footer.rootOffset footer.rootSize endAt
      afterFooter = .error message reached) :
    openTableChecked source crc expectedId start = .error message reached := by
  simp [openTableChecked, openChecked, Bind.bind, EStateM.bind, footerRead,
    identity, nonempty, extent, failed]

theorem openTableChecked_root_decode_error {source : Source (EStateM String σ)}
    (footerRead : readFooter source crc start = .ok (footer, endAt) afterFooter)
    (identity : footer.layout.tableId = expectedId) (nonempty : footer.count ≠ 0)
    (extent : footer.rootOffset + footer.rootSize = endAt)
    (received : readPacket source crc expectedId 3 footer.rootOffset footer.rootSize endAt
      afterFooter = .ok raw reached)
    (failed : decodeIndex raw = .error message) :
    openTableChecked source crc expectedId start = .error message reached := by
  simp [openTableChecked, openChecked, Bind.bind, EStateM.bind, footerRead,
    identity, nonempty, extent, received, liftDecode, failed]

theorem Handle.readLeaf_packet_error {handle : Handle (EStateM String σ)}
    (failed : readPacket handle.source handle.crc handle.layout.tableId 2
      parent.offset parent.size maxFileSize start = .error message reached) :
    handle.readLeaf parent start = .error message reached := by
  simp [Handle.readLeaf, Bind.bind, EStateM.bind, failed]

theorem Handle.readLeaf_decode_error {handle : Handle (EStateM String σ)}
    (received : readPacket handle.source handle.crc handle.layout.tableId 2
      parent.offset parent.size maxFileSize start = .ok raw reached)
    (failed : decodeIndex raw = .error message) :
    handle.readLeaf parent start = .error message reached := by
  simp [Handle.readLeaf, Bind.bind, EStateM.bind, received, liftDecode, failed]

theorem Handle.readData_packet_error {handle : Handle (EStateM String σ)}
    (failed : readPacket handle.source handle.crc handle.layout.tableId 1
      ref.offset ref.size maxFileSize start = .error message reached) :
    handle.readData ref start = .error message reached := by
  simp [Handle.readData, Bind.bind, EStateM.bind, failed]

theorem Handle.readData_decode_error {handle : Handle (EStateM String σ)}
    (received : readPacket handle.source handle.crc handle.layout.tableId 1
      ref.offset ref.size maxFileSize start = .ok raw reached)
    (failed : openData handle.layout ref.count raw = .error message) :
    handle.readData ref start = .error message reached := by
  simp [Handle.readData, Bind.bind, EStateM.bind, received, liftDecode, failed]

theorem Handle.locate_leaf_error {handle : Handle (EStateM String σ)}
    (selected : findRef handle.root (fun ref => decide (ref.lastKey < key)) = some parent)
    (failed : handle.readLeaf parent start = .error message reached) :
    handle.locate key start = .error message reached := by
  simp [Handle.locate, selected, Bind.bind, EStateM.bind, failed]

theorem Handle.locate_data_error {handle : Handle (EStateM String σ)}
    (selected : findRef handle.root (fun ref => decide (ref.lastKey < key)) = some parent)
    (leafRead : handle.readLeaf parent start = .ok children afterLeaf)
    (chosen : findRef children (fun ref => decide (ref.lastKey < key)) = some ref)
    (failed : handle.readData ref afterLeaf = .error message reached) :
    handle.locate key start = .error message reached := by
  simp [Handle.locate, selected, leafRead, chosen, Bind.bind, EStateM.bind, failed]

theorem Handle.locate_row_probe_error {handle : Handle (EStateM String σ)}
    (selected : findRef handle.root (fun ref => decide (ref.lastKey < key)) = some parent)
    (leafRead : handle.readLeaf parent start = .ok children afterLeaf)
    (chosen : findRef children (fun ref => decide (ref.lastKey < key)) = some ref)
    (dataRead : handle.readData ref afterLeaf = .ok data afterData)
    (path : RequiredProbeError (fun i => liftDecode (data.readRow i)) key message reached
      0 ref.count afterData) :
    handle.locate key start = .error message reached := by
  simp [Handle.locate, selected, leafRead, chosen, dataRead, Bind.bind, EStateM.bind, path.propagates]

/-- The public key operations share the same required packet and row probes. -/
theorem Handle.table_lookup_seek_error {handle : Handle (EStateM String σ)}
    (failed : handle.locate key start = .error message reached) :
    handle.table.lookup key start = .error message reached ∧
      handle.table.seek key start = .error message reached := by
  simp [Handle.table, Handle.lookup, Handle.seek, Bind.bind, EStateM.bind, failed]

theorem Handle.table_lookup_row_error {handle : Handle (EStateM String σ)}
    (located : handle.locate key start = .ok (some (ref, data, index)) reached)
    (failed : data.readRow index = .error message) :
    handle.table.lookup key start = .error message reached := by
  simp [Handle.table, Handle.lookup, Bind.bind, EStateM.bind, located, liftDecode, failed]

theorem Handle.table_next_leaf_error {handle : Handle (EStateM String σ)}
    (within : index < handle.rowCount)
    (selected : findRef handle.root (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some parent)
    (failed : handle.readLeaf parent start = .error message reached) :
    handle.table.next index start = .error message reached := by
  simp [Handle.table, Handle.next, Nat.not_le.mpr within, selected, Bind.bind, EStateM.bind, failed]

theorem Handle.table_next_data_error {handle : Handle (EStateM String σ)}
    (within : index < handle.rowCount)
    (selected : findRef handle.root (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some parent)
    (leafRead : handle.readLeaf parent start = .ok children afterLeaf)
    (chosen : findRef children (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some ref)
    (failed : handle.readData ref afterLeaf = .error message reached) :
    handle.table.next index start = .error message reached := by
  simp [Handle.table, Handle.next, Nat.not_le.mpr within, selected, leafRead, chosen,
    Bind.bind, EStateM.bind, failed]

theorem Handle.table_next_row_error {handle : Handle (EStateM String σ)}
    (within : index < handle.rowCount)
    (selected : findRef handle.root (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some parent)
    (leafRead : handle.readLeaf parent start = .ok children afterLeaf)
    (chosen : findRef children (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some ref)
    (dataRead : handle.readData ref afterLeaf = .ok data reached)
    (failed : data.readRow (index - ref.firstRow) = .error message) :
    handle.table.next index start = .error message reached := by
  simp [Handle.table, Handle.next, Nat.not_le.mpr within, selected, leafRead, chosen, dataRead,
    Bind.bind, EStateM.bind, failed, liftDecode]

/-- The actual lookup preserves the error of its selected leaf read. -/
theorem Handle.lookup_leaf_error {handle : Handle (EStateM String σ)}
    {parent : Ref} {key : ByteArray} {start reached : σ} {message : String}
    (selected : findRef handle.root (fun ref => decide (ref.lastKey < key)) = some parent)
    (bounds : checksumSize ≤ parent.size ∧ parent.size ≤ maxRowSize ∧
      parent.offset + parent.size ≤ maxFileSize)
    (failed : handle.source.readAt parent.offset parent.size start = .error message reached) :
    handle.lookup key start = .error message reached :=
  (handle.table_lookup_seek_error
    (handle.locate_leaf_error selected (handle.readLeaf_packet_error
      (readPacket_source_error bounds failed)))).1

end Unified

theorem TypedTable.seek_read_error {table : TypedTable (EStateM String σ) κ ν}
    (failed : table.table.seek (table.keyCodec.encode key) start = .error error reached) :
    table.seek key start = .error error reached :=
  failed

theorem TypedTable.lookup_read_error {table : TypedTable (EStateM String σ) κ ν}
    (failed : table.table.lookup (table.keyCodec.encode key) start = .error message reached) :
    table.lookup key start = .error message reached := by
  simp [TypedTable.lookup, Bind.bind, EStateM.bind, failed]

theorem TypedTable.lookup_decode_error {table : TypedTable (EStateM String σ) κ ν}
    (received : table.table.lookup (table.keyCodec.encode key) start = .ok (some value) reached)
    (failed : table.valueCodec.decode value = .error message) :
    table.lookup key start = .error message reached := by
  simp [TypedTable.lookup, Bind.bind, EStateM.bind, received, liftDecode, failed]

theorem TypedTable.next_read_error {table : TypedTable (EStateM String σ) κ ν}
    (failed : table.table.next index start = .error message reached) :
    table.next index start = .error message reached := by
  simp [TypedTable.next, Bind.bind, EStateM.bind, failed]

theorem TypedTable.next_key_decode_error {table : TypedTable (EStateM String σ) κ ν}
    (received : table.table.next index start = .ok (some (row, nextIndex)) reached)
    (failed : table.keyCodec.decode row.key = .error message) :
    table.next index start = .error message reached := by
  simp [TypedTable.next, Bind.bind, EStateM.bind, received, liftDecode, failed]

theorem TypedTable.next_value_decode_error {table : TypedTable (EStateM String σ) κ ν}
    (received : table.table.next index start = .ok (some (row, nextIndex)) reached)
    (keyDecoded : table.keyCodec.decode row.key = .ok key)
    (failed : table.valueCodec.decode row.value = .error message) :
    table.next index start = .error message reached := by
  simp [TypedTable.next, Bind.bind, EStateM.bind, received, liftDecode, keyDecoded, failed,
    Pure.pure, EStateM.pure]

end ImmutableSSTable
