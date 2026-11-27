import Alvoki.Experiments.SSTable.FixedReader
import Alvoki.Experiments.SSTable.Proofs.FixedGeometry
import Alvoki.Experiments.SSTable.Proofs.Reader

namespace ImmutableSSTable.Fixed

theorem openLayout_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {image : ByteArray} {layout : Layout} {count : Nat}
    (served : source.Serves image) (fits : layout.Fits count)
    (extent : image.size = layout.fileSize count)
    (footer : image.extract (image.size - footerSize) image.size = encodeFooter layout count) :
    openLayout source = pure (layout, count) := by
  have bound : footerSize ≤ image.size := by rw [extent, Layout.fileSize]; omega
  have fileFits : image.size ≤ maxFileSize := extent ▸ fits.2.2
  have request : image.size - footerSize + footerSize ≤ image.size := by omega
  have read := served.readAt (image.size - footerSize) footerSize (by decide) request
  rw [Nat.sub_add_cancel bound, footer] at read
  simp only [openLayout, served.size, pure_bind, ite_eq_left (And.intro bound fileFits),
    read, decodeFooter_encodeFooter layout count fits, liftDecode, ite_eq_left extent.symm]

theorem readEntry_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {image payload : ByteArray} {layout : Layout} {count index : Nat}
    (served : source.Serves image) (valid : layout.Valid)
    (nonempty : 0 < layout.blockRows count (index / layout.rowsPerBlock))
    (size : payload.size = layout.blockRows count (index / layout.rowsPerBlock) * layout.rowWidth)
    (within : layout.blockOffset (index / layout.rowsPerBlock) +
      layout.blockReadSize count (index / layout.rowsPerBlock) ≤ image.size)
    (slice : image.extract (layout.blockOffset (index / layout.rowsPerBlock))
      (layout.blockOffset (index / layout.rowsPerBlock) +
        layout.blockReadSize count (index / layout.rowsPerBlock)) =
      encodeBlock layout (index / layout.rowsPerBlock) payload) :
    readEntry source layout count index = pure (readRow layout payload (index % layout.rowsPerBlock)) := by
  have read := served.readAt _ _ (Layout.blockReadSize_le layout valid count (index / layout.rowsPerBlock)) within
  rw [slice] at read
  simp only [readEntry, readBlock, ite_eq_left nonempty, read, pure_bind,
    decodeBlock_encodeBlock layout _ _ payload size, liftDecode]

/-- Transfer the physical indexed read result to the common public handle. -/
theorem open_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {layout : Layout} {rows : List Entry}
    (opened : openLayout source = pure (layout, rows.length))
    (reads : ∀ i (within : i < rows.length),
      readEntry source layout rows.length i = pure rows[i])
    (ordered : Ordered rows) :
    ∃ table, openTable source = pure table ∧ table.Represents rows := by
  let table := Table.ofReader rows.length (readEntry source layout rows.length)
  refine ⟨table, ?_, Table.represents_of_indexed_reads rfl ?_ ordered⟩
  · simp [openTable, opened, table]
  · intro i within
    rw [Table.ofReader_readEntry _ within, reads i within]

/-- The actual fixed reader represents the ordered rows supplied to the
shared streaming builder, under the same stable-source assumption as ALVSST03. -/
theorem open_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {layout : Layout} {rows : List Entry} {count : Nat} {image : ByteArray}
    (built : modelBuild layout rows = .ok (count, image)) (served : source.Serves image) :
    ∃ table, openTable source = pure table ∧ table.Represents rows := by
  obtain ⟨fits, ordered, widths, _, full, tail, rfl, groups, short, rfl⟩ := modelBuild_ok built
  have opened := openLayout_encoded served fits
    (encodeImage_extent layout full tail fits.1 groups short widths)
    (encodeImage_footer layout full tail)
  apply open_represents opened _ ordered
  intro i within
  obtain ⟨payload, nonempty, size, bounded, slice, row⟩ :=
    encodeImage_row_block layout full tail fits.1 groups short widths i within
  rw [readEntry_encoded served fits.1 nonempty size bounded slice, row]

/-- A failed physical block probe propagates its original error and reached state. -/
theorem readEntry_source_error {source : Source (EStateM String σ)} {layout : Layout}
    {count index : Nat} {before reached : σ} {message : String}
    (nonempty : 0 < layout.blockRows count (index / layout.rowsPerBlock))
    (failed : source.readAt (layout.blockOffset (index / layout.rowsPerBlock))
      (layout.blockReadSize count (index / layout.rowsPerBlock)) before = .error message reached) :
    readEntry source layout count index before = .error message reached := by
  simp [readEntry, readBlock, nonempty, Bind.bind, EStateM.bind, failed]

end ImmutableSSTable.Fixed
