import Alvoki.Experiments.SSTable.Recursive.MetadataProofs
import Alvoki.Experiments.SSTable.Proofs.UnifiedSearch

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum Ref Data RefCovers encodeData encodeIndex encodePacket
  checksumSize)

structure DataAt (layout : Layout) (crc : Checksum) (image : ByteArray)
    (rows : List Entry) (ref : Ref) (endAt : Nat) : Prop where
  within : ref.offset + ref.size ≤ endAt
  count : 0 < ref.count
  rowExtent : ref.firstRow + ref.count ≤ rows.length
  fence : ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key
  body : ∃ block : Array Entry, block.size = ref.count ∧ ref.count ≤ maxFileSize ∧
    (∀ i (bound : i < block.size), block[i] = rowAt rows (ref.firstRow + i)) ∧
    (∀ i (bound : i < block.size), Unified.rowFits layout block[i] = true) ∧
    Unified.PacketAt crc layout.tableId dataKind image ref.offset ref.size (encodeData layout block)

structure IndexAt (layout : Layout) (crc : Checksum) (image : ByteArray)
    (rows : List Entry) (height : Nat) (ref : Ref) (endAt : Nat) (fence : Bool)
    (children : Array Ref) : Prop where
  packet : IndexPacketAt crc layout.tableId height image ref endAt children
  coverage : RefCovers rows ref.firstRow ref.count children
  bounds : Unified.checkChildren children ref.firstRow ref.count ref.offset = .ok ()
  lastKey : fence = true → children.back?.map Ref.lastKey = some ref.lastKey

/-- The same exact byte and row partition invariant at every index height.
Height zero describes one data block. The root has no parent fence. -/
def TreeInImage (layout : Layout) (crc : Checksum) (image : ByteArray)
    (rows : List Entry) (ref : Ref) (endAt : Nat) (fence : Bool) : Nat → Prop
  | 0 => DataAt layout crc image rows ref endAt
  | height + 1 =>
    ∃ children, IndexAt layout crc image rows (height + 1) ref endAt fence children ∧
      ∀ child ∈ children.toList, TreeInImage layout crc image rows child ref.offset true height

structure Image (layout : Layout) (crc : Checksum) (image : ByteArray)
    (rows : List Entry) : Prop where
  ordered : Ordered rows
  extent : image.size ≤ maxFileSize
  root : ∃ footer,
    footer.Valid ∧ footer.base.layout = layout ∧ footer.base.count = rows.length ∧
    footerPacketSize ≤ image.size ∧
    image.extract (image.size - footerPacketSize) image.size =
      encodePacket crc 0 footerKind 0 (encodeFooter footer) ∧
    if rows.isEmpty then image.size = footerPacketSize else
      footer.base.rootOffset + footer.base.rootSize = image.size - footerPacketSize ∧
      TreeInImage layout crc image rows footer.rootRef (image.size - footerPacketSize)
        false footer.height

theorem IndexAt.checked (node : IndexAt layout crc image rows height ref endAt fence children) :
    pageChildren (encodeIndex children) ref fence = .ok children := by
  cases fence
  · simp [pageChildren, decodePage_encode _ node.packet.shape, node.bounds,
      Bind.bind, Except.bind, pure, Except.pure]
  · simp [pageChildren, decodePage_encode _ node.packet.shape, node.bounds,
      node.lastKey rfl, Bind.bind, Except.bind, pure, Except.pure]

theorem DataAt.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (data : DataAt handle.layout handle.crc image rows ref endAt)
    (served : handle.source.Serves image) (valid : handle.layout.Valid) :
    ∃ block, handle.readData ref endAt = pure block ∧
      ∀ i, i < ref.count → block.readRow i = .ok (rowAt rows (ref.firstRow + i)) := by
  obtain ⟨contents, count, countLimit, rowMatches, widths, packet⟩ := data.body
  have refCount := data.count
  have positive : 0 < contents.size := by omega
  have bounded : contents.size ≤ maxFileSize := by omega
  have fits : (encodeData handle.layout contents).size ≤ maxRowSize := by
    have bound := packet.bounded
    rw [packet.size_eq] at bound
    omega
  obtain ⟨block, opened, _, reads⟩ :=
    Unified.openData_encodeData handle.layout contents valid positive bounded fits widths
  have lastIndex : ref.count - 1 < contents.size := by omega
  have lastRow := reads _ lastIndex
  rw [rowMatches] at lastRow
  have last : (rowAt rows (ref.firstRow + (ref.count - 1))).key = ref.lastKey := by
    rw [data.fence]
    congr 2
    omega
  refine ⟨block, ?_, ?_⟩
  · simp [Handle.readData, packet.read served data.within, ← count, opened, liftDecode,
      show contents.size - 1 = ref.count - 1 by omega, lastRow, last]
  · intro i bound
    have inside : i < contents.size := by omega
    rw [reads i inside, rowMatches]

/-- The route condition identifies an in-range row. It is instantiated with
either the row cursor or the global key lower bound. -/
def Routes (rows : List Entry) (index : Nat) (before : Ref → Bool) : Prop :=
  ∀ {first count refs}, RefCovers rows first count refs →
    first ≤ index → index < first + count →
    ∃ child ∈ refs.toList, Unified.findRef refs before = some child ∧
      child.firstRow ≤ index ∧ index < child.firstRow + child.count

theorem Routes.cursor (rows : List Entry) (index : Nat) :
    Routes rows index (fun ref => decide (ref.firstRow + ref.count ≤ index)) := by
  intro _ _ refs covers first last
  obtain ⟨i, hi, picked, lo, upper⟩ := covers.selectRow first last
  exact ⟨refs[i], by simp, picked, lo, upper⟩

theorem Routes.key {key : ByteArray} (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index) :
    Routes rows index (fun ref => decide (ref.lastKey < key)) := by
  intro _ _ refs covers first last
  obtain ⟨i, hi, picked, lo, upper⟩ := covers.selectKey lower first last
  exact ⟨refs[i], by simp, picked, lo, upper⟩

theorem TreeInImage.descend [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (served : source.Serves image)
    (route : Routes rows index before) (tree : TreeInImage layout crc image rows ref endAt true height)
    (lo : ref.firstRow ≤ index) (hi : index < ref.firstRow + ref.count) :
    ∃ data parent, descend source crc layout.tableId before ref endAt height = pure (data, parent) ∧
      DataAt layout crc image rows data parent ∧
      data.firstRow ≤ index ∧ index < data.firstRow + data.count := by
  induction height generalizing ref endAt with
  | zero => exact ⟨ref, endAt, rfl, tree, lo, hi⟩
  | succ depth ih =>
    obtain ⟨children, node, below⟩ := tree
    obtain ⟨child, member, picked, start, stop⟩ := route node.coverage lo hi
    obtain ⟨data, parent, ran, exactData, startData, stopData⟩ :=
      ih (below child member) start stop
    refine ⟨data, parent, ?_, exactData, startData, stopData⟩
    simp [Recursive.descend, node.packet.read served, node.checked, liftDecode, picked, ran]

/-- The checked reader observes the exact logical table recorded by its root
and recursively described descendants. -/
structure Handle.Observes [Monad m] (handle : Handle m)
    (image : ByteArray) (rows : List Entry) : Prop where
  serves : handle.source.Serves image
  valid : handle.layout.Valid
  count : handle.rowCount = rows.length
  root : RefCovers rows 0 rows.length handle.root
  children : ∀ child ∈ handle.root.toList,
    TreeInImage handle.layout handle.crc image rows child handle.rootOffset true (handle.height - 1)

private theorem Handle.Observes.select [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (observed : handle.Observes image rows)
    (route : Routes rows index before) (inside : index < rows.length) :
    ∃ rootChild ref data,
      Unified.findRef handle.root before = some rootChild ∧
      handle.select before rootChild = pure (ref, data) ∧
      ref.firstRow ≤ index ∧ index < ref.firstRow + ref.count ∧
      ref.firstRow + ref.count ≤ rows.length ∧
      ∀ i, i < ref.count → data.readRow i = .ok (rowAt rows (ref.firstRow + i)) := by
  obtain ⟨rootChild, member, picked, lo, hi⟩ := route observed.root (Nat.zero_le _) (by simpa)
  obtain ⟨ref, parent, routeRead, exactData, start, stop⟩ :=
    (observed.children rootChild member).descend observed.serves route lo hi
  obtain ⟨data, read, fits⟩ := exactData.read observed.serves observed.valid (handle := handle)
  exact ⟨rootChild, ref, data, picked, by simp [Handle.select, routeRead, read],
    start, stop, exactData.rowExtent, fits⟩

private theorem Handle.Observes.locate [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (observed : handle.Observes image rows)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (inside : index < rows.length) :
    ∃ ref data, handle.locate key = pure (some (ref, data, index - ref.firstRow)) ∧
      ref.firstRow ≤ index ∧ data.readRow (index - ref.firstRow) = .ok rows[index] := by
  obtain ⟨rootChild, ref, data, picked, read, start, stop, extent, reads⟩ :=
    observed.select (Routes.key lower) inside
  have localSeek := Unified.seek_local (m := m) reads lower start stop extent
  have rowInside : index - ref.firstRow < ref.count := by omega
  have rowRead := reads _ rowInside
  rw [Nat.add_sub_of_le start, rowAt_eq inside] at rowRead
  exact ⟨ref, data, by simp [Handle.locate, picked, read, localSeek, rowInside], start, rowRead⟩

theorem Handle.Observes.represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (observed : handle.Observes image rows) (ordered : Ordered rows) :
    handle.table.Represents rows := by
  refine ⟨ordered, observed.count, ?_, ?_, ?_⟩
  · intro key
    change handle.lookup key = _
    obtain ⟨index, lower⟩ := Unified.exists_lowerBound ordered key
    rw [Unified.lookup_of_lowerBound ordered lower]
    by_cases inside : index < rows.length
    · obtain ⟨ref, data, located, _, row⟩ := observed.locate lower inside
      simp [Handle.lookup, located, inside, row, liftDecode]
    · have atEnd : index = rows.length := by have := lower.1; omega
      subst index
      simp [Handle.lookup, Handle.locate, observed.root.noKey lower]
  · intro key
    change ∃ index, handle.seek key = _ ∧ _
    obtain ⟨index, lower⟩ := Unified.exists_lowerBound ordered key
    refine ⟨index, ?_, lower⟩
    by_cases inside : index < rows.length
    · obtain ⟨ref, data, located, start, _⟩ := observed.locate lower inside
      simp [Handle.seek, located, Nat.add_sub_of_le start]
    · have atEnd : index = rows.length := by have := lower.1; omega
      subst index
      simp [Handle.seek, Handle.locate, observed.root.noKey lower, observed.count]
  · intro index
    change handle.next index = _
    by_cases inside : index < rows.length
    · obtain ⟨rootChild, ref, data, picked, read, start, stop, _, reads⟩ :=
        observed.select (Routes.cursor rows index) inside
      have row := reads (index - ref.firstRow) (by omega)
      rw [Nat.add_sub_of_le start, rowAt_eq inside] at row
      simp [Handle.next, Contents.next, observed.count, inside, Nat.not_le_of_lt inside,
        picked, read, row, liftDecode]
    · simp [Handle.next, Contents.next, observed.count, inside, Nat.le_of_not_gt inside]

theorem Image.open_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (exact : Image layout crc image rows) (served : source.Serves image) :
    ∃ handle, openChecked source crc layout.tableId = pure handle ∧ handle.table.Represents rows := by
  obtain ⟨footer, valid, layoutEq, count, packetFits, footerBytes, root⟩ := exact.root
  let endAt := image.size - footerPacketSize
  have enough : endAt + footerPacketSize = image.size := Nat.sub_add_cancel packetFits
  have footerRead : readFooter source crc = pure (footer, endAt) := by
    have bytes := readExact_serves served (by decide : footerPacketSize ≤ maxRowSize)
      (Nat.le_of_eq enough)
    rw [enough, footerBytes] at bytes
    simp only [readFooter, served.size, pure_bind, packetFits, exact.extent, and_self,
      ↓reduceIte, endAt, bytes, Unified.decodePacket_encodePacket, decodeFooter_encode _ valid, liftDecode]
  have tableId : footer.base.layout.tableId = layout.tableId := by rw [layoutEq]
  have layoutValid := valid.base.1
  cases rows with
  | nil =>
    have empty : image.size = footerPacketSize := root
    have noData : endAt = 0 := by simp [endAt, empty]
    have zeroCount : footer.base.count = 0 := count
    have opened : ∃ handle, openChecked source crc layout.tableId = pure handle ∧
        handle.source = source ∧ handle.layout = footer.base.layout ∧
        handle.rowCount = 0 ∧ handle.root = #[] := by
      simp only [openChecked, footerRead, pure_bind, tableId, noData, zeroCount, eq_self,
        ↓reduceIte]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨handle, ran, src, lay, size, refs⟩ := opened
    refine ⟨handle, ran, Handle.Observes.represents (image := image) ?_ exact.ordered⟩
    refine ⟨src ▸ served, lay ▸ layoutValid, size, ?_, ?_⟩
    · rw [refs]
      exact ⟨by simp, by simp, by simp, by omega⟩
    · rw [refs]
      simp
  | cons row rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at root
    obtain ⟨rootEnd, tree⟩ := root
    have positive : footer.height ≠ 0 := fun zero => by
      have empty := valid.empty.mp zero
      simp [empty] at count
    obtain ⟨height, h⟩ := Nat.exists_eq_succ_of_ne_zero positive
    rw [h] at tree
    obtain ⟨children, node, below⟩ := tree
    have nonempty : footer.base.count ≠ 0 := by simp [count]
    have bytes := node.packet.read served
    have depthEq : footer.height = height + 1 := h
    rw [← depthEq] at bytes
    have opened : ∃ handle, openChecked source crc layout.tableId = pure handle ∧
        handle.source = source ∧ handle.layout = footer.base.layout ∧ handle.crc = crc ∧
        handle.rowCount = footer.base.count ∧ handle.root = children ∧
        handle.rootOffset = footer.rootRef.offset ∧ handle.height = footer.height := by
      simp only [openChecked, footerRead, pure_bind, tableId, eq_self, nonempty, rootEnd, endAt,
        ↓reduceIte, bytes, node.checked, liftDecode]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨handle, ran, src, lay, checksum, size, refs, offset, depth⟩ := opened
    refine ⟨handle, ran, Handle.Observes.represents (image := image) ?_ exact.ordered⟩
    refine ⟨src ▸ served, lay ▸ layoutValid, size.trans count, ?_, ?_⟩
    · rw [refs]
      simpa only [Footer.rootRef, count] using node.coverage
    · intro child member
      rw [offset, depth, h, Nat.succ_sub_one, lay, checksum, layoutEq]
      exact below child (refs ▸ member)

end ImmutableSSTable.Recursive
