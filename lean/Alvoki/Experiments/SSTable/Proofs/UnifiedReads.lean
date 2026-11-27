import Alvoki.Experiments.SSTable.Proofs.UnifiedImage
import Alvoki.Experiments.SSTable.Proofs.UnifiedData
import Alvoki.Experiments.SSTable.Proofs.Reader

namespace ImmutableSSTable.Unified

theorem PacketAt.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {image : ByteArray} {offset size endAt : Nat} {tableId kind : UInt64} {body : ByteArray}
    (packet : PacketAt crc tableId kind image offset size body) (served : source.Serves image)
    (extent : offset + size ≤ endAt) :
    readPacket source crc tableId kind offset size endAt = pure body := by
  have enough : checksumSize ≤ size := by rw [packet.size_eq]; omega
  have bytes := served.readAt offset size packet.bounded packet.extent
  rw [packet.slice] at bytes
  have exactLength : (encodePacket crc tableId kind offset body).size = size := by
    rw [encodePacket_size, packet.size_eq]
  simp only [readPacket, ite_eq_left (And.intro enough (And.intro packet.bounded extent)),
    bytes, pure_bind, exactLength, eq_self, ite_true, decodePacket_encodePacket, liftDecode]

theorem openChecked_image [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {image : ByteArray} {groups : Array LeafGroup} {rows : List Entry}
    {footer : Footer} (crc : Checksum) (served : source.Serves image)
    (extent : image.size ≤ maxFileSize) (footerFits : footer.Valid)
    (count : footer.count = rows.length)
    (footerAt : image.extract (image.size - (footerBodySize + checksumSize)) image.size =
      encodePacket crc 0 4 0 (encodeFooterBody footer))
    (footerWithin : footerBodySize + checksumSize ≤ image.size)
    (root : if rows.isEmpty then groups.isEmpty = true ∧ image.size = footerBodySize + checksumSize
      else ValidRefs (groups.map LeafGroup.ref) ∧
        checkChildren (groups.map LeafGroup.ref) 0 rows.length footer.rootOffset = .ok () ∧
        footer.rootOffset + footer.rootSize = image.size - (footerBodySize + checksumSize) ∧
        PacketAt crc footer.layout.tableId 3 image footer.rootOffset footer.rootSize
          (encodeIndex (groups.map LeafGroup.ref))) :
    ∃ handle, openChecked source crc footer.layout.tableId = pure handle ∧
      handle.rowCount = rows.length ∧ handle.root = groups.map LeafGroup.ref ∧
      handle.source = source ∧ handle.crc = crc ∧ handle.layout = footer.layout := by
  have sizeBound : footerBodySize + checksumSize ≤ maxRowSize := by decide
  have endEq := Nat.sub_add_cancel footerWithin
  have fread := served.readAt _ _ sizeBound (Nat.le_of_eq endEq)
  rw [endEq, footerAt] at fread
  have flength : (encodePacket crc 0 4 0 (encodeFooterBody footer)).size =
      footerBodySize + checksumSize := by rw [encodePacket_size, encodeFooterBody_size]
  have readsFooter : readFooter source crc = pure (footer, image.size - (footerBodySize + checksumSize)) := by
    simp only [readFooter, served.size, pure_bind, ite_eq_left (And.intro footerWithin extent),
      fread, flength, eq_self, ite_true, decodePacket_encodePacket,
      decodeFooterBody_encodeFooterBody footer footerFits, liftDecode]
  cases rows with
  | nil =>
    have zero : footer.count = 0 := count
    simp only [List.isEmpty_nil, ite_true] at root
    have empty : groups = #[] := Array.size_eq_zero_iff.mp (Array.isEmpty_iff_size_eq_zero.mp root.1)
    have noData : image.size - (footerBodySize + checksumSize) = 0 := by rw [root.2, Nat.sub_self]
    simp only [openChecked, readsFooter, pure_bind, zero, noData, eq_self, ite_true,
      empty, Array.map_empty, List.length_nil]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons row rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at root
    obtain ⟨valid, children, rootEnd, packet⟩ := root
    have rread := packet.read served (Nat.le_of_eq rootEnd)
    have notZero : (row :: rest).length ≠ 0 := by simp
    simp only [openChecked, readsFooter, pure_bind, eq_self, ite_true, count, ite_eq_right notZero,
      ite_eq_left rootEnd, rread, decodeIndex_encodeIndex _ valid, liftDecode, children]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LeafGroup.InImage.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {leaf : LeafGroup} (inImage : leaf.InImage handle.layout handle.crc image)
    (served : handle.source.Serves image) (limit : image.size ≤ maxFileSize) :
    handle.readLeaf leaf.ref = pure (leaf.blocks.map DataGroup.ref) := by
  have read := inImage.packet.read served (Nat.le_trans inImage.packet.extent limit)
  simp only [Handle.readLeaf, read, pure_bind, decodeIndex_encodeIndex _ inImage.refs, liftDecode,
    inImage.bounds, inImage.lastKey, eq_self, ite_true]

theorem DataGroup.InImage.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {group : DataGroup} (inImage : group.InImage handle.layout handle.crc image)
    (served : handle.source.Serves image) (limit : image.size ≤ maxFileSize)
    (valid : handle.layout.Valid) (countLimit : group.rows.size ≤ maxFileSize) :
    ∃ data, handle.readData group.ref = pure data ∧ data.count = group.rows.size ∧
      ∀ i (within : i < group.rows.size), data.readRow i = .ok group.rows[i] := by
  have bytes := inImage.packet.read served (Nat.le_trans inImage.packet.extent limit)
  have bodyFits : (encodeData handle.layout group.rows).size ≤ maxRowSize := by
    have bound := inImage.packet.bounded
    rw [inImage.packet.size_eq] at bound
    omega
  have widths (i : Nat) (within : i < group.rows.size) : Unified.rowFits handle.layout group.rows[i] = true :=
    inImage.rowFits group.rows[i] (by simp)
  obtain ⟨data, opened, dataCount, reads⟩ :=
    openData_encodeData handle.layout group.rows valid inImage.nonempty countLimit bodyFits widths
  have lastWithin : group.rows.size - 1 < group.rows.size := by have := inImage.nonempty; omega
  have lastRead := reads (group.rows.size - 1) lastWithin
  have lastKey : (group.rows[group.rows.size - 1]'lastWithin).key = group.ref.lastKey := by
    have fence := inImage.lastKey
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem lastWithin] at fence
    exact Option.some.inj fence
  refine ⟨data, ?_, dataCount, reads⟩
  simp only [Handle.readData, bytes, pure_bind, inImage.count_eq, opened, liftDecode,
    lastRead, lastKey, eq_self, ite_true]

end ImmutableSSTable.Unified
