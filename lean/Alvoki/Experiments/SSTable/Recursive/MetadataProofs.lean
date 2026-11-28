import Alvoki.Experiments.SSTable.Recursive.Reader
import Alvoki.Experiments.SSTable.Proofs.UnifiedReads

namespace ImmutableSSTable.Recursive

open Unified (Ref Checksum checksumSize refPrefixSize encodePacket decodePacket encodeIndex
  encodeIndex_minSize decodeRefs_encodeIndex encodePacket_size decodePacket_encodePacket)

/-- One reusable shape condition for every level, including the two-entry
exception to the ordinary packet bound. -/
structure PageValid (refs : Array Ref) : Prop where
  nonempty : 0 < refs.size
  bounded : (encodeIndex refs).size + checksumSize ≤ maxIndexSize
  overflow : (encodeIndex refs).size + checksumSize ≤ maxRowSize || refs.size == 2
  keys : refs.all (fun ref => Unified.indexEntrySize ref.lastKey + checksumSize ≤ maxRowSize)
  adjacent : Unified.ValidRefsAfter none refs.toList

theorem decodePage_encode (refs : Array Ref) (valid : PageValid refs) :
    decodePage (encodeIndex refs) = .ok refs := by
  have limit : maxIndexSize ≤ maxFileSize := by decide
  have bytes := valid.bounded
  have fits : (encodeIndex refs).size ≤ maxFileSize := by omega
  simp only [decodePage, encodeIndex_minSize refs valid.nonempty, valid.bounded, and_self,
    ↓reduceIte, decodeRefs_encodeIndex _ valid.adjacent fits, Except.bind, Bind.bind,
    valid.overflow, valid.keys, pure, Except.pure]

structure IndexPacketAt (crc : Checksum) (id : UInt64) (height : Nat) (image : ByteArray)
    (ref : Ref) (endAt : Nat) (refs : Array Ref) : Prop where
  shape : PageValid refs
  extent : ref.offset + ref.size ≤ endAt
  within : endAt ≤ image.size
  length : ref.size = (encodeIndex refs).size + checksumSize
  slice : image.extract ref.offset (ref.offset + ref.size) =
    encodePacket crc id (indexKind height) ref.offset (encodeIndex refs)

theorem readExact_serves [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    (served : source.Serves image) (limit : size ≤ maxRowSize)
    (extent : offset + size ≤ image.size) :
    readExact (m := m) source offset size = pure (image.extract offset (offset + size)) := by
  have length : (image.extract offset (offset + size)).size = size := by simp [extent]
  simp [readExact, served.readAt _ _ limit extent, length]

theorem IndexPacketAt.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {id : UInt64} (packet : IndexPacketAt crc id height image ref endAt refs)
    (served : source.Serves image) :
    readIndexPacket source crc id height ref endAt = pure (encodeIndex refs) := by
  have whole : ref.offset + ref.size ≤ image.size := Nat.le_trans packet.extent packet.within
  have nonzero : checksumSize ≤ ref.size := by rw [packet.length]; omega
  have bound : ref.size ≤ maxIndexSize := by rw [packet.length]; exact packet.shape.bounded
  have read : readIndexBytes source ref = pure (image.extract ref.offset (ref.offset + ref.size)) := by
    unfold readIndexBytes
    split
    · exact readExact_serves served (by assumption) whole
    · rename_i large
      have simplify : ref.offset + maxRowSize + (ref.size - maxRowSize) = ref.offset + ref.size :=
        by omega
      have tailBound : ref.size - maxRowSize ≤ maxRowSize := by
        unfold maxIndexSize at bound
        omega
      rw [readExact_serves served (Nat.le_refl _) (by omega), pure_bind,
        readExact_serves served tailBound (by omega), pure_bind, simplify,
        ← ByteArray.extract_eq_extract_append_extract (ref.offset + maxRowSize) (by omega) (by omega)]
  have good : checkedChild ref endAt maxIndexSize = .ok () := by
    simp [checkedChild, nonzero, bound, packet.extent]
  simp only [readIndexPacket, good, liftDecode, pure_bind, read, packet.slice, decodePacket_encodePacket]

private theorem footerPayload_size (footer : Footer) :
    (magic ++ (Unified.encodeFooterBody footer.base).extract 8 Unified.footerBodySize).size =
      Unified.footerBodySize := by
  simp [Unified.footerBodySize, show magic.size = 8 by rfl]

@[simp] theorem encodeFooter_size (footer : Footer) :
    (encodeFooter footer).size = footerBodySize := by
  unfold encodeFooter footerBodySize
  rw [Alvoki.ByteWords.pushWordFast_size, footerPayload_size]

structure Footer.Valid (footer : Footer) : Prop where
  base : footer.base.Valid
  height : footer.height ≤ maxHeight
  empty : footer.height = 0 ↔ footer.base.count = 0

theorem decodeFooter_encode (footer : Footer) (valid : footer.Valid) :
    decodeFooter (encodeFooter footer) = .ok footer := by
  let tail := (Unified.encodeFooterBody footer.base).extract 8 Unified.footerBodySize
  have tailSize : tail.size = Unified.footerBodySize - 8 := by
    simp [tail]
  have fullSize : (magic ++ tail).size = Unified.footerBodySize := footerPayload_size footer
  have width : magic.size = 8 := rfl
  have inner : Unified.magic ++ tail = Unified.encodeFooterBody footer.base := by
    have splitAtMagic := ByteArray.extract_eq_extract_append_extract
      (a := Unified.encodeFooterBody footer.base) (i := 0) (k := Unified.footerBodySize)
      8 (by decide) (by decide)
    rw [Unified.encodeFooterBody_magic] at splitAtMagic
    rw [← splitAtMagic, ← Unified.encodeFooterBody_size footer.base, ByteArray.extract_zero_size]

  have newMagic : (encodeFooter footer).extract 0 8 = magic := by
    unfold encodeFooter
    rw [Alvoki.ByteWords.pushWordFast_append]
    rw [ByteArray.append_assoc, ByteArray.extract_append_eq_left width.symm]
  have newTail : (encodeFooter footer).extract 8 Unified.footerBodySize = tail := by
    change (Alvoki.pushWordFast (magic ++ tail) footer.height.toUInt64).extract
      8 Unified.footerBodySize = tail
    rw [Alvoki.ByteWords.pushWordFast_append]
    have trim := ByteArray.extract_append_size_left (a := magic ++ tail)
      (b := Alvoki.pushWordFast ByteArray.empty footer.height.toUInt64) (i := 8)
    rw [fullSize] at trim
    rw [trim]
    exact ByteArray.extract_append_eq_right width.symm (by rw [width, tailSize]; decide)
  have depthWord : (Alvoki.word (encodeFooter footer) Unified.footerBodySize).toNat = footer.height := by
    change (Alvoki.word (Alvoki.pushWordFast (magic ++ tail) footer.height.toUInt64)
      Unified.footerBodySize).toNat = footer.height
    rw [← fullSize, Alvoki.pushWordFast_roundtrip]
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt valid.height (by decide))
  have header : (decide ((encodeFooter footer).size = footerBodySize) &&
      (encodeFooter footer).extract 0 8 == magic) = true := by simp [newMagic]
  simp only [decodeFooter, header, ↓reduceIte, newTail, inner, Bind.bind, Except.bind,
    Unified.decodeFooterBody_encodeFooterBody _ valid.base, depthWord, valid.height, valid.empty,
    and_self, pure, Except.pure]

end ImmutableSSTable.Recursive
