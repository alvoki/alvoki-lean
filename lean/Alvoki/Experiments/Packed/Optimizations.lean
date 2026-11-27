import Alvoki.Proofs.Packed.PackedViewProofs

namespace Alvoki.Opt

structure ScalarRecord where
  key : UInt64
  value : UInt64

def decodeScalar (block : @& Block) : Array ScalarRecord := Id.run do
  let mut result := Array.emptyWithCapacity block.count
  for i in [0:block.count] do
    result := result.push ⟨block.key i, block.read (24 + i * 16)⟩
  return result

@[inline] def decodeFold (block : @& Block) : UInt64 := Id.run do
  let mut sum := 0
  for i in [0:block.count] do
    sum := sum + (block.key i ^^^ block.read (24 + i * 16))
  return sum

def validateCarry (block : @& Block) : Bool := Id.run do
  if block.count == 0 then return true
  let mut previous := block.key 0
  for i in [1:block.count] do
    let key := block.key i
    if previous >= key then return false
    previous := key
  return true

def searchNat (block : @& Block) (key : UInt64) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    if block.key mid < key then searchNat block key (mid + 1) hi
    else searchNat block key lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

private def View.decodeFrom (view : @& View) (i : USize)
    (records : Array ScalarRecord) : Array ScalarRecord :=
  if _h : i < view.count then
    view.decodeFrom (i + 1) (records.push ⟨view.keyOrZero i, view.valueOrZero i⟩)
  else records
termination_by view.count.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp _h
  have step := addOne i view.count order
  omega

def View.decode (view : @& View) : Array ScalarRecord :=
  view.decodeFrom 0 (Array.emptyWithCapacity view.count.toNat)

def encodeScalar (records : @& Array ScalarRecord) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (16 + records.size * 16)
  out := pushWordFast (pushWordFast out records.size.toUInt64) 1
  for record in records do
    out := pushWordFast (pushWordFast out record.key) record.value
  return out

private abbrev FixedBytes (size : Nat) := { bytes : ByteArray // bytes.size = size }

@[inline] private def storeLane (bytes : FixedBytes size) (offset lane : USize)
    (value : UInt64) (h : offset.toNat + lane.toNat < size) : FixedBytes size :=
  have index : (offset + lane).toNat < bytes.val.size := by
    rw [bytes.property, USize.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le ..) h
  ⟨bytes.val.uset (offset + lane) (splitByte value lane.toNat) index,
    by
      have hsize : bytes.val.data.size = size := bytes.property
      have hu := Array.size_uset (xs := bytes.val.data) (i := offset + lane)
        (v := splitByte value lane.toNat) (h := index)
      exact hu.trans hsize⟩

private theorem machineExtent (bytes : ByteArray) (offset extra : USize)
    (h : (decide (extra < bytes.usize) && decide (offset < bytes.usize - extra)) = true) :
    offset.toNat + extra.toNat < bytes.size := by
  have hsize : bytes.usize.toNat ≤ bytes.size := USize.toNat_ofNat_le
  have hle : extra ≤ bytes.usize :=
    USize.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1)
  have hi : offset < bytes.usize - extra := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ hle] at hi
  omega

@[inline] private def storeWordIn (bytes : FixedBytes size) (offset : USize)
    (value : UInt64) (extent : offset.toNat + 7 < size) : FixedBytes size :=
  have laneBound (n : Nat) (hn : n ≤ 7) :
      offset.toNat + (USize.ofNat n).toNat < size :=
    have small : (USize.ofNat n).toNat ≤ n := USize.toNat_ofNat_le
    by omega
  let b1 := storeLane bytes offset 0 value (laneBound 0 (by decide))
  let b2 := storeLane b1 offset 1 value (laneBound 1 (by decide))
  let b3 := storeLane b2 offset 2 value (laneBound 2 (by decide))
  let b4 := storeLane b3 offset 3 value (laneBound 3 (by decide))
  let b5 := storeLane b4 offset 4 value (laneBound 4 (by decide))
  let b6 := storeLane b5 offset 5 value (laneBound 5 (by decide))
  let b7 := storeLane b6 offset 6 value (laneBound 6 (by decide))
  storeLane b7 offset 7 value (laneBound 7 (by decide))

/-- Overwrite one little-endian word inside a caller-validated destination. -/
@[inline] def storeWordAt (bytes : ByteArray) (offset : USize) (value : UInt64)
    (extent : offset.toNat + 7 < bytes.size) : { out : ByteArray // out.size = bytes.size } :=
  storeWordIn ⟨bytes, rfl⟩ offset value extent

@[inline] def storeWord (bytes : ByteArray) (offset : USize) (value : UInt64) : ByteArray :=
  if h : 7 < bytes.usize && offset < bytes.usize - 7 then
    have extent := machineExtent bytes offset 7 h
    have seven : (7 : USize).toNat = 7 := USize.toNat_ofNat_of_lt_32 (by decide)
    (storeWordIn ⟨bytes, rfl⟩ offset value (by rwa [seven] at extent)).val
  else bytes

/-- Write both words with one extent check. A short destination is preserved. -/
@[inline] def storePair (bytes : ByteArray) (offset : USize) (key value : UInt64) : ByteArray :=
  if h : 15 < bytes.usize && offset < bytes.usize - 15 then
    have extent := machineExtent bytes offset 15 h
    have fifteen : (15 : USize).toNat = 15 := USize.toNat_ofNat_of_lt_32 (by decide)
    have bound : offset.toNat + 15 < bytes.size := by rwa [fifteen] at extent
    let middle := storeWordIn ⟨bytes, rfl⟩ offset key (by omega)
    (storeWordIn middle (offset + 8) value (by
      rw [USize.toNat_add, show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt_32 (by decide)]
      have hm := Nat.mod_le (offset.toNat + 8) (2 ^ System.Platform.numBits)
      omega)).val
  else bytes

/-- Grow a zero-filled destination by copying successively larger zero spans. -/
def zeroedBytes (size : Nat) : ByteArray := Id.run do
  if size == 0 then return ByteArray.empty
  let mut bytes := (ByteArray.emptyWithCapacity size).push 0
  while bytes.size < size do
    let half := bytes.size
    bytes := bytes.copySlice 0 bytes half (min half (size - half))
  return bytes

def encodeIndexed (records : @& Array ScalarRecord) : ByteArray := Id.run do
  let length := 16 + records.size * 16
  if length ≥ USize.size then return encodeScalar records
  let mut out := zeroedBytes length
  out := storeWord (storeWord out 0 records.size.toUInt64) 8 1
  let mut offset : USize := 16
  for record in records do
    out := storeWord (storeWord out offset record.key) (offset + 8) record.value
    offset := offset + 16
  return out

private def readUnalignedFrom (bytes : @& ByteArray) (i count : USize) (sum : UInt64) : UInt64 :=
  if _h : i < count then
    readUnalignedFrom bytes (i + 1) count (sum + wordMachine bytes (17 + i * 16))
  else sum
termination_by count.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp _h
  have step := addOne i count order
  omega

def View.readUnaligned (view : @& View) : UInt64 :=
  readUnalignedFrom view.bytes 0 view.count 0

private theorem View.decodeFrom_records (view : View) (i : USize) (out : Array ScalarRecord) :
    (view.decodeFrom i out).toList.map (fun row => (row.key, row.value)) =
      out.toList.map (fun row => (row.key, row.value)) ++
        (List.range' i.toNat (view.count.toNat - i.toNat)).map view.logicalRecord := by
  rw [View.decodeFrom]
  by_cases hit : i < view.count
  · have bound := USize.lt_iff_toNat_lt.mp hit
    have step := addOne i view.count bound
    have length : view.count.toNat - i.toNat = (view.count.toNat - (i + 1).toNat) + 1 := by omega
    rw [dite_eq_left hit, View.decodeFrom_records, Array.toList_push, List.map_append,
      length, List.range'_succ, List.map_cons, ← step, view.key_eq hit, view.value_eq hit,
      List.append_assoc]
    rfl
  · have noneLeft : view.count.toNat - i.toNat = 0 := by
      rw [USize.lt_iff_toNat_lt] at hit
      omega
    simp [hit, noneLeft]
termination_by view.count.toNat - i.toNat
decreasing_by omega

theorem View.decode_records (view : View) :
    view.decode.toList.map (fun row => (row.key, row.value)) =
      (List.range view.count.toNat).map view.logicalRecord := by
  rw [View.decode, view.decodeFrom_records,
    show (0 : USize).toNat = 0 from USize.toNat_ofNat_of_lt_32 (by decide),
    Nat.sub_zero, ← List.range_eq_range']
  rfl

private theorem storeLane_byte (bytes : FixedBytes size) (offset lane : USize)
    (v : UInt64) (extent : offset.toNat + lane.toNat < size)
    (fits : size < USize.size) (j : Nat) :
    (storeLane bytes offset lane v extent).val.data[j]? =
      if offset.toNat + lane.toNat = j then some (splitByte v lane.toNat) else bytes.val.data[j]? := by
  have exactOffset : (offset + lane).toNat = offset.toNat + lane.toNat := by
    rw [USize.toNat_add, Nat.mod_eq_of_lt (Nat.lt_trans extent fits)]
  obtain ⟨⟨data⟩, width⟩ := bytes
  unfold storeLane ByteArray.uset
  dsimp only
  rw [Array.uset_eq_set, Array.getElem?_set, exactOffset]

private theorem storeWordIn_byte (bytes : FixedBytes size) (offset : USize)
    (v : UInt64) (extent : offset.toNat + 7 < size) (fits : size < USize.size) (j : Nat) :
    (storeWordIn bytes offset v extent).val.data[j]? =
      if offset.toNat ≤ j ∧ j < offset.toNat + 8 then some (splitByte v (j - offset.toNat))
      else bytes.val.data[j]? := by
  have small (n : Nat) (h : n < 8) : (USize.ofNat n).toNat = n :=
    USize.toNat_ofNat_of_lt_32 (by omega)
  simp only [storeWordIn, storeLane_byte _ _ _ _ _ fits j,
    show (0 : USize).toNat = 0 from small 0 (by decide),
    show (1 : USize).toNat = 1 from small 1 (by decide),
    show (2 : USize).toNat = 2 from small 2 (by decide),
    show (3 : USize).toNat = 3 from small 3 (by decide),
    show (4 : USize).toNat = 4 from small 4 (by decide),
    show (5 : USize).toNat = 5 from small 5 (by decide),
    show (6 : USize).toNat = 6 from small 6 (by decide),
    show (7 : USize).toNat = 7 from small 7 (by decide)]
  by_cases hit : offset.toNat ≤ j ∧ j < offset.toNat + 8
  · have n : j = offset.toNat + 0 ∨ j = offset.toNat + 1 ∨ j = offset.toNat + 2 ∨
        j = offset.toNat + 3 ∨ j = offset.toNat + 4 ∨ j = offset.toNat + 5 ∨
        j = offset.toNat + 6 ∨ j = offset.toNat + 7 := by omega
    rcases n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hit]
  · have separate (n : Nat) (h : n < 8) : offset.toNat + n ≠ j := by omega
    simp [hit, show offset.toNat ≠ j by omega, separate 1 (by decide), separate 2 (by decide),
      separate 3 (by decide), separate 4 (by decide), separate 5 (by decide),
      separate 6 (by decide), separate 7 (by decide)]

@[simp] theorem storeWord_size (bytes : ByteArray) (offset : USize) (v : UInt64) :
    (storeWord bytes offset v).size = bytes.size := by
  unfold storeWord
  split
  · exact (storeWordIn ..).property
  · rfl

theorem storeWord_fallback (bytes : ByteArray) (offset : USize) (v : UInt64)
    (outside : ¬ (7 < bytes.usize && offset < bytes.usize - 7) = true) :
    storeWord bytes offset v = bytes := by
  unfold storeWord
  rw [dite_eq_right outside]

/-- For a machine-sized buffer and a valid extent, a word store changes exactly
its eight little-endian bytes. Every other byte and out-of-range index is preserved. -/
theorem storeWord_byte (bytes : ByteArray) (offset : USize) (v : UInt64)
    (fits : bytes.size < USize.size) (extent : offset.toNat + 7 < bytes.size) (j : Nat) :
    (storeWord bytes offset v).data[j]? =
      if offset.toNat ≤ j ∧ j < offset.toNat + 8 then some (splitByte v (j - offset.toNat))
      else bytes.data[j]? := by
  have size : bytes.usize.toNat = bytes.size := USize.toNat_ofNat_of_lt fits
  have seven : (7 : USize).toNat = 7 := USize.toNat_ofNat_of_lt_32 (by decide)
  have enough : (7 : USize) < bytes.usize := by rw [USize.lt_iff_toNat_lt, seven, size]; omega
  have bound : offset < bytes.usize - 7 := by
    rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ (USize.le_of_lt enough), seven, size]
    omega
  have guard : (7 < bytes.usize && offset < bytes.usize - 7) = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true enough, decide_eq_true bound⟩
  unfold storeWord
  rw [dite_eq_left guard]
  exact storeWordIn_byte ⟨bytes, rfl⟩ offset v extent fits j

end Alvoki.Opt
