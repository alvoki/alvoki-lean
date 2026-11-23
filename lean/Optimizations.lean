import Block

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

@[inline] private def byteMachine (bytes : @& ByteArray) (offset i : USize)
    (bound : offset.toNat + i.toNat < bytes.size) : UInt64 :=
  (bytes.uget (offset + i) (by
    rw [USize.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le ..) bound)).toUInt64

/-- Assemble a word using proof-carrying machine-sized byte offsets. -/
@[inline] def wordMachine (bytes : @& ByteArray) (offset : USize) : UInt64 :=
  if h : 7 < bytes.usize && offset < bytes.usize - 7 then
    have hsize : bytes.usize.toNat ≤ bytes.size := USize.toNat_ofNat_le
    have hle : (7 : USize) ≤ bytes.usize :=
      USize.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1)
    have hb : offset.toNat + 7 < bytes.size := by
      have hi : offset < bytes.usize - 7 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
      rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ hle] at hi
      rw [show (7 : USize).toNat = 7 from USize.toNat_ofNat_of_lt_32 (by decide)] at hi
      omega
    have small (n : Nat) (hn : n ≤ 7) :
        offset.toNat + (USize.ofNat n).toNat < bytes.size :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_trans USize.toNat_ofNat_le hn) _) hb
    byteMachine bytes offset 0 (small 0 (by decide)) |||
      (byteMachine bytes offset 1 (small 1 (by decide)) <<< 8) |||
      (byteMachine bytes offset 2 (small 2 (by decide)) <<< 16) |||
      (byteMachine bytes offset 3 (small 3 (by decide)) <<< 24) |||
      (byteMachine bytes offset 4 (small 4 (by decide)) <<< 32) |||
      (byteMachine bytes offset 5 (small 5 (by decide)) <<< 40) |||
      (byteMachine bytes offset 6 (small 6 (by decide)) <<< 48) |||
      (byteMachine bytes offset 7 (small 7 (by decide)) <<< 56)
  else 0

private theorem byteMachine_eq (bytes : ByteArray) (offset i : USize)
    (limit : bytes.size < USize.size)
    (bound : offset.toNat + i.toNat < bytes.size) :
    byteMachine bytes offset i bound = (bytes.get! (offset.toNat + i.toNat)).toUInt64 := by
  have index : (offset + i).toNat = offset.toNat + i.toNat := by
    rw [USize.toNat_add]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bound limit)
  cases bytes with
  | mk data =>
    unfold byteMachine ByteArray.uget ByteArray.get!
    have valid : (offset + i).toNat < data.size := index ▸ bound
    change (data[(offset + i).toNat]'valid).toUInt64 = (data[offset.toNat + i.toNat]!).toUInt64
    rw [getElem!_pos data _ bound]
    exact congrArg UInt8.toUInt64 (getElem_congr_idx index)

theorem wordMachine_eq (bytes : ByteArray) (offset : USize)
    (limit : bytes.size < USize.size) (bound : offset.toNat + 7 < bytes.size) :
    wordMachine bytes offset = word bytes offset.toNat := by
  have sizeEq : bytes.usize.toNat = bytes.size := USize.toNat_ofNat_of_lt limit
  have seven : (7 : USize).toNat = 7 := USize.toNat_ofNat_of_lt_32 (by decide)
  have leSize : (7 : USize) ≤ bytes.usize := by
    rw [USize.le_iff_toNat_le, seven, sizeEq]
    omega
  have short : (7 : USize) < bytes.usize := by
    rw [USize.lt_iff_toNat_lt, seven, sizeEq]
    omega
  have inBounds : offset < bytes.usize - 7 := by
    rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ leSize, seven, sizeEq]
    omega
  have digit (n : Nat) (hn : n < 8) : (USize.ofNat n).toNat = n :=
    USize.toNat_ofNat_of_lt_32 (by omega)
  unfold wordMachine word joinBytes
  rw [dite_eq_left (Bool.and_eq_true_iff.mpr ⟨decide_eq_true short, decide_eq_true inBounds⟩)]
  simp only [byteMachine_eq _ _ _ limit,
    show (0 : USize).toNat = 0 from digit 0 (by decide),
    show (1 : USize).toNat = 1 from digit 1 (by decide),
    show (2 : USize).toNat = 2 from digit 2 (by decide),
    show (3 : USize).toNat = 3 from digit 3 (by decide),
    show (4 : USize).toNat = 4 from digit 4 (by decide),
    show (5 : USize).toNat = 5 from digit 5 (by decide),
    show (6 : USize).toNat = 6 from digit 6 (by decide),
    show (7 : USize).toNat = 7 from digit 7 (by decide)]

structure View where
  private mk ::
  bytes : ByteArray
  count : USize
  stride : USize
  values : USize

@[inline] def View.key (view : @& View) (i : USize) : UInt64 :=
  wordMachine view.bytes (16 + i * view.stride)

@[inline] def View.value (view : @& View) (i : USize) : UInt64 :=
  wordMachine view.bytes (view.values + i * view.stride)

private theorem addExact (a b : USize) (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem addOne (a b : USize) (h : a.toNat < b.toNat) :
    (a + 1).toNat = a.toNat + 1 := by
  have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
  have lim := b.toNat_lt_size
  rw [addExact, one]
  rw [one]
  omega

private def View.validateFrom (view : @& View) (index : USize) (previous : UInt64) : Bool :=
  if h : index < view.count then
    let key := view.key index
    if previous >= key then false
    else view.validateFrom (index + 1) key
  else true
termination_by view.count.toNat - index.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp h
  have step := addOne index view.count order
  omega

def View.validate (view : @& View) : Bool :=
  view.count == 0 || view.validateFrom 1 (view.key 0)

def validateCarry (block : @& Block) : Bool := Id.run do
  if block.count == 0 then return true
  let mut previous := block.key 0
  for i in [1:block.count] do
    let key := block.key i
    if previous >= key then return false
    previous := key
  return true

def parseView (bytes : ByteArray) : Except String View := do
  if bytes.size < 16 then throw "short header"
  let version := word bytes 8
  if version != 1 && version != 2 then throw "invalid header"
  let payload := bytes.size - 16
  let count := payload / 16
  if bytes.size ≥ USize.size || payload % 16 != 0 || (word bytes 0).toNat != count then
    throw "invalid length"
  let view := View.mk bytes count.toUSize (if version == 1 then 16 else 8)
    (if version == 1 then 24 else (16 + count * 8).toUSize)
  if !view.validate then throw "keys must increase"
  return view

def searchNat (block : @& Block) (key : UInt64) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    if block.key mid < key then searchNat block key (mid + 1) hi
    else searchNat block key lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem midpoint_toNat (lo hi : USize) (h : lo < hi) :
    (lo + (hi - lo) / 2).toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
  have order := USize.lt_iff_toNat_lt.mp h
  have half : (2 : USize).toNat = 2 := USize.toNat_ofNat_of_lt_32 (by decide)
  have distance : ((hi - lo) / 2).toNat = (hi.toNat - lo.toNat) / 2 := by
    rw [USize.toNat_div, USize.toNat_sub_of_le _ _ (USize.le_of_lt h), half]
  have lim := hi.toNat_lt_size
  rw [addExact, distance]
  rw [distance]
  omega

@[specialize] def searchMachineLoop (readKey : USize → UInt64) (key : UInt64)
    (lo hi : USize) : USize :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    have order := USize.lt_iff_toNat_lt.mp h
    have midNat : mid.toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := midpoint_toNat lo hi h
    have below : mid.toNat < hi.toNat := by omega
    have next := addOne mid hi below
    if readKey mid < key then searchMachineLoop readKey key (mid + 1) hi
    else searchMachineLoop readKey key lo mid
  else lo
termination_by hi.toNat - lo.toNat
decreasing_by all_goals (dsimp [mid] at midNat next below; omega)

@[inline] def searchMachine (readKey : USize → UInt64) (key : UInt64) (count : USize) : USize :=
  searchMachineLoop readKey key 0 count

@[inline] def View.lowerBound (view : @& View) (key : UInt64) : USize :=
  searchMachine (fun i => view.key i) key view.count

private def View.scanFrom (view : @& View) (index hi : USize) (sum : UInt64) : UInt64 :=
  if _h : index < hi then
    view.scanFrom (index + 1) hi (sum + (view.key index ^^^ view.value index))
  else sum
termination_by hi.toNat - index.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp _h
  have step := addOne index hi order
  omega

@[inline] def View.scan (view : @& View) (lo hi : USize) : UInt64 :=
  view.scanFrom lo (min hi view.count) 0

private def View.decodeFrom (view : @& View) (i : USize)
    (records : Array ScalarRecord) : Array ScalarRecord :=
  if _h : i < view.count then
    view.decodeFrom (i + 1) (records.push ⟨view.key i, view.value i⟩)
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

@[inline] private def storeWord (bytes : ByteArray) (offset : USize) (value : UInt64) : ByteArray :=
  if h : 7 < bytes.usize && offset < bytes.usize - 7 then
    have sizeBound : bytes.usize.toNat ≤ bytes.size := USize.toNat_ofNat_le
    have hle : (7 : USize) ≤ bytes.usize :=
      USize.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1)
    have hi : offset < bytes.usize - 7 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    have hiNat : offset.toNat < bytes.usize.toNat - 7 := by
      rwa [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ hle,
        show (7 : USize).toNat = 7 from USize.toNat_ofNat_of_lt_32 (by decide)] at hi
    have laneBound (n : Nat) (hn : n ≤ 7) :
        offset.toNat + (USize.ofNat n).toNat < bytes.size :=
      have small : (USize.ofNat n).toNat ≤ n := USize.toNat_ofNat_le
      by omega
    let b0 : FixedBytes bytes.size := ⟨bytes, rfl⟩
    let b1 := storeLane b0 offset 0 value (laneBound 0 (by decide))
    let b2 := storeLane b1 offset 1 value (laneBound 1 (by decide))
    let b3 := storeLane b2 offset 2 value (laneBound 2 (by decide))
    let b4 := storeLane b3 offset 3 value (laneBound 3 (by decide))
    let b5 := storeLane b4 offset 4 value (laneBound 4 (by decide))
    let b6 := storeLane b5 offset 5 value (laneBound 5 (by decide))
    let b7 := storeLane b6 offset 6 value (laneBound 6 (by decide))
    (storeLane b7 offset 7 value (laneBound 7 (by decide))).val
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

end Alvoki.Opt
