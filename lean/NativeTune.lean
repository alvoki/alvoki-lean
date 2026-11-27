import Alvoki.Experiments.Packed.Optimizations
import Alvoki.Experiments.Merge.SpanMerge

namespace Alvoki.NativeTune
open Alvoki.Opt Alvoki.Packed

@[inline] private def loadLane (bytes : @& ByteArray) (i stride lane : USize)
    (h : i.toNat * stride.toNat + lane.toNat + 7 < bytes.size) : UInt64 :=
  wordBounded bytes (i * stride + lane) (by
    rw [USize.toNat_add, USize.toNat_mul]
    have hm := Nat.mod_le (i.toNat * stride.toNat) (2 ^ System.Platform.numBits)
    have ha := Nat.mod_le ((i.toNat * stride.toNat) % (2 ^ System.Platform.numBits) + lane.toNat)
      (2 ^ System.Platform.numBits)
    omega)

@[inline] private def pairAt (bytes : @& ByteArray) (i : USize) (stride lane : USize)
    (h : i.toNat * stride.toNat + lane.toNat + 15 < bytes.size) : UInt64 :=
  loadLane bytes i stride lane (by omega) ^^^
    loadLane bytes i stride (lane + 8) (by
      rw [USize.toNat_add, show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt_32 (by decide)]
      have hm := Nat.mod_le (lane.toNat + 8) (2 ^ System.Platform.numBits)
      omega)

private def scanOne (bytes : @& ByteArray) (i count : USize) (sum : UInt64)
    (extent : 16 + count.toNat * 16 ≤ bytes.size) : UInt64 :=
  if h : i < count then
    have order := USize.lt_iff_toNat_lt.mp h
    have wordSize : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt_32 (by decide)
    scanOne bytes (i + 1) count (sum + pairAt bytes i 16 16 (by rw [wordSize]; omega)) extent
  else sum
termination_by count.toNat - i.toNat
decreasing_by
  have next := addOne i count order
  omega

private def scanFour (bytes : @& ByteArray) (i groups : USize) (a b c d : UInt64)
    (extent : 16 + groups.toNat * 64 ≤ bytes.size) : UInt64 :=
  if h : i < groups then
    have order := USize.lt_iff_toNat_lt.mp h
    have stride : (64 : USize).toNat = 64 := USize.toNat_ofNat_of_lt_32 (by decide)
    have lane (offset : Nat) (valid : offset ≤ 64) :
        i.toNat * (64 : USize).toNat + (USize.ofNat offset).toNat + 15 < bytes.size := by
      rw [stride]
      have small : (USize.ofNat offset).toNat ≤ offset := USize.toNat_ofNat_le
      omega
    scanFour bytes (i + 1) groups
      (a + pairAt bytes i 64 16 (lane 16 (by decide)))
      (b + pairAt bytes i 64 32 (lane 32 (by decide)))
      (c + pairAt bytes i 64 48 (lane 48 (by decide)))
      (d + pairAt bytes i 64 64 (lane 64 (by decide))) extent
  else a + b + c + d
termination_by groups.toNat - i.toNat
decreasing_by
  have next := addOne i groups order
  omega

def scanScalar (run : @& Run) : UInt64 :=
  let view := run.view
  if h : 16 + view.count.toNat * 16 ≤ view.bytes.size then
    scanOne view.bytes 0 view.count 0 h
  else 0

def scanUnrolled (run : @& Run) : UInt64 :=
  let view := run.view
  let groups := view.count / 4
  if h : 16 + view.count.toNat * 16 ≤ view.bytes.size then
    have groupCount : groups.toNat = view.count.toNat / 4 := by
      dsimp [groups]
      rw [USize.toNat_div, show (4 : USize).toNat = 4 from USize.toNat_ofNat_of_lt_32 (by decide)]
    let sum := scanFour view.bytes 0 groups 0 0 0 0 (by omega)
    scanOne view.bytes (groups * 4) view.count sum h
  else 0

@[inline] private def appendSpan (view : @& View) (start stop : USize) (out : ByteArray) : ByteArray :=
  view.bytes.copySlice (16 + start.toNat * 16) out out.size
    ((stop.toNat - start.toNat) * 16) false

/-- Probe before doing a binary search so short winning spans take the one-record path. -/
@[inline] private def spanEnd (view : @& View) (start : USize) (key : UInt64) : USize :=
  if view.count - start ≥ 8 && view.keyOrZero (start + 7) < key then
    let endIndex := searchMachineLoop (fun i => view.keyOrZero i) key (start + 1) view.count
    if start + 1 < endIndex then endIndex else start + 1
  else start + 1

private theorem spanProgress (view : View) (start : USize) (key : UInt64) :
    (start + 1).toNat ≤ (spanEnd view start key).toNat := by
  unfold spanEnd
  split
  · dsimp only
    split
    next h => exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    next _ => omega
  · omega

private def mergeSpansFrom (left right : @& View) (i j : USize) (out : ByteArray) : ByteArray :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      if a < b then
        let next := spanEnd left i b
        mergeSpansFrom left right next j (appendSpan left i next out)
      else if a == b then
        mergeSpansFrom left right (i + 1) (j + 1) (appendSpan right j (j + 1) out)
      else
        let next := spanEnd right j a
        mergeSpansFrom left right i next (appendSpan right j next out)
    else appendSpan left i left.count out
  else appendSpan right j right.count out
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    have lp := spanProgress left i (right.keyOrZero j)
    have rp := spanProgress right j (left.keyOrZero i)
    omega

def mergeSpans (a b : @& Run) : ByteArray :=
  let capacity := 16 + (a.view.count.toNat + b.view.count.toNat) * 16
  let initial := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity capacity) 0) 1
  let out := mergeSpansFrom a.view b.view 0 0 initial
  let header := pushWordFast (ByteArray.emptyWithCapacity 8) ((out.size - 16) / 16).toUInt64
  header.copySlice 0 out 0 8

def mergeCached (a b : @& Run) (trigger : UInt8) : ByteArray :=
  mergeSpansWith a b false trigger

theorem mergeCached_eq (a b : Run) (trigger : UInt8) :
    mergeCached a b trigger = Alvoki.Packed.merge a b :=
  mergeSpansWith_eq a b false trigger

@[inline] private def copyAt (view : @& View) (start : USize) (len dst : Nat)
    (out : ByteArray) : ByteArray :=
  view.bytes.copySlice (16 + start.toNat * 16) out dst len false

private def mergeCopyIntoFrom (left right : @& View) (i j : USize) (dst : Nat)
    (out : ByteArray) : ByteArray × Nat :=
  if _hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      if a < b then
        mergeCopyIntoFrom left right (i + 1) j (dst + 16) (copyAt left i 16 dst out)
      else if a == b then
        mergeCopyIntoFrom left right (i + 1) (j + 1) (dst + 16) (copyAt right j 16 dst out)
      else
        mergeCopyIntoFrom left right i (j + 1) (dst + 16) (copyAt right j 16 dst out)
    else
      let len := (left.count.toNat - i.toNat) * 16
      (copyAt left i len dst out, dst + len)
  else
    let len := (right.count.toNat - j.toNat) * 16
    (copyAt right j len dst out, dst + len)
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have ls := addOne i left.count (USize.lt_iff_toNat_lt.mp _hi)
    have rs := addOne j right.count (USize.lt_iff_toNat_lt.mp hj)
    have li := USize.lt_iff_toNat_lt.mp _hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    omega

/-- Compare whole-record overwrite on a pre-sized buffer with append and indexed byte writes. -/
def mergeCopyInto (a b : @& Run) : ByteArray :=
  let capacity := 16 + (a.view.count.toNat + b.view.count.toNat) * 16
  if capacity ≥ USize.size then merge a b else
    let (bytes, used) := mergeCopyIntoFrom a.view b.view 0 0 16 (zeroedBytes capacity)
    let bytes := storePair bytes 0 ((used - 16) / 16).toUInt64 1
    if used == capacity then bytes else bytes.extract 0 used

private def patchLowFrom (bytes : ByteArray) (i count : USize)
    (extent : 16 + count.toNat * 16 ≤ bytes.size) : ByteArray :=
  if h : i < count then
    let offset := i * 16 + 24
    have order := USize.lt_iff_toNat_lt.mp h
    have bound : offset.toNat < bytes.size := by
      dsimp [offset]
      rw [USize.toNat_add, USize.toNat_mul]
      rw [show (16 : USize).toNat = 16 from USize.toNat_ofNat_of_lt_32 (by decide)]
      rw [show (24 : USize).toNat = 24 from USize.toNat_ofNat_of_lt_32 (by decide)]
      have hm := Nat.mod_le (i.toNat * 16) (2 ^ System.Platform.numBits)
      have ha := Nat.mod_le ((i.toNat * 16) % (2 ^ System.Platform.numBits) + 24)
        (2 ^ System.Platform.numBits)
      omega
    let updated := bytes.uset offset (bytes.uget offset bound ^^^ 1) bound
    have same : updated.size = bytes.size := by
      exact Array.size_uset bound
    patchLowFrom updated (i + 1) count (same ▸ extent)
  else bytes
termination_by count.toNat - i.toNat
decreasing_by
  have step := addOne i count order
  omega

/-- Copy the block once, then change only the byte affected by the low-bit transform. -/
def encodeCopyLow (run : @& Run) : ByteArray :=
  let view := run.view
  let bytes := view.bytes.extract 0 view.bytes.size
  if extent : 16 + view.count.toNat * 16 ≤ bytes.size then
    patchLowFrom bytes 0 view.count extent
  else bytes

/-- Copy the original block, then rewrite one full value word per record. -/
def encodeCopyWords (run : @& Run) (mask : UInt64) : ByteArray := Id.run do
  let view := run.view
  let mut out := view.bytes.extract 0 view.bytes.size
  for i in [0:view.count.toNat] do
    out := storeWord out (24 + i.toUSize * 16) (view.valueOrZero i.toUSize ^^^ mask)
  return out

/-- Re-encode a packed input into a fresh block, flipping the low bit of each value. -/
def encodeDirect (run : @& Run) : ByteArray := Id.run do
  let view := run.view
  let mut out := zeroedBytes view.bytes.size
  out := storeWord (storeWord out 0 view.count.toUInt64) 8 1
  for i in [0:view.count.toNat] do
    let offset := (16 + i * 16).toUSize
    out := storeWord (storeWord out offset (view.keyOrZero i.toUSize)) (offset + 8)
      (view.valueOrZero i.toUSize ^^^ 1)
  return out

def encodePair (run : @& Run) (mask : UInt64 := 1) : ByteArray := Id.run do
  let view := run.view
  let mut out := storePair (zeroedBytes view.bytes.size) 0 view.count.toUInt64 1
  for i in [0:view.count.toNat] do
    out := storePair out (16 + i.toUSize * 16) (view.keyOrZero i.toUSize) (view.valueOrZero i.toUSize ^^^ mask)
  return out

private def mergeIndexedFrom (left right : @& View) (i j dst : USize)
    (out : ByteArray) : ByteArray × Nat :=
  if _hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      if a < b then
        mergeIndexedFrom left right (i + 1) j (dst + 16)
          (storePair out dst a (left.valueOrZero i))
      else if a == b then
        mergeIndexedFrom left right (i + 1) (j + 1) (dst + 16)
          (storePair out dst b (right.valueOrZero j))
      else
        mergeIndexedFrom left right i (j + 1) (dst + 16)
          (storePair out dst b (right.valueOrZero j))
    else
      let remaining := (left.count.toNat - i.toNat) * 16
      (left.bytes.copySlice (16+i.toNat*16) out dst.toNat remaining false, dst.toNat + remaining)
  else
    let remaining := (right.count.toNat - j.toNat) * 16
    (right.bytes.copySlice (16+j.toNat*16) out dst.toNat remaining false, dst.toNat + remaining)
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp _hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

def mergeIndexed (a b : @& Run) : ByteArray :=
  let capacity := 16 + (a.view.count.toNat + b.view.count.toNat) * 16
  if capacity ≥ USize.size then merge a b else
    let (bytes, used) := mergeIndexedFrom a.view b.view 0 0 16 (zeroedBytes capacity)
    let bytes := storePair bytes 0 ((used - 16) / 16).toUInt64 1
    if used == capacity then bytes else bytes.extract 0 used

def encodeStaged (run : @& Run) : ByteArray := Id.run do
  let view := run.view
  let mut out := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity view.bytes.size)
    view.count.toUInt64) 1
  let mut scratch := zeroedBytes 4096
  let mut offset : USize := 0
  for i in [0:view.count.toNat] do
    scratch := storeWord (storeWord scratch offset (view.keyOrZero i.toUSize)) (offset + 8)
      (view.valueOrZero i.toUSize ^^^ 1)
    offset := offset + 16
    if offset == 4096 then
      out := scratch.copySlice 0 out out.size 4096 false
      offset := 0
  return scratch.copySlice 0 out out.size offset.toNat false

end Alvoki.NativeTune
