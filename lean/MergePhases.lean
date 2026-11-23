import PackedRun

namespace Alvoki.MergePhases
open Alvoki.Opt Alvoki.Packed

@[inline] private def consume (sum key value : UInt64) : UInt64 :=
  sum * 3 + (key ^^^ value)

private def consumeTail (view : @& View) (i : USize) (sum : UInt64) : UInt64 :=
  if h : i < view.count then
    consumeTail view (i + 1) (consume sum (view.key i) (view.value i))
  else sum
termination_by view.count.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp h
  have step := addOne i view.count order
  omega

private def selectFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.key i
      let b := right.key j
      if a < b then
        selectFrom left right (i + 1) j (consume sum a (left.value i))
      else if a == b then
        selectFrom left right (i + 1) (j + 1) (consume sum b (right.value j))
      else
        selectFrom left right i (j + 1) (consume sum b (right.value j))
    else consumeTail left i sum
  else consumeTail right j sum
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

def select (a b : @& Run) : UInt64 := selectFrom a.view b.view 0 0 0

/-- 0 consumes left, 1 consumes right, 2 consumes both and emits right.
    Check the trace's shape and cursor bounds before timing replay. -/
def validateTrace (trace : @& ByteArray) (left right : Nat) : Bool := Id.run do
  let mut i := 0
  let mut j := 0
  for op in trace do
    match op with
    | 0 =>
      if i ≥ left then return false
      i := i + 1
    | 1 =>
      if j ≥ right then return false
      j := j + 1
    | 2 =>
      if i ≥ left || j ≥ right then return false
      i := i + 1
      j := j + 1
    | _ => return false
  return i == left && j == right

private def replayChecksumFrom (left right : @& View) (trace : @& ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) (sum : UInt64) : UInt64 :=
  if h : pos < endPos then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if op == 0 then
      replayChecksumFrom left right trace endPos extent (pos + 1) (i + 1) j
        (consume sum (left.key i) (left.value i))
    else
      let nextLeft := if op == 2 then i + 1 else i
      replayChecksumFrom left right trace endPos extent (pos + 1) nextLeft (j + 1)
        (consume sum (right.key j) (right.value j))
  else sum
termination_by endPos.toNat - pos.toNat
decreasing_by
  all_goals
    have step := addOne pos endPos order
    omega

private def replayWriteFrom (left right : @& View) (trace : @& ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) (out : ByteArray) : ByteArray :=
  if h : pos < endPos then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if op == 0 then
      replayWriteFrom left right trace endPos extent (pos + 1) (i + 1) j
        (left.bytes.copySlice (16 + i.toNat * 16) out out.size 16 false)
    else
      let nextLeft := if op == 2 then i + 1 else i
      replayWriteFrom left right trace endPos extent (pos + 1) nextLeft (j + 1)
        (right.bytes.copySlice (16 + j.toNat * 16) out out.size 16 false)
  else out
termination_by endPos.toNat - pos.toNat
decreasing_by
  all_goals
    have step := addOne pos endPos order
    omega

def replayChecksum (a b : @& Run) (trace : @& ByteArray) : UInt64 :=
  replayChecksumFrom a.view b.view trace trace.usize USize.toNat_ofNat_le 0 0 0 0

def replayWrite (a b : @& Run) (trace : @& ByteArray) : ByteArray :=
  let header := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (16 + trace.size * 16))
    trace.size.toUInt64) 1
  replayWriteFrom a.view b.view trace trace.usize USize.toNat_ofNat_le 0 0 0 header

end Alvoki.MergePhases
