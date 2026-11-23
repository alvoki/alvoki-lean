import Optimizations
import NativeTune
import ScopedBytes

namespace Alvoki.MergePhases
open Alvoki.Opt Alvoki.Packed Alvoki.ScopedBytes

@[inline] private def consume (sum key value : UInt64) : UInt64 :=
  sum * 3 + (key ^^^ value)

private def consumeTail (view : @& View) (i : USize) (sum : UInt64) : UInt64 :=
  if h : i < view.count then
    consumeTail view (i + 1) (consume sum (view.keyUnchecked i) (view.valueUnchecked i))
  else sum
termination_by view.count.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp h
  have step := addOne i view.count order
  omega

private def selectFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyUnchecked i
      let b := right.keyUnchecked j
      if a < b then
        selectFrom left right (i + 1) j (consume sum a (left.valueUnchecked i))
      else if a == b then
        selectFrom left right (i + 1) (j + 1) (consume sum b (right.valueUnchecked j))
      else
        selectFrom left right i (j + 1) (consume sum b (right.valueUnchecked j))
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

/-- Check each trace decision against the heads of the validated runs before timing replay.
    0 emits left, 1 emits right, and 2 consumes equal keys and emits right. -/
def validateMergeTrace (trace : @& ByteArray) (left right : @& Run) : Bool := Id.run do
  let mut i : USize := 0
  let mut j : USize := 0
  for op in trace do
    if i >= left.count && j >= right.count then return false
    let expected : UInt8 :=
      if i < left.count then
        if j < right.count then
          let a := left.view.keyUnchecked i
          let b := right.view.keyUnchecked j
          if a < b then 0 else if a == b then 2 else 1
        else 0
      else 1
    if op != expected then return false
    if op != 1 then i := i + 1
    if op != 0 then j := j + 1
  return i == left.count && j == right.count

private def replayChecksumFrom (left right : @& View) (trace : @& ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) (sum : UInt64) : UInt64 :=
  if h : pos < endPos then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if op == 0 then
      replayChecksumFrom left right trace endPos extent (pos + 1) (i + 1) j
        (consume sum (left.keyUnchecked i) (left.valueUnchecked i))
    else
      let nextLeft := if op == 2 then i + 1 else i
      replayChecksumFrom left right trace endPos extent (pos + 1) nextLeft (j + 1)
        (consume sum (right.keyUnchecked j) (right.valueUnchecked j))
  else sum
termination_by endPos.toNat - pos.toNat
decreasing_by
  all_goals
    have step := addOne pos endPos order
    omega

private def replayWriteFrom (left right : @& View) (trace : @& ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) (out : Builder) : Builder :=
  if h : pos < endPos then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if op == 0 then
      replayWriteFrom left right trace endPos extent (pos + 1) (i + 1) j
        (out.copyToTail left.bytes (16 + i.toNat * 16) 16)
    else
      let nextLeft := if op == 2 then i + 1 else i
      replayWriteFrom left right trace endPos extent (pos + 1) nextLeft (j + 1)
        (out.copyToTail right.bytes (16 + j.toNat * 16) 16)
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
  (replayWriteFrom a.view b.view trace trace.usize USize.toNat_ofNat_le 0 0 0
    (Builder.ofPrefix header)).finish

private def replayModelFrom (left right : @& View) (trace : @& ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) : ByteArray :=
  if h : pos < endPos then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if op == 0 then
      let start := 16 + i.toNat * 16
      left.bytes.extract start (start + 16) ++
        replayModelFrom left right trace endPos extent (pos + 1) (i + 1) j
    else
      let start := 16 + j.toNat * 16
      let nextLeft := if op == 2 then i + 1 else i
      right.bytes.extract start (start + 16) ++
        replayModelFrom left right trace endPos extent (pos + 1) nextLeft (j + 1)
  else ByteArray.empty
termination_by endPos.toNat - pos.toNat
decreasing_by
  all_goals
    have step := addOne pos endPos order
    omega

private theorem replayWriteFrom_refines (left right : View) (trace : ByteArray)
    (endPos : USize) (extent : endPos.toNat ≤ trace.size)
    (pos i j : USize) (out : Builder) :
    (replayWriteFrom left right trace endPos extent pos i j out).finish =
      out.finish ++ replayModelFrom left right trace endPos extent pos i j := by
  rw [replayWriteFrom, replayModelFrom]
  by_cases h : pos < endPos
  · have order := USize.lt_iff_toNat_lt.mp h
    simp only [dite_eq_left h]
    split
    · rename_i eq
      rw [replayWriteFrom_refines, copyToTail_refines, ByteArray.append_assoc]
    · rename_i ne
      rw [replayWriteFrom_refines, copyToTail_refines, ByteArray.append_assoc]
  · simp [h]
termination_by endPos.toNat - pos.toNat
decreasing_by
  all_goals
    have step := addOne pos endPos order
    omega

/-- The sequence of record slices selected by the trace, excluding the header. -/
def replayPayloadModel (a b : Run) (trace : ByteArray) : ByteArray :=
  replayModelFrom a.view b.view trace trace.usize USize.toNat_ofNat_le 0 0 0

theorem replayWrite_refines (a b : Run) (trace : ByteArray) :
    replayWrite a b trace =
      pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (16 + trace.size * 16))
        trace.size.toUInt64) 1 ++ replayPayloadModel a b trace := by
  unfold replayWrite replayPayloadModel
  dsimp only
  exact replayWriteFrom_refines a.view b.view trace trace.usize
    (by exact USize.toNat_ofNat_le) 0 0 0
    (Builder.ofPrefix (pushWordFast (pushWordFast
      (ByteArray.emptyWithCapacity (16 + trace.size * 16)) trace.size.toUInt64) 1))

/-- The replay loop consumes this checked merge trace without per-record cursor checks. -/
structure ReplayPlan where
  private mk ::
  left : Run
  right : Run
  trace : ByteArray
  mergeTrace : validateMergeTrace trace left right = true

def checkReplayPlan (left right : Run) (trace : ByteArray) : Except String ReplayPlan :=
  if valid : validateMergeTrace trace left right then .ok ⟨left, right, trace, valid⟩
  else .error "invalid replay trace"

@[noinline] def ReplayPlan.write (plan : @& ReplayPlan) : ByteArray :=
  replayWrite plan.left plan.right plan.trace

private def recordSlice (run : Run) (start count : Nat) : Except String Slice :=
  let offset := 16 + start * 16
  let length := count * 16
  if h : offset + length ≤ run.view.bytes.size then
    .ok ⟨run.view.bytes, offset, length, h⟩
  else .error "replay extent exceeds input"

structure PreparedReplay where
  private mk ::
  count : Nat
  slices : Array Slice
  complete : Slice.totalLength slices = count * 16

/-- Coalesce consecutive records emitted from the same run. A collision emits
    right and advances the left cursor, so it can extend a right span. -/
def ReplayPlan.prepare (plan : @& ReplayPlan) : Except String PreparedReplay := do
  let mut slices : Array Slice := #[]
  let mut left := 0
  let mut right := 0
  let mut start := 0
  let mut count := 0
  let mut fromLeft := true
  for op in plan.trace do
    let takeLeft := op == 0
    let index := if takeLeft then left else right
    if count == 0 || takeLeft != fromLeft then
      if count != 0 then
        let source := if fromLeft then plan.left else plan.right
        slices := slices.push (← recordSlice source start count)
      start := index
      count := 0
      fromLeft := takeLeft
    count := count + 1
    if takeLeft || op == 2 then left := left + 1
    if !takeLeft then right := right + 1
  if count != 0 then
    let source := if fromLeft then plan.left else plan.right
    slices := slices.push (← recordSlice source start count)
  if h : Slice.totalLength slices = plan.trace.size * 16 then
    return ⟨plan.trace.size, slices, h⟩
  else
    throw "prepared replay length disagrees with trace"

/-- The prepared writer emits the concatenation specified by appendAll_refines. -/
def PreparedReplay.write (prepared : @& PreparedReplay) : ByteArray :=
  let capacity := 16 + prepared.count * 16
  let header := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity capacity)
    prepared.count.toUInt64) 1
  ((Builder.ofPrefix header).appendAll prepared.slices).finish

/-- Find the end of one span of records emitted from the same source. The
    second result counts skipped left records when this is a right span. -/
private def spanEnd (trace : @& ByteArray) (limit : USize) (extent : limit.toNat ≤ trace.size)
    (fromLeft : Bool) (origin pos skipped : USize) (progress : origin.toNat ≤ pos.toNat) :
    { result : USize × USize // origin.toNat ≤ result.1.toNat } :=
  if h : pos < limit then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    if (op == 0) == fromLeft then
      let nextSkipped := if op == 2 then skipped + 1 else skipped
      have step := addOne pos limit order
      spanEnd trace limit extent fromLeft origin (pos + 1) nextSkipped (by omega)
    else ⟨(pos, skipped), progress⟩
  else ⟨(pos, skipped), progress⟩
termination_by limit.toNat - pos.toNat
decreasing_by
  omega

private def replaySpansFrom (left right : @& View) (trace : @& ByteArray)
    (limit : USize) (extent : limit.toNat ≤ trace.size)
    (pos i j : USize) (out : Builder) : Builder :=
  if h : pos < limit then
    have order := USize.lt_iff_toNat_lt.mp h
    let op := trace.uget pos (by omega)
    let fromLeft := op == 0
    let next := pos + 1
    have step : next.toNat = pos.toNat + 1 := addOne pos limit order
    let continues := if hnext : next < limit then
      have nextOrder := USize.lt_iff_toNat_lt.mp hnext
      (trace.uget next (by omega) == 0) == fromLeft
    else false
    if continues then
      let span := spanEnd trace limit extent fromLeft next next
        (if op == 2 then 1 else 0) (Nat.le_refl _)
      have advance := span.property
      let count := span.val.1 - pos
      let bytes := count.toNat * 16
      if fromLeft then
        replaySpansFrom left right trace limit extent span.val.1 (i + count) j
          (out.copyToTail left.bytes (16 + i.toNat * 16) bytes)
      else
        replaySpansFrom left right trace limit extent span.val.1 (i + span.val.2) (j + count)
          (out.copyToTail right.bytes (16 + j.toNat * 16) bytes)
    else if fromLeft then
      replaySpansFrom left right trace limit extent next (i + 1) j
        (out.copyToTail left.bytes (16 + i.toNat * 16) 16)
    else
      replaySpansFrom left right trace limit extent next (if op == 2 then i + 1 else i) (j + 1)
        (out.copyToTail right.bytes (16 + j.toNat * 16) 16)
  else out
termination_by limit.toNat - pos.toNat
decreasing_by
  all_goals
    first
    | change limit.toNat - span.val.1.toNat < limit.toNat - pos.toNat
      omega
    | change limit.toNat - next.toNat < limit.toNat - pos.toNat
      omega

/-- Plan and emit one span at a time. No separate array of span descriptors is needed. -/
def ReplayPlan.writeSpans (plan : @& ReplayPlan) : ByteArray :=
  let trace := plan.trace
  let header := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (16 + trace.size * 16))
    trace.size.toUInt64) 1
  (replaySpansFrom plan.left.view plan.right.view trace trace.usize USize.toNat_ofNat_le
    0 0 0 (Builder.ofPrefix header)).finish

/-- Each byte selects one contiguous fixed-width group from the indicated run. -/
def validateGroups (trace : @& ByteArray) (left right width : Nat) : Bool := Id.run do
  let mut a := 0
  let mut b := 0
  for op in trace do
    if op == 0 then a := a + width
    else if op == 1 then b := b + width
    else return false
  return a == left && b == right

private def copyGroupsFrom (left right : @& ByteArray) (trace : @& ByteArray)
    (count : USize) (extent : count.toNat ≤ trace.size)
    (width pos : USize) (a b offset : Nat) (out : ByteArray) : ByteArray :=
  if h : pos < count then
    have order := USize.lt_iff_toNat_lt.mp h
    if trace.uget pos (by omega) == 0 then
      let next := left.copySlice a out offset width.toNat
      copyGroupsFrom left right trace count extent width (pos + 1)
        (a + width.toNat) b (offset + width.toNat) next
    else
      let next := right.copySlice b out offset width.toNat
      copyGroupsFrom left right trace count extent width (pos + 1)
        a (b + width.toNat) (offset + width.toNat) next
  else out
termination_by count.toNat - pos.toNat
decreasing_by all_goals
  have next := addOne pos count order
  omega

def copyGroups (left right : @& Run) (trace : @& ByteArray) (width : USize)
    (out : ByteArray) : ByteArray :=
  let out := storePair out 0 (left.view.count.toUInt64 + right.view.count.toUInt64) 1
  copyGroupsFrom left.view.bytes right.view.bytes trace trace.usize USize.toNat_ofNat_le
    width 0 16 16 16 out

/-- Reference copy expressed with array operations, independent of the runtime entry point. -/
private def copyModel (src dest : ByteArray) (a b n : Nat) : ByteArray :=
  ⟨dest.data.extract 0 b ++ src.data.extract a (a+n) ++
    dest.data.extract (b + min n (src.size - a)) dest.size⟩

def checkCopyContract : IO Unit := do
  let src := Id.run do
    let mut out := ByteArray.emptyWithCapacity 128
    for i in [0:128] do out := out.push i.toUInt8
    return out
  for width in [0, 16, 32, 64] do
    for (a, b, size, capacity) in [
        (3, 7, 96, 96), (3, 96, 96, 192), (3, 96, 96, 96),
        (123, 4, 96, 96), (130, 4, 96, 96), (3, 200, 96, 192)] do
      let dest := Id.run do
        let mut bytes := ByteArray.emptyWithCapacity capacity
        for _ in [0:size] do bytes := bytes.push 0xa5
        return bytes
      let expected := copyModel src dest a b width
      if src.copySlice a dest b width != expected then
        throw (IO.userError s!"copy contract failed at {a}, {b}, {width}")
      if src.copySlice a dest b width false != expected then
        throw (IO.userError "shared destination contract failed")
    if src.copySlice 3 src 7 width != copyModel src src 3 7 width then
      throw (IO.userError "aliased copy contract failed")

@[noinline] def denseRewrite (run : @& Run) : ByteArray :=
  Alvoki.NativeTune.encodeCopyWords run 0xfedcba9876543210

end Alvoki.MergePhases
