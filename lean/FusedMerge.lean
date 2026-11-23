import NativeTune
import ScopedBytes

namespace Alvoki.FusedMerge
open Alvoki.Opt Alvoki.Packed Alvoki.ScopedBytes

@[inline] private def appendSpan (out : Builder) (view : @& View) (start stop : USize) : Builder :=
  out.copyToTail view.bytes (16 + start.toNat * 16) ((stop.toNat - start.toNat) * 16)

-- A small lookahead rejects short spans. Bound successful searches to a window
-- and copy the whole window directly when its last key still wins.
@[inline] private def windowEnd (view : @& View) (i : USize) (rival : UInt64)
    (consecutive : Bool) : USize :=
  if consecutive && view.count - i ≥ 8 && view.key (i + 7) < rival then
    let limit := i + min (view.count - i) 256
    if view.key (limit - 1) < rival then limit
    else searchMachineLoop (fun k => view.key k) rival (i + 8) limit
  else i + 1

@[inline] private def nextWinner (view : @& View) (i : USize) (rival : UInt64)
    (consecutive : Bool) : USize :=
  let stop := windowEnd view i rival consecutive
  if i + 1 < stop then stop else i + 1

private theorem nextWinner_progress (view : View) (i : USize) (rival : UInt64)
    (consecutive : Bool) :
    (i + 1).toNat ≤ (nextWinner view i rival consecutive).toNat := by
  unfold nextWinner
  dsimp only
  split
  next h => exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
  next _ => omega

private def mergeFrom (left right : @& View) (i j : USize) (a b : UInt64)
    (last : UInt8) (out : Builder) : Builder :=
  if hi : i < left.count then
    if hj : j < right.count then
      if a < b then
        let stop := nextWinner left i b (last == 0)
        have advance : (i + 1).toNat ≤ stop.toNat := nextWinner_progress left i b (last == 0)
        mergeFrom left right stop j (left.key stop) b 0 (appendSpan out left i stop)
      else if a == b then
        mergeFrom left right (i + 1) (j + 1) (left.key (i + 1)) (right.key (j + 1)) 2
          (appendSpan out right j (j + 1))
      else
        let stop := nextWinner right j a (last == 1)
        have advance : (j + 1).toNat ≤ stop.toNat := nextWinner_progress right j a (last == 1)
        mergeFrom left right i stop a (right.key stop) 1 (appendSpan out right j stop)
    else appendSpan out left i left.count
  else appendSpan out right j right.count
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    try dsimp [stop] at advance
    omega

/-- Direct span emission into the stock builder. Right wins a duplicate. -/
def merge (a b : @& Run) : ByteArray :=
  let capacity := 16 + (a.view.count.toNat + b.view.count.toNat) * 16
  let header := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity capacity) 0) 1
  let bytes := (mergeFrom a.view b.view 0 0 (a.view.key 0) (b.view.key 0) 2
    (Builder.ofPrefix header)).finish
  let count := pushWordFast (ByteArray.emptyWithCapacity 8) ((bytes.size - 16) / 16).toUInt64
  count.copySlice 0 bytes 0 8

private def scanFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.key i
      let b := right.key j
      if a < b then
        scanFrom left right (i + 1) j (sum + (a ^^^ left.value i))
      else if a == b then
        scanFrom left right (i + 1) (j + 1) (sum + (b ^^^ right.value j))
      else
        scanFrom left right i (j + 1) (sum + (b ^^^ right.value j))
    else sum + left.scan i left.count
  else sum + right.scan j right.count
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

/-- Consume the right-biased union into a wrapping XOR-and-sum checksum. -/
def scan (a b : @& Run) : UInt64 :=
  scanFrom a.view b.view 0 0 0

private def scanSelectedFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.key i
      let b := right.key j
      let takeLeft := a < b
      let source := if takeLeft then left else right
      let index := if takeLeft then i else j
      let key := if takeLeft then a else b
      let nextI := if a ≤ b then i + 1 else i
      let nextJ := if b ≤ a then j + 1 else j
      scanSelectedFrom left right nextI nextJ (sum + (key ^^^ source.value index))
    else sum + left.scan i left.count
  else sum + right.scan j right.count
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  have li := USize.lt_iff_toNat_lt.mp hi
  have rj := USize.lt_iff_toNat_lt.mp hj
  have ls := addOne i left.count li
  have rs := addOne j right.count rj
  have order := UInt64.le_total a b
  split <;> split <;> first | omega | (rcases order with h | h <;> contradiction)

/-- Select the source once and advance each cursor based on the key comparison. -/
def scanSelected (a b : @& Run) : UInt64 :=
  scanSelectedFrom a.view b.view 0 0 0

end Alvoki.FusedMerge
