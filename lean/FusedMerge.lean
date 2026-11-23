import SpanMerge

namespace Alvoki.FusedMerge
open Alvoki.Opt Alvoki.Packed

/-- Direct span emission with the bounded-window policy. Right wins a duplicate. -/
def merge (a b : @& Run) : ByteArray := mergeSpansWith a b true 1

theorem merge_eq (a b : Run) : merge a b = Alvoki.Packed.merge a b :=
  mergeSpansWith_eq a b true 1

/-- Consume the right-biased union into a wrapping XOR-and-sum checksum. -/
def scan (a b : @& Run) : UInt64 := scanMerged a b

theorem scan_refines (a b : Run) :
    scan a b = (mergedRows a b).foldl MergeModel.consume 0 :=
  scanMerged_refines a b

private def scanSelectedFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      let takeLeft := a < b
      let source := if takeLeft then left else right
      let index := if takeLeft then i else j
      let key := if takeLeft then a else b
      let nextI := if a ≤ b then i + 1 else i
      let nextJ := if b ≤ a then j + 1 else j
      scanSelectedFrom left right nextI nextJ (sum + (key ^^^ source.valueOrZero index))
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
