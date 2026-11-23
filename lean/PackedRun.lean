import Optimizations

namespace Alvoki.Packed
open Alvoki.Opt

structure Run where
  private mk ::
  view : View

def parseRun (bytes : ByteArray) : Except String Run := do
  if bytes.size < 16 || word bytes 8 != 1 then throw "expected version 1"
  return ⟨← parseView bytes⟩

private def mergeFrom (left right : @& View) (i j : USize)
    (out : ByteArray) : ByteArray :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.key i
      let b := right.key j
      if a < b then
        mergeFrom left right (i + 1) j
          (left.bytes.copySlice (16 + i.toNat * 16) out out.size 16 false)
      else if a == b then
        mergeFrom left right (i + 1) (j + 1)
          (right.bytes.copySlice (16 + j.toNat * 16) out out.size 16 false)
      else
        mergeFrom left right i (j + 1)
          (right.bytes.copySlice (16 + j.toNat * 16) out out.size 16 false)
    else left.bytes.copySlice (16 + i.toNat * 16) out out.size
      ((left.count.toNat - i.toNat) * 16) false
  else right.bytes.copySlice (16 + j.toNat * 16) out out.size
    ((right.count.toNat - j.toNat) * 16) false
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    try have leftOrder := USize.lt_iff_toNat_lt.mp hi
    try have leftStep := addOne i left.count leftOrder
    try have rightOrder := USize.lt_iff_toNat_lt.mp hj
    try have rightStep := addOne j right.count rightOrder
    omega

private def initialBuffer (left right : @& View) : ByteArray :=
  let capacity := 16 + (left.count.toNat + right.count.toNat) * 16
  pushWordFast (pushWordFast (ByteArray.emptyWithCapacity capacity) 0) 1

private def patchCount (merged : ByteArray) : ByteArray :=
  let header := pushWordFast (ByteArray.emptyWithCapacity 8) ((merged.size - 16) / 16).toUInt64
  header.copySlice 0 merged 0 8

private def appendPayload (source : @& View) (out : ByteArray) : ByteArray :=
  source.bytes.copySlice 16 out out.size (source.count.toNat * 16) false

/-- Merge two validated version-1 runs. The right input supplies the value on collision. -/
def merge (a b : @& Run) : ByteArray :=
  let left := a.view
  let right := b.view
  patchCount (mergeFrom left right 0 0 (initialBuffer left right))

/-- Use contiguous copies when the two key ranges are disjoint. -/
def mergeDisjointFast (a b : @& Run) : ByteArray :=
  let left := a.view
  let right := b.view
  if left.count == 0 then right.bytes
  else if right.count == 0 then left.bytes
  else if left.key (left.count - 1) < right.key 0 then
    patchCount (appendPayload right (appendPayload left (initialBuffer left right)))
  else if right.key (right.count - 1) < left.key 0 then
    patchCount (appendPayload left (appendPayload right (initialBuffer left right)))
  else merge a b

end Alvoki.Packed
