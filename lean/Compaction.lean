import PackedView
import ScopedBytes

namespace Alvoki.Compaction
open Alvoki.Opt Alvoki.ScopedBytes

structure Run where
  private mk ::
  bytes : ByteArray
  count : USize
  size_eq : bytes.size = 16 + 32 * count.toNat

@[inline] private def readLane (run : @& Run) (i : USize) (lane : USize)
    (within : i < run.count) (laneFits : lane.toNat ≤ 40) : UInt64 :=
  wordBounded run.bytes (lane + 32 * i) (by
    have index := USize.lt_iff_toNat_lt.mp within
    have size := run.size_eq
    have stride : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [USize.toNat_add, USize.toNat_mul, stride]
    have offset : (lane.toNat + 32 * i.toNat % USize.size) % USize.size ≤ lane.toNat + 32 * i.toNat :=
      Nat.le_trans (Nat.mod_le ..) (Nat.add_le_add_left (Nat.mod_le ..) lane.toNat)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right offset 7) (by omega))

@[inline] private def key (run : @& Run) (i : USize) (within : i < run.count) : UInt64 :=
  readLane run i 16 within (by simp)

@[inline] private def sequence (run : @& Run) (i : USize) (within : i < run.count) : UInt64 :=
  readLane run i 24 within (by simp)

@[inline] private def kind (run : @& Run) (i : USize) : UInt64 :=
  wordMachine run.bytes (32 + 32 * i)

@[inline] private def value (run : @& Run) (i : USize) : UInt64 :=
  wordMachine run.bytes (40 + 32 * i)

private def validateFrom (run : @& Run) (i : USize) (prevKey prevSeq : UInt64)
    (firstRow : Bool) : Bool :=
  if within : i < run.count then
    let k := key run i within
    let seq := sequence run i within
    let tag := readLane run i 32 within (by simp)
    if tag > 1 || (tag == 1 && readLane run i 40 within (by simp) != 0) then false
    else if !firstRow && (k < prevKey || (k == prevKey && seq >= prevSeq)) then false
    else validateFrom run (i + 1) k seq false
  else true
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

def parse (bytes : ByteArray) : Except String Run :=
  if short : bytes.size < 16 then .error "expected a versioned run"
  else if word bytes 8 != 3 then .error "expected a versioned run"
  else
    let payload := bytes.size - 16
    let count := payload / 32
    if valid : bytes.size < USize.size ∧ payload % 32 = 0 ∧ (word bytes 0).toNat = count then
      have countExact : count.toUSize.toNat = count := USize.toNat_ofNat_of_lt (by
        have fits := valid.1
        dsimp [count, payload]
        omega)
      have size : bytes.size = 16 + 32 * count := by
        have aligned := valid.2.1
        dsimp [count, payload] at *
        omega
      let run : Run := ⟨bytes, count.toUSize, by rwa [countExact]⟩
      if validateFrom run 0 0 0 true then .ok run else .error "invalid version order or row kind"
    else .error "invalid versioned run length"

/-- Entries sort by key ascending and sequence descending. Equal pairs select right. -/
@[inline] private def first (ka sa kb sb : UInt64) : Bool :=
  ka < kb || (ka == kb && sa > sb)

@[specialize] private def visitFrom (left right : @& Run) (floor : UInt64)
    (emit : α → Bool → USize → UInt64 → UInt64 → α)
    (i j : USize) (previous : UInt64) (covered : Bool) (state : α) : α :=
  if hi : i < left.count then
    let a := key left i hi
    let sa := sequence left i hi
    if hj : j < right.count then
      let b := key right j hj
      let sb := sequence right j hj
      if first a sa b sb then
        let keep := a != previous || !covered
        let next := if keep then emit state false i a sa else state
        visitFrom left right floor emit (i + 1) j a (sa ≤ floor) next
      else
        let keep := b != previous || !covered
        let next := if keep then emit state true j b sb else state
        let skip := if a == b && sa == sb then i + 1 else i
        visitFrom left right floor emit skip (j + 1) b (sb ≤ floor) next
    else
      let keep := a != previous || !covered
      let next := if keep then emit state false i a sa else state
      visitFrom left right floor emit (i + 1) j a (sa ≤ floor) next
  else if hj : j < right.count then
    let b := key right j hj
    let sb := sequence right j hj
    let keep := b != previous || !covered
    let next := if keep then emit state true j b sb else state
    visitFrom left right floor emit i (j + 1) b (sb ≤ floor) next
  else state
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    try have li := USize.lt_iff_toNat_lt.mp hi
    try have ls := addOne i left.count li
    try have rj := USize.lt_iff_toNat_lt.mp hj
    try have rs := addOne j right.count rj
    try dsimp [skip]
    first | omega | (split <;> omega)

@[inline] private def visit (left right : @& Run) (floor : UInt64) (init : α)
    (emit : α → Bool → USize → UInt64 → UInt64 → α) : α :=
  visitFrom left right floor emit 0 0 0 false init

@[inline] private def payloadOffset (i : USize) : Nat := 16 + i.toNat * 32

private def initial (a b : @& Run) : Builder :=
  Builder.ofPrefix (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity
    (16 + 32 * (a.count.toNat + b.count.toNat))) 0) 3)

private def finish (out : Builder) : ByteArray :=
  let bytes := out.finish
  let header := pushWordFast (ByteArray.emptyWithCapacity 8) ((bytes.size - 16) / 32).toUInt64
  header.copySlice 0 bytes 0 8

def compact (left right : @& Run) (floor : UInt64) : ByteArray :=
  finish (visit left right floor (initial left right) fun out fromRight i _ _ =>
    let source := if fromRight then right else left
    out.copyToTail source.bytes (payloadOffset i) 32)

private structure Pending where
  output : Builder
  right : Bool
  start : USize
  stop : USize

@[inline] private def flush (left right : @& Run) (span : Pending) : Builder :=
  if span.start == span.stop then span.output
  else
    let source := if span.right then right else left
    span.output.copyToTail source.bytes (payloadOffset span.start)
      (32 * (span.stop.toNat - span.start.toNat))

def compactSpans (left right : @& Run) (floor : UInt64) : ByteArray :=
  let span : Pending := ⟨initial left right, false, 0, 0⟩
  let tail := visit left right floor span fun prev fromRight i _ _ =>
    if fromRight == prev.right && i == prev.stop then { prev with stop := i + 1 }
    else ⟨flush left right prev, fromRight, i, i + 1⟩
  finish (flush left right tail)

/-- Fold the visible non-tombstone rows at the given snapshot. -/
def scan (left right : @& Run) (snapshot : UInt64) : UInt64 :=
  visit left right snapshot 0 fun sum fromRight i k seq =>
    let source := if fromRight then right else left
    if seq ≤ snapshot && kind source i == 0 then sum + (k ^^^ value source i) else sum

def Run.scan (run : @& Run) (snapshot : UInt64) : UInt64 :=
  let empty := pushWordFast (pushWordFast ByteArray.empty 0) 3
  Alvoki.Compaction.scan run ⟨empty, 0, by
    have zero : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [zero]
    rfl⟩ snapshot

end Alvoki.Compaction
