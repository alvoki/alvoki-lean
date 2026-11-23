import Alvoki.Storage.Table.PackedTable

open Alvoki.Storage Alvoki.Sequential

private def expect (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private inductive Operation where
  | write (key : UInt64) (value : Option UInt64)
  | pin (snapshot : Option UInt64 := none)
  | release (slot : Nat)
  | flush
  | compact (index : Nat)
  | advance (floor : UInt64)
  deriving Repr

private structure Trace where
  packed : PackedTable := .empty
  model : SnapshotTable UInt64 := .empty
  handles : Array (SnapshotHandle × SnapshotHandle) := #[]

private def compareOptions (trace : Trace) (p : Option PackedTable)
    (m : Option (SnapshotTable UInt64)) : IO Trace :=
  match p, m with
  | some packed, some model => pure { trace with packed, model }
  | none, none => pure trace
  | _, _ => throw (IO.userError "packed and logical operation acceptance differed")

private def Trace.step (t : Trace) : Operation → IO Trace
  | .write key value => compareOptions t (t.packed.write key value) (t.model.write key value)
  | .pin snapshot => do
    let p := t.packed.acquireAt (snapshot.getD t.packed.committed)
    let m := t.model.acquireAt (snapshot.getD t.model.committed)
    match p, m with
    | some (actual, packed), some (expected, model) =>
      expect (decide (actual = expected)) "the acquired handles or sequences differed"
      return { packed, model, handles := t.handles.push (actual.handle, expected.handle) }
    | none, none => return t
    | _, _ => throw (IO.userError "packed and logical acquisition acceptance differed")
  | .release slot => do
    let some (p, m) := t.handles[slot]? | return t
    return { t with packed := t.packed.release p, model := t.model.release m }
  | .flush =>
    match t.packed.flush with
    | .ok packed => pure { t with packed, model := t.model.flush }
    | .error message => throw (IO.userError s!"flush failed: {message}")
  | .compact index => compareOptions t (t.packed.compact index) (t.model.compact index)
  | .advance floor => compareOptions t (t.packed.advanceFloor floor) (t.model.advanceFloor floor)

private def maxKey : UInt64 := UInt64.ofNat (UInt64.size - 1)

private def Trace.check (t : Trace) : IO Unit := do
  expect (decide (t.packed.committed = t.model.committed &&
    t.packed.pins.floor = t.model.pins.floor &&
    t.packed.pins.active = t.model.pins.active)) "the write clock, floor, or active pins differed"
  let p := t.packed.describe
  let m := t.model.table
  expect (decide (p.memory.rows = m.memory.rows ∧ p.runs.map History.rows = m.runs.map History.rows))
    "the packed run histories or memtable differed"
  let keys : List UInt64 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, maxKey]
  let ranges : List (UInt64 × UInt64) := [(0, maxKey), (2, 7), (7, 7), (12, 4), (maxKey - 1, maxKey)]
  for key in keys do
    expect (decide (t.packed.lookupAt key t.packed.committed = m.lookup key t.model.committed))
      s!"latest point read disagreed for {key}"
  for (start, stop) in ranges do
    expect (decide (t.packed.rangeAt start stop t.packed.committed = m.range start stop t.model.committed))
      s!"latest range disagreed for [{start}, {stop})"
  for (p, m) in t.handles do
    for key in keys do
      expect (decide (t.packed.lookup p key = t.model.lookup m key))
        s!"point read disagreed for handle {p.id}, key {key}"
    for (start, stop) in ranges do
      expect (decide (t.packed.range p start stop = t.model.range m start stop))
        s!"range disagreed for handle {p.id}, [{start}, {stop})"

private def run (ops : List Operation) : IO Trace := do
  let mut state : Trace := {}
  for (op, index) in ops.zipIdx do
    try
      state ← state.step op
      state.check
    catch error =>
      throw (IO.userError s!"operation {index}: {repr op}: {error}")
  return state

private def fixture : List Operation :=
  [.write 4 (some 40), .write 7 (some 70), .write maxKey (some 99), .pin,
    .flush, .write 4 (some 41), .write 7 none, .flush, .pin, .compact 0,
    .compact 0, .advance 5, .pin (some 999)]

private def mixed (seed : UInt64) : List Operation := Id.run do
  let mut rng := seed
  let mut out := []
  for _ in [:128] do
    rng := rng * 6364136223846793005 + 1442695040888963407
    let n := (rng >>> 32).toNat
    let key := (n / 11 % 16).toUInt64
    let op := match n % 11 with
      | 0 => Operation.flush
      | 1 => .compact (n / 11 % 4)
      | 2 => .pin
      | 3 => .release (n / 11 % 16)
      | 4 => .advance (n / 11 % 40).toUInt64
      | 5 => .write key none
      | _ => .write key (some rng)
    out := op :: out
  return out.reverse

def main : IO Unit := do
  let t ← run fixture
  let some (old, _) := t.handles[0]? | throw (IO.userError "missing original handle")
  let some (current, _) := t.handles[1]? | throw (IO.userError "missing current handle")
  expect (decide (t.packed.lookup old 4 = some (some 40) ∧ t.packed.lookup old 7 = some (some 70)))
    "the older snapshot lost a value after compaction"
  expect (decide (t.packed.lookup current 4 = some (some 41) ∧ t.packed.lookup current 7 = some none))
    "the latest snapshot missed an overwrite or tombstone"
  expect (decide (t.packed.lookup current maxKey = some (some 99)))
    "the maximum key was lost during a packed read"
  for seed in [7, 23, 271, 20261123] do
    let _ ← run (mixed seed)
  IO.println "Packed v3 table agrees with SnapshotTable on the fixed trace and 512 generated operations."
