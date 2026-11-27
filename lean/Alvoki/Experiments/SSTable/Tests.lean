import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable.Tests

private abbrev Trace := List (Nat × Nat)
private abbrev Probe := EStateM String Trace

private def source (bytes : ByteArray) (failRead : Nat → Trace → Bool := fun _ _ => false) :
    Source Probe where
  size := pure bytes.size
  readAt offset count := do
    let previous ← get
    set ((offset, count) :: previous)
    if failRead offset previous then throw "injected read error"
    pure (bytes.extract offset (offset + count))

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def run {α : Type} (action : Probe α) : IO (α × Trace) := do
  match action [] with
  | .ok value trace => return (value, trace.reverse)
  | .error e _ => throw (IO.userError e)

private def expectError {α : Type} (action : Probe α) (label : String) : IO Unit :=
  match action [] with
  | .error _ _ => pure ()
  | .ok _ _ => throw (IO.userError label)

-- Literal bytes computed independently of the SSTable encoder.
-- The second key extends the first and has an empty value.
private def golden : ByteArray := ⟨#[
  1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 204, 253, 80, 231, 227, 22, 111, 160,
  2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 246, 80, 148, 39, 211, 227, 25, 155,
  0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0,
  65, 76, 86, 83, 83, 84, 48, 51, 2, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0]⟩

private def first : Entry := ⟨⟨#[1]⟩, ⟨#[2, 3]⟩⟩
private def second : Entry := ⟨⟨#[1, 0]⟩, .empty⟩

private def checkGolden : IO Unit := do
  let (fixture, footerReads) ← run (openTable (source golden))
  check (encodeImage [first, second] == golden) "encoder disagrees with independent fixture"
  check (fixture.rowCount == 2 && footerReads == [(61, 24)]) "footer read"
  let (found, _) ← run (fixture.lookup first.key)
  check (found == some first.value) "lookup lost value bytes"
  let (found, _) ← run (fixture.lookup second.key)
  check (found == some .empty) "empty value reported as missing"
  let (located, _) ← run (fixture.seek ⟨#[0, 255]⟩)
  check (located == 0) "lexicographic seek"
  let (located, _) ← run (fixture.seek ⟨#[1, 0, 0]⟩)
  check (located == 2) "prefix seek"

  -- Binary search first probes row 1. Fail the index read and the payload read separately.
  for failingOffset in [45, 19] do
    let (broken, _) ← run (openTable (source golden (fun offset _ => offset == failingOffset)))
    for action in [discard (broken.lookup first.key), discard (broken.seek first.key),
                   discard (broken.next 1)] do
      match action [] with
      | .error "injected read error" _ => pure ()
      | _ => throw (IO.userError "required read error lost")
  -- A hit for the first key revisits row 0 after seek completes.
  let (intermittent, _) ← run (openTable (source golden (fun offset trace =>
    offset == 0 && trace.length == 5)))
  match intermittent.lookup first.key [] with
  | .error "injected read error" trace =>
    check (trace.length == 6) "unexpected read after final lookup error"
  | _ => throw (IO.userError "lost final lookup error")

  -- Change the key length, key, value and checksum of row 0. Row 1 still decodes.
  for offset in [0, 8, 9, 11] do
    let damaged := golden.set! offset (golden[offset]! ^^^ 1)
    let (lazyTable, _) ← run (openTable (source damaged))
    let (unaffected, _) ← run (lazyTable.next 1)
    check (unaffected == some (second, 2)) "unrelated row failed"
    expectError (lazyTable.next 0) "corrupt row accepted"
    expectError (lazyTable.seek first.key) "seek compared a corrupt row"
    expectError (lazyTable.lookup first.key) "lookup accepted a corrupt row"

  -- Move the start of row 1 to its end or move its end into the index.
  for damaged in [golden.set! 45 37, golden.set! 53 38] do
    let (lazyTable, _) ← run (openTable (source damaged))
    match lazyTable.next 1 [] with
    | .error _ reads => check (reads == [(45, 16)]) "read payload for invalid offsets"
    | _ => throw (IO.userError "invalid offsets accepted")
  let original := source golden
  let shortPayload := { original with
    readAt := fun offset count =>
      original.readAt offset (if offset == 0 then count - 1 else count) }
  let (shortTable, _) ← run (openTable shortPayload)
  expectError (shortTable.next 0) "short payload accepted"

  let oversized := maxRowSize + 1
  let oversizedSource : Source Probe := {
    size := pure (oversized + 16 + footerSize)
    readAt := fun offset count => do
      modify ((offset, count) :: ·)
      if offset == oversized + 16 then return encodeFooter 1 oversized
      if offset == oversized then return encodeOffset 0 ++ encodeOffset oversized
      throw "unexpected payload read"
  }
  let (oversizedTable, _) ← run (openTable oversizedSource)
  match oversizedTable.next 0 [] with
  | .error _ reads => check (reads == [(oversized, 16)]) "read payload for oversized row"
  | _ => throw (IO.userError "oversized row span accepted")

  for damaged in [golden.set! 61 0, golden.set! 69 3, golden.set! 77 38,
                  golden ++ ⟨#[0]⟩, golden.extract 0 84] do
    expectError (openTable (source damaged)) "invalid footer accepted"

private def checkOracle : IO Unit := do
  let rows : List Entry := (List.range 38).map fun i =>
    let first := (i * 3).toUInt8
    let key := if i % 2 == 0 then #[first] else #[first, 0]
    ⟨⟨key⟩, ⟨Array.replicate (i % 7) (i + 8).toUInt8⟩⟩
  let image := encodeImage rows
  let indexStart := image.size - footerSize - 8 * (rows.length + 1)
  let (table, _) ← run (openTable (source image))
  for query in List.range 116 do
    for key in [ByteArray.mk #[query.toUInt8], ByteArray.mk #[query.toUInt8, 0]] do
      let expected := rows.takeWhile (fun r => compare r.key.data.toList key.data.toList == .lt)
      let (cursor, probes) ← run (table.seek key)
      check (cursor == expected.length) "lower bound disagrees with list oracle"
      check (probes.length ≤ 12 && probes.length % 2 == 0 &&
        probes.all (fun (offset, count) =>
          if offset ≥ indexStart then count == 16 && (offset - indexStart) % 8 == 0 &&
            offset + count ≤ image.size - footerSize
          else offset + count ≤ indexStart && count ≤ maxRowSize)) "probe bounds"
      let (value, _) ← run (table.lookup key)
      check (value == (rows.find? (fun r => r.key == key)).map Entry.value)
        "lookup disagrees with list oracle"
  let mut cursor := 0
  let mut offset := 0
  for row in rows do
    let (observed, probes) ← run (table.next cursor)
    let size := 16 + row.key.size + row.value.size
    check (observed == some (row, cursor + 1) &&
      probes == [(indexStart + 8 * cursor, 16), (offset, size)]) "iteration"
    cursor := cursor + 1
    offset := offset + size
  let (endRow, reads) ← run (table.next cursor)
  check (endRow.isNone && reads.isEmpty) "end of iteration performed I/O"
  let (pastEnd, reads) ← run (table.next (cursor + 10))
  check (pastEnd.isNone && reads.isEmpty) "out-of-range iteration performed I/O"

def checks : IO Unit := do
  checkGolden
  checkOracle
  IO.println "SSTable format, oracle and positional read checks passed"

end ImmutableSSTable.Tests

def main := ImmutableSSTable.Tests.checks
