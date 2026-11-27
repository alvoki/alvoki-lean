import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable.Tests

private abbrev Trace := List (Nat × Nat)
private abbrev Probe := EStateM String Trace

private def source (bytes : ByteArray) (failRead : Nat → Trace → Bool := fun _ _ => false) : Source Probe where
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

-- A literal fixture independent of the encoder: two little-endian key/value pairs.
private def golden : ByteArray := ⟨#[
  65, 76, 86, 83, 83, 84, 48, 50, 2, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0,
  77, 231, 83, 176, 66, 9, 243, 79,
  2, 1, 0, 0, 0, 0, 0, 0, 255, 1, 0, 0, 0, 0, 0, 128,
  216, 122, 185, 39, 120, 236, 124, 116]⟩

def checks : IO Unit := do
  let (fixture, headerReads) ← run (openTable (source golden))
  check (fixture.rowCount == 2 && headerReads == [(0, 16)]) "header read"
  let (found, _) ← run (fixture.lookup 258)
  check (found == some 0x80000000000001ff) "wire byte order"
  let (broken, _) ← run (openTable (source golden (fun offset _ => offset == 40)))
  for action in [discard (broken.lookup 3), discard (broken.seek 3), discard (broken.next 1)] do
    match action [] with
    | .error "injected read error" _ => pure ()
    | _ => throw (IO.userError "read error lost")
  -- Looking up the first key visits row 1, row 0, then rereads row 0.
  -- Inject the same error at either of the latter reads.
  for priorReads in [1, 2] do
    let (intermittent, _) ← run (openTable (source golden (fun offset trace =>
      offset == 16 && trace.length == priorReads)))
    match intermittent.lookup 1 [] with
    | .error "injected read error" trace => check (trace.length == priorReads + 1) "unexpected read after EIO"
    | _ => throw (IO.userError "lost later lookup error")
  -- Open checks only the header. A corrupted record first fails at its own read.
  for offset in [40, 48, 56] do
    let damaged := golden.set! offset (golden[offset]! ^^^ 1)
    let (lazyTable, header) ← run (openTable (source damaged))
    let (first, _) ← run (lazyTable.next 0)
    check (header == [(0, 16)] && first == some (⟨1, 9⟩, 1)) "unrelated row failed"
    for action in [discard (lazyTable.next 1), discard (lazyTable.seek 258),
                   discard (lazyTable.lookup 258)] do
      match action [] with
      | .error _ _ => pure ()
      | _ => throw (IO.userError "corrupt row accepted")
  let rows : List Entry := (List.range 38).map (fun i => ⟨(i*3).toUInt64, (i+8).toUInt64⟩)
  let (table, _) ← run (openTable (source (encodeImage rows)))
  for query in List.range 116 do
    let key := query.toUInt64
    let expected := rows.takeWhile (fun r => r.key < key)
    let (cursor, probes) ← run (table.seek key)
    check (cursor == expected.length) "lower bound"
    check (probes.length ≤ 6 && probes.all (fun (offset, count) =>
      count == 24 && (offset - 16) % 24 == 0 && 16 ≤ offset && offset + count ≤ 16 + 24 * rows.length)) "probe bounds"
    let (value, _) ← run (table.lookup key)
    check (value == (rows.find? (fun r => r.key == key)).map Entry.value) "lookup"
  let mut cursor := 0
  for row in rows do
    let (observed, probes) ← run (table.next cursor)
    check (observed == some (row, cursor + 1) && probes == [(16 + 24 * cursor, 24)]) "iteration"
    cursor := cursor + 1
  let (endRow, reads) ← run (table.next cursor)
  check (endRow.isNone && reads.isEmpty) "end of iteration performed I/O"
  IO.println "SSTable format, oracle and positional read checks passed"

end ImmutableSSTable.Tests

def main := ImmutableSSTable.Tests.checks
