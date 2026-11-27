import Alvoki.Experiments.SSTable.FixedNative

open ImmutableSSTable

namespace ImmutableSSTable.FixedBench

private def ok (action : EIO String α) : IO α := action.adapt IO.userError

private def key (n : Nat) : ByteArray :=
  ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
    (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

private def row (index : Nat) : Entry :=
  ⟨key (2 * index), encodeOffset (index + 1)⟩

private def mix (hash value : UInt64) : UInt64 := (hash ^^^ value) * 1099511628211

private structure Query where
  bytes : ByteArray
  expected : UInt64

private def makeQueries (rows queries : Nat) : Array Query := Id.run do
  let mut result := Array.emptyWithCapacity queries
  let mut seed := 12345
  for i in [:queries] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let index := (seed >>> 8) % rows
    let miss := i % 2
    result := result.push ⟨key (2 * index + miss), if miss == 0 then (index + 1).toUInt64 else 0⟩
  return result

private def lookup (table : Table (EIO String)) (queries : Array Query) : EIO String UInt64 := do
  let mut checksum := 0
  for query in queries do
    let found ← table.lookup query.bytes
    let value := found.elim 0 (fun bytes => Alvoki.word bytes 0)
    checksum := mix checksum value
  return checksum

private def scan (table : Table (EIO String)) : EIO String UInt64 := do
  let mut checksum := 0
  for index in [:table.rowCount] do
    let some (entry, _) ← table.next index | throw "unexpected end of SSTable"
    checksum := mix checksum (Alvoki.word entry.value 0)
  return checksum

private def scanBlocks (source : Source (EIO String)) (layout : Fixed.Layout) (count : Nat) :
    EIO String UInt64 := do
  let mut checksum := 0
  for block in [:(count + layout.rowsPerBlock - 1) / layout.rowsPerBlock] do
    let payload ← Fixed.readBlock source layout count block
    let remaining := count - block * layout.rowsPerBlock
    for index in [:min layout.rowsPerBlock remaining] do
      let entry := Fixed.readRow layout payload index
      checksum := mix checksum (Alvoki.word entry.value 0)
  return checksum

private def elapsed (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let result ← action
  return (result, (← IO.monoNanosNow) - start)

private def countReads (source : Source (EIO String)) (reads : IO.Ref (Nat × Nat)) :
    Source (EIO String) where
  size := source.size
  readAt offset count := do
    reads.modify fun (calls, bytes) => (calls + 1, bytes + count)
    source.readAt offset count

private def sample (rows trial : Nat) (format operation : String) (items bytes time : Nat)
    (reads : Option (Nat × Nat)) (checksum : UInt64) : IO Unit := do
  let readColumns := reads.elim "," (fun (calls, requested) => s!"{calls},{requested}")
  IO.println s!"{rows},{trial},{format},{operation},{items},{bytes},{time},{readColumns},{checksum}"

private def measureRead (rows trial : Nat) (format operation : String) (items bytes : Nat)
    (reads : IO.Ref (Nat × Nat)) (timed measured : EIO String UInt64) (expected : UInt64) :
    IO Unit := do
  let warm ← ok timed
  unless warm == expected do throw (IO.userError s!"{format} {operation} warm-up checksum")
  let (value, uptime) ← elapsed (ok timed)
  unless value == expected do throw (IO.userError s!"{format} {operation} timed checksum")
  reads.set (0, 0)
  let counted ← ok measured
  unless counted == expected do throw (IO.userError s!"{format} {operation} counted checksum")
  sample rows trial format operation items bytes uptime (some (← reads.get)) value

private def runSample (dir : System.FilePath) (rows trial : Nat) (queries : Array Query)
    (scanSum lookupSum : UInt64) (blockRows : Option Nat) : IO Unit := do
  let format := blockRows.elim "variable" (fun count => s!"fixed-{count}")
  let path := dir / s!"{format}-{trial}"
  let nextIndex ← IO.mkRef 0
  let nextRow := do
    let index ← nextIndex.get
    if index == rows then return none
    nextIndex.set (index + 1)
    return some (row index)
  let (written, buildTime) ← elapsed <| match blockRows with
    | none => buildFile path nextRow
    | some count => Fixed.buildFile path ⟨8, 8, count, 27⟩ nextRow
  unless written == rows do throw (IO.userError "benchmark build count")
  let handle ← IO.FS.Handle.mk path .read
  let source := handleSource handle
  let bytes ← ok source.size
  sample rows trial format "build" rows bytes buildTime none 0

  let reads ← IO.mkRef (0, 0)
  let instrumented := countReads source reads
  let openFor := if blockRows.isSome then Fixed.openTable else openTable
  let table ← ok (openFor source)
  let countTable ← ok (openFor instrumented)
  unless table.rowCount == rows && countTable.rowCount == rows do
    throw (IO.userError "benchmark open count")
  measureRead rows trial format "lookup-mixed" queries.size bytes reads
    (lookup table queries) (lookup countTable queries) lookupSum
  measureRead rows trial format "scan-next" rows bytes reads
    (scan table) (scan countTable) scanSum

  if blockRows == some 128 then
    let (layout, count) ← ok (Fixed.openLayout source)
    measureRead rows trial format "scan-block" rows bytes reads
      (scanBlocks source layout count) (scanBlocks instrumented layout count) scanSum
  IO.FS.removeFile path

def run (rows queryCount trials : Nat) : IO Unit := IO.FS.withTempDir fun dir => do
  let queries := makeQueries rows queryCount
  let lookupSum := queries.foldl (fun hash query => mix hash query.expected) 0
  let mut scanSum := 0
  for index in [:rows] do
    scanSum := mix scanSum (index + 1).toUInt64
  IO.println "rows,trial,format,operation,items,file_bytes,elapsed_ns,read_calls,requested_bytes,checksum"
  let formats := #[none, some 1, some 128]
  for trial in [:trials] do
    for index in [:formats.size] do
      runSample dir rows trial queries scanSum lookupSum formats[(trial + index) % formats.size]!

end ImmutableSSTable.FixedBench

def main (args : List String) : IO Unit := do
  let [some rows, some queries, some trials] := args.map String.toNat?
    | throw (IO.userError "usage: fixed-sstable-bench ROWS QUERIES TRIALS")
  unless 0 < rows && rows < 2 ^ 32 && 0 < queries && 0 < trials do
    throw (IO.userError "require 0 < ROWS < 2^32, QUERIES and TRIALS positive")
  ImmutableSSTable.FixedBench.run rows queries trials
