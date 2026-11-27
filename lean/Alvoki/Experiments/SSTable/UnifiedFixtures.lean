import Alvoki.Experiments.SSTable.UnifiedNative

open ImmutableSSTable

namespace ImmutableSSTable.UnifiedFixtures

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def ok (action : EIO String α) : IO α := action.adapt IO.userError

private def pureOK (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def expectError (action : EIO String α) (message : String) : IO Unit := do
  check (!(← action.toBaseIO).isOk) message

private def build (path : System.FilePath) (layout : Unified.Layout) (rows : List Entry)
    (options : Unified.BuildOptions := {}) : IO Nat := do
  let remaining ← IO.mkRef rows
  Unified.buildFile path layout (do
    match ← remaining.get with
    | [] => return none
    | entry :: tail =>
      remaining.set tail
      return some entry) options

private def key (width : Option Nat) (index : Nat) : ByteArray :=
  let first := (3 * index + 1).toUInt8
  if width.isSome || index % 2 == 1 then ⟨#[first, 0]⟩ else ⟨#[first]⟩

private def row (layout : Unified.Layout) (index : Nat) : Entry :=
  let size := layout.valueWidth.getD (index % 11)
  ⟨key layout.keyWidth index, ⟨Array.replicate size (index + 99).toUInt8⟩⟩

private def seamOptions : Unified.BuildOptions := { dataTarget := 96, leafTarget := 128 }

/-- Decode the native output with the portable CRC and extract index references. -/
private def readIndexes (bytes : ByteArray) : IO (Array Unified.Ref × Array Unified.Ref) := do
  let footerStart := bytes.size - Unified.footerBodySize - Unified.checksumSize
  let footerBody ← pureOK <| Unified.decodePacket Unified.crc32c 0 4 0 (bytes.extract footerStart bytes.size)
  let footer ← pureOK <| Unified.decodeFooterBody footerBody
  let readIndex (kind : UInt64) (offset size : Nat) := do
    let block ← pureOK <| Unified.decodePacket Unified.crc32c footer.layout.tableId kind offset
      (bytes.extract offset (offset + size))
    pureOK (Unified.decodeIndex block)
  let root ← readIndex 3 footer.rootOffset footer.rootSize
  let mut data := #[]
  for leaf in root do
    data := data ++ (← readIndex 2 leaf.offset leaf.size)
  return (root, data)

private def checkWidths (dir : System.FilePath) : IO Unit := do
  let count := 63
  for keyWidth in [none, some 2] do
    for valueWidth in [none, some 9] do
      let layout : Unified.Layout := ⟨keyWidth, valueWidth, 2503⟩
      let rows := (List.range count).map (row layout)
      let path := dir / s!"layout-{keyWidth.isSome}-{valueWidth.isSome}"
      let written ← build path layout rows seamOptions
      check (written == count) "unified writer row count"
      let table ← ok (Unified.openNativeChecked path layout.tableId)
      check (table.rowCount == count) "unified footer row count"
      let (leaves, data) ← readIndexes (← IO.FS.readBinFile path)
      check (leaves.size > 1 && data.size > 2) "unified fixture did not cross packet boundaries"

      for index in List.range count do
        let entry := row layout index
        check ((← ok (table.next index)) == some (entry, index + 1)) "unified cursor row"
      check ((← ok (table.next count)).isNone && (← ok (table.next (count + 1))).isNone)
        "unified logical EOF"

      for first in List.range (3 * count + 1) do
        let byte := first.toUInt8
        for query in [ByteArray.mk #[byte], ByteArray.mk #[byte, 0], ByteArray.mk #[byte, 1]] do
          let expectedIndex := rows.takeWhile
            (fun entry => compare entry.key.data.toList query.data.toList == .lt)
          let expectedValue := (rows.find? fun entry => entry.key == query).map Entry.value
          check ((← ok (table.seek query)) == expectedIndex.length) "unified seek differs from list oracle"
          check ((← ok (table.lookup query)) == expectedValue) "unified lookup differs from list oracle"

private def checkEmpty (dir : System.FilePath) : IO Unit := do
  let path := dir / "empty"
  let layout : Unified.Layout := ⟨none, none, 4⟩
  check ((← build path layout []) == 0) "unified empty build count"
  let table ← ok (Unified.openNativeChecked path layout.tableId)
  check (table.rowCount == 0) "unified empty count"
  check ((← ok (table.seek .empty)) == 0 && (← ok (table.lookup .empty)).isNone &&
    (← ok (table.next 0)).isNone) "unified empty observations"
  let bytes ← IO.FS.readBinFile path
  check (bytes.size == Unified.footerBodySize + Unified.checksumSize) "unified empty extent"
  expectError (Unified.openNativeChecked path 5) "unified empty table ID mismatch ignored"
  let zeroPath := dir / "zero-width"
  let zeroLayout : Unified.Layout := ⟨some 0, some 0, 5⟩
  check ((← build zeroPath zeroLayout [⟨.empty, .empty⟩]) == 1) "zero-width fields"
  let zero ← ok (Unified.openNativeChecked zeroPath zeroLayout.tableId)
  check ((← ok (zero.lookup .empty)) == some .empty) "zero-width value reported as absent"

private def checkFailures (dir : System.FilePath) : IO Unit := do
  let path := dir / "builder-failure"
  let layout : Unified.Layout := ⟨some 2, some 9, 42⟩
  let first := row layout 0
  let later := row layout 1
  for rows in [[first, first], [later, first], [⟨.empty, first.value⟩], [⟨first.key, .empty⟩]] do
    check (!(← (build path layout rows).toBaseIO).isOk) "unified writer accepted invalid rows"
    check (!(← path.pathExists)) "unified invalid rows left destination"

  let oversized := ⟨first.key, ⟨Array.replicate maxRowSize 0⟩⟩
  check (!(← (build path { layout with valueWidth := none } [oversized]).toBaseIO).isOk)
    "unified writer accepted oversized row"
  check (!(← path.pathExists)) "unified oversized row left destination"
  for options in [{ seamOptions with dataTarget := 0 }, { seamOptions with leafTarget := maxRowSize + 1 }] do
    check (!(← (build path layout [first] options).toBaseIO).isOk)
      "unified writer accepted invalid packet target"
    check (!(← path.pathExists)) "unified invalid target left destination"

  let supplied ← IO.mkRef false
  let primary := IO.userError "unified input failure"
  let result ← (Unified.buildFile path layout do
    if ← supplied.get then
      IO.FS.removeFile path
      throw primary
    supplied.set true
    return some first).toBaseIO
  match result with
  | .error error => check (error.toString == primary.toString) "unified cleanup masked input error"
  | .ok _ => throw (IO.userError "unified input failure reported success")
  discard <| build path layout [first]
  let before ← IO.FS.readBinFile path
  check (!(← (build path layout [later]).toBaseIO).isOk) "unified writer overwrote an existing file"
  check ((← IO.FS.readBinFile path) == before) "unified failed build changed an existing file"

private def corrupt (bytes : ByteArray) (offset : Nat) : ByteArray :=
  bytes.set! offset (bytes[offset]! ^^^ 1)

private def checkCorruption (dir : System.FilePath) : IO Unit := do
  let path := dir / "original"
  let secondPath := dir / "second"
  let damagePath := dir / "damaged"
  let layout : Unified.Layout := ⟨some 2, some 9, 54⟩
  let rows := (List.range 63).map (row layout)
  discard <| build path layout rows seamOptions
  discard <| build secondPath { layout with tableId := 55 } rows seamOptions
  let original ← IO.FS.readBinFile path
  let second ← IO.FS.readBinFile secondPath
  let (leaves, data) ← readIndexes original
  let some firstLeaf := leaves[0]? | throw (IO.userError "missing first leaf")
  let some firstData := data[0]? | throw (IO.userError "missing first data packet")
  let some secondData := data[1]? | throw (IO.userError "missing second data packet")
  let footerStart := original.size - Unified.footerBodySize - Unified.checksumSize
  let rootBody ← pureOK <| Unified.decodePacket Unified.crc32c 0 4 0
    (original.extract footerStart original.size)
  let footer ← pureOK <| Unified.decodeFooterBody rootBody

  for bytes in [corrupt original footerStart, corrupt original footer.rootOffset,
                original.extract 0 (original.size - 1), original ++ ⟨#[0]⟩] do
    IO.FS.writeBinFile damagePath bytes
    expectError (Unified.openNativeChecked damagePath layout.tableId) "unified open accepted corrupt extent or index"

  for offset in [firstLeaf.offset, firstData.offset] do
    IO.FS.writeBinFile damagePath (corrupt original offset)
    let damaged ← ok (Unified.openNativeChecked damagePath layout.tableId)
    expectError (damaged.lookup (row layout 0).key) "unified lookup accepted a corrupt packet"
    expectError (damaged.next 0) "unified cursor accepted a corrupt packet"
    check ((← ok (damaged.lookup (row layout 62).key)) == some (row layout 62).value)
      "unified lazy validation touched an unrelated packet"

  expectError (Unified.openNativeChecked secondPath layout.tableId) "unified accepted substituted table"
  let endAt := firstData.offset + firstData.size
  let transplanted := original.extract 0 firstData.offset ++ second.extract firstData.offset endAt ++
    original.extract endAt original.size
  IO.FS.writeBinFile damagePath transplanted
  let damaged ← ok (Unified.openNativeChecked damagePath layout.tableId)
  expectError (damaged.next 0) "unified accepted data at the same position from a different table"

  check (firstData.size == secondData.size) "unified relocation fixture size mismatch"
  let secondEnd := secondData.offset + secondData.size
  let relocated := original.extract 0 secondData.offset ++ original.extract firstData.offset endAt ++
    original.extract secondEnd original.size
  IO.FS.writeBinFile damagePath relocated
  let damaged ← ok (Unified.openNativeChecked damagePath layout.tableId)
  expectError (damaged.next secondData.firstRow) "unified accepted data moved within the same table"

  let table ← ok (Unified.openNativeChecked path layout.tableId)
  IO.FS.writeBinFile path (original.extract 0 (firstData.offset + 1))
  expectError (table.next 0) "unified accepted a truncated live file"
  check ((← ok (table.next table.rowCount)).isNone) "unified logical EOF attempted file I/O"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  check (Unified.crc32c 0 "123456789".toUTF8 == 0xe3069283) "CRC32C standard vector"
  check (Unified.crc32c (Unified.crc32c 0 "1234".toUTF8) "56789".toUTF8 == 0xe3069283)
    "portable CRC32C incremental vector"
  check (Unified.nativeCRC32C (Unified.nativeCRC32C 0 "1234".toUTF8) "56789".toUTF8 == 0xe3069283)
    "native CRC32C incremental vector"
  checkWidths dir
  checkEmpty dir
  checkFailures dir
  checkCorruption dir
  IO.println "unified immutable SSTable native fixtures passed"

private def benchKey (n : Nat) : ByteArray :=
  ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
    (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

private def benchKeyFor (layout : Unified.Layout) (index : Nat) : ByteArray :=
  let bytes := benchKey index
  if layout.keyWidth.isSome then bytes
  else bytes ++ ByteArray.mk (Array.replicate ((index / 2) % 8) 0x42)

private def benchRows (layout : Unified.Layout) (rows : Nat) : IO (IO (Option Entry)) := do
  let next ← IO.mkRef 0
  return do
    let index ← next.get
    if index == rows then return none
    next.set (index + 1)
    let value := encodeOffset (index + 1)
    let value := if layout.valueWidth.isSome then value
      else value ++ ByteArray.mk (Array.replicate (index % 16) 0x56)
    return some ⟨benchKeyFor layout (2 * index), value⟩

private def mix (hash value : UInt64) : UInt64 := (hash ^^^ value) * 1099511628211

private def benchQueries (layout : Unified.Layout) (rows queries : Nat) :
    Array ByteArray × Array ByteArray × Array ByteArray × UInt64 × UInt64 := Id.run do
  let mut mixed := #[]
  let mut hits := #[]
  let mut misses := #[]
  let mut mixedSum : UInt64 := 0
  let mut hitSum : UInt64 := 0
  let mut seed := 12345
  for i in [:queries] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let index := (seed >>> 8) % rows
    let miss := i % 2
    let key := benchKeyFor layout (2 * index + miss)
    let value := if miss == 0 then (index + 1).toUInt64 else 0
    mixed := mixed.push key
    mixedSum := mix mixedSum value
    if miss == 0 then
      hits := hits.push key
      hitSum := mix hitSum value
    else
      misses := misses.push key
  return (mixed, hits, misses, mixedSum, hitSum)

private def lookups (lookup : ByteArray → EIO String (Option ByteArray))
    (queries : Array ByteArray) : EIO String UInt64 := do
  let mut checksum := 0
  for key in queries do
    let value ← lookup key
    checksum := mix checksum (value.elim 0 (Alvoki.word · 0))
  return checksum

private def scan (next : Nat → EIO String (Option (Entry × Nat))) (rows : Nat) :
    EIO String UInt64 := do
  let mut checksum := 0
  for index in [:rows] do
    let some (entry, following) ← next index | throw "benchmark scan ended early"
    unless following == index + 1 do throw "benchmark scan cursor"
    checksum := mix checksum (Alvoki.word entry.value 0)
  return checksum

private structure BenchmarkCase where
  label : String
  layoutName : String
  dataTarget : Nat := 0
  leafTarget : Nat := 0
  leaves : Nat := 0
  blocks : Nat := 0
  fileBytes : Nat := 0

private structure ReadStats where
  indexCalls : Nat := 0
  indexBytes : Nat := 0
  dataCalls : Nat := 0
  dataBytes : Nat := 0

private def report (configuration : BenchmarkCase) (operation : String)
    (items trial elapsed : Nat) (sample : ReadStats := {}) : IO Unit :=
  IO.println s!"{configuration.label},{configuration.layoutName},{configuration.dataTarget},{configuration.leafTarget},{configuration.leaves},{configuration.blocks},{configuration.fileBytes},{operation},{items},{trial},{elapsed},{sample.indexCalls},{sample.indexBytes},{sample.dataCalls},{sample.dataBytes}"

private def measure (configuration : BenchmarkCase) (operation : String) (items : Nat)
    (action traced : EIO String UInt64) (expected : UInt64) (stats : IO.Ref ReadStats) : IO Unit := do
  check ((← ok action) == expected) "benchmark warm-up checksum"
  stats.set {}
  check ((← ok traced) == expected) "benchmark traced checksum"
  let sample ← stats.get
  for trial in [:3] do
    let started ← IO.monoNanosNow
    let checksum ← ok action
    let elapsed := (← IO.monoNanosNow) - started
    check (checksum == expected) "benchmark timed checksum"
    report configuration operation items trial elapsed sample

private def benchmarkCase (path : System.FilePath) (configuration : BenchmarkCase)
    (layout : Unified.Layout) (rows : Nat) (isIndex : Nat → Bool) (scanSum : UInt64) :
    IO Unit := do
  let file ← IO.FS.Handle.mk path .read
  let source := handleSource file
  let stats ← IO.mkRef ({} : ReadStats)
  let traced : Source (EIO String) := {
    size := source.size
    readAt := fun offset count => do
      stats.modify fun sample =>
        if isIndex offset then
          { sample with indexCalls := sample.indexCalls + 1, indexBytes := sample.indexBytes + count }
        else
          { sample with dataCalls := sample.dataCalls + 1, dataBytes := sample.dataBytes + count }
      source.readAt offset count
  }
  let openFor := fun input => do
    let table ← Unified.openTableChecked input Unified.nativeCRC32C layout.tableId
    return (table.lookup, table.next)
  for trial in [:3] do
    let start ← IO.monoNanosNow
    discard <| ok (openFor source)
    report configuration "open" 1 trial ((← IO.monoNanosNow) - start)
  let (lookup, next) ← ok (openFor source)
  let (traceLookup, traceNext) ← ok (openFor traced)
  let (mixed, hits, misses, mixedSum, hitSum) := benchQueries layout rows 4096
  for (label, queries, expected) in [("mixed", mixed, mixedSum), ("hit", hits, hitSum), ("miss", misses, 0)] do
    measure configuration label queries.size (lookups lookup queries) (lookups traceLookup queries) expected stats
  measure configuration "scan-next" rows (scan next rows) (scan traceNext rows) scanSum stats

def benchmark : IO Unit := IO.FS.withTempDir fun dir => do
  let rows := 65537
  let scanSum := (List.range rows).foldl (fun hash index => mix hash (index + 1).toUInt64) 0
  IO.println "format,layout,data_target,leaf_target,leaf_blocks,data_blocks,file_bytes,operation,items,trial,elapsed_ns,index_reads,index_bytes,data_reads,data_bytes"
  for (name, keyWidth, valueWidth) in [
      ("fixed-fixed", some 8, some 8), ("fixed-variable", some 8, none),
      ("variable-fixed", none, some 8), ("variable-variable", none, none)] do
    let layout : Unified.Layout := ⟨keyWidth, valueWidth, 84⟩
    for (dataTarget, leafTarget) in [(1024, 1024), (4096, 1024), (16384, 1024), (4096, 4096)] do
      let path := dir / s!"{name}-{dataTarget}-{leafTarget}"
      let provider ← benchRows layout rows
      let start ← IO.monoNanosNow
      let count ← Unified.buildFile path layout provider { dataTarget, leafTarget }
      let buildTime := (← IO.monoNanosNow) - start
      check (count == rows) "benchmark build count"
      let image ← IO.FS.readBinFile path
      let (leaves, blocks) ← readIndexes image
      let configuration : BenchmarkCase :=
        ⟨"ALVSST05", name, dataTarget, leafTarget,
          leaves.size, blocks.size, image.size⟩
      report configuration "build" rows 0 buildTime
      let isIndex : Nat → Bool := fun offset => leaves.any (·.offset == offset)
      benchmarkCase path configuration layout rows isIndex scanSum
      IO.FS.removeFile path

end ImmutableSSTable.UnifiedFixtures

def main (args : List String) : IO Unit :=
  match args with
  | [] => ImmutableSSTable.UnifiedFixtures.run
  | ["--bench"] => ImmutableSSTable.UnifiedFixtures.benchmark
  | _ => throw (IO.userError "usage: test-unified-sstable [--bench]")
