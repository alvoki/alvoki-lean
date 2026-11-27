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

private def benchRows (rows : Nat) : IO (IO (Option Entry)) := do
  let next ← IO.mkRef 0
  return do
    let index ← next.get
    if index == rows then return none
    next.set (index + 1)
    return some ⟨benchKey (2 * index), encodeOffset (index + 1)⟩

private def mix (hash value : UInt64) : UInt64 := (hash ^^^ value) * 1099511628211

private def benchQueries (rows queries : Nat) : Array ByteArray × UInt64 := Id.run do
  let mut keys := Array.emptyWithCapacity queries
  let mut expected : UInt64 := 0
  let mut seed := 12345
  for i in [:queries] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let index := (seed >>> 8) % rows
    let miss := i % 2
    keys := keys.push (benchKey (2 * index + miss))
    expected := mix expected (if miss == 0 then (index + 1).toUInt64 else 0)
  return (keys, expected)

private abbrev Lookup := ByteArray → EIO String (Option ByteArray)

private abbrev OpenLookup := Source (EIO String) → EIO String Lookup

private def lookups (lookup : Lookup) (queries : Array ByteArray) : EIO String UInt64 := do
  let mut checksum := 0
  for key in queries do
    let value ← lookup key
    checksum := mix checksum (value.elim 0 (Alvoki.word · 0))
  return checksum

private structure ReadStats where
  indexCalls : Nat := 0
  indexBytes : Nat := 0
  dataCalls : Nat := 0
  dataBytes : Nat := 0

private def benchmarkLookups (path : System.FilePath) (label : String) (rows : Nat)
    (queries : Array ByteArray) (expected : UInt64) (openLookup : OpenLookup)
    (isIndex : Nat → Bool) : IO Unit := do
  let file ← IO.FS.Handle.mk path .read
  let source := handleSource file
  let bytes ← ok source.size
  let lookup ← ok (openLookup source)
  check ((← ok (lookups lookup queries)) == expected) "unified benchmark warm-up checksum"

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
  let traceLookup ← ok (openLookup traced)
  stats.set {}
  check ((← ok (lookups traceLookup queries)) == expected) "unified benchmark traced checksum"
  let sample ← stats.get
  for trial in [:3] do
    let started ← IO.monoNanosNow
    let checksum ← ok (lookups lookup queries)
    let elapsed := (← IO.monoNanosNow) - started
    check (checksum == expected) "unified benchmark timed checksum"
    IO.println s!"{label},{rows},{queries.size},{trial},{bytes},{elapsed},{sample.indexCalls},{sample.indexBytes},{sample.dataCalls},{sample.dataBytes},{checksum}"

def benchmark : IO Unit := IO.FS.withTempDir fun dir => do
  let rows := 65537
  let (queries, expected) := benchQueries rows 4096
  let layout : Unified.Layout := ⟨some 8, some 8, 84⟩
  let variablePath := dir / "variable"
  let unified := dir / "unified"
  check ((← buildFile variablePath (← benchRows rows)) == rows) "variable benchmark build count"
  check ((← Unified.buildFile unified layout (← benchRows rows) { leafTarget := 1024 }) == rows) "unified benchmark build count"

  IO.println "format,rows,lookups,trial,file_bytes,elapsed_ns,index_reads,index_bytes,data_reads,data_bytes,checksum"
  let variableSize := (← IO.FS.readBinFile variablePath).size
  let indexStart := variableSize - footerSize - 8 * (rows + 1)
  benchmarkLookups variablePath "variable" rows queries expected
    (fun source => return (← openTable source).lookup) (· ≥ indexStart)

  let (leaves, _) ← readIndexes (← IO.FS.readBinFile unified)
  let isIndex := fun offset => leaves.any (·.offset == offset)
  let runWith crc label := benchmarkLookups unified label rows queries expected
    (fun source => return (← Unified.openChecked source crc layout.tableId).lookup) isIndex
  runWith Unified.nativeCRC32C "unified-native-crc32c"
  runWith Unified.crc32c "unified-portable-crc32c"

end ImmutableSSTable.UnifiedFixtures

def main (args : List String) : IO Unit :=
  match args with
  | [] => ImmutableSSTable.UnifiedFixtures.run
  | ["--bench"] => ImmutableSSTable.UnifiedFixtures.benchmark
  | _ => throw (IO.userError "usage: test-unified-sstable [--bench]")
