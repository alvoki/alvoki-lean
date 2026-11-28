import Alvoki.Experiments.SSTable.Recursive.FilteredReader

open ImmutableSSTable

namespace ImmutableSSTable.Recursive.Fixtures

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def ok (action : EIO String α) : IO α :=
  action.adapt IO.userError

private def save (path : System.FilePath) (layout : Unified.Layout) (rows : List Entry)
    (options : BuildOptions := {}) : IO Unit := do
  let pending ← IO.mkRef rows
  let count ← buildFileSynced path layout
    (pending.modifyGet fun rest => (rest.head?, rest.tail)) options
  require (count == rows.length) "recursive build count"

private def exerciseLayout (path : System.FilePath) (layout : Unified.Layout) : IO Unit := do
  let rows := (List.range 33).map fun i =>
    let key : ByteArray := ⟨if layout.keyWidth.isSome then #[i.toUInt8 * 2, 0] else
      if i % 2 == 0 then #[i.toUInt8 * 2] else #[i.toUInt8 * 2, 0]⟩
    let value : ByteArray := ⟨Array.replicate (layout.valueWidth.getD (i % 5)) i.toUInt8⟩
    ⟨key, value⟩
  save path layout rows { dataTarget := 1, indexTarget := 1 }
  let handle ← ok (openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path layout.tableId)
  require (handle.height ≥ 5) "tiny index target did not exercise recursive traversal"
  let table := handle.table
  require (table.rowCount == rows.length) "recursive footer count"
  for i in [:rows.length + 2] do
    require ((← ok (table.next i)) == Contents.next rows i) "recursive arbitrary cursor"
  for b in [:67] do
    for key in [ByteArray.mk #[b.toUInt8], ByteArray.mk #[b.toUInt8, 0]] do
      let expected := (rows.takeWhile (fun row => row.key < key)).length
      require ((← ok (table.seek key)) == expected) "recursive seek"
      require ((← ok (table.lookup key)) == Contents.lookup rows key) "recursive lookup"

private def exerciseMalformed (path : System.FilePath) : IO Unit := do
  let layout : Unified.Layout := ⟨some 1, some 0, 901⟩
  let rows : List Entry := (List.range 9).map fun i => ⟨⟨#[i.toUInt8 * 2]⟩, .empty⟩
  save path layout rows { dataTarget := 1, indexTarget := 1 }
  let crc := Alvoki.CRC32C.extend
  let bytes ← IO.FS.readBinFile path
  let endAt := bytes.size - footerPacketSize
  let exact (image : ByteArray) : Source (EIO String) :=
    ⟨pure image.size, fun offset size => pure (image.extract offset (offset + size))⟩
  let (footer, _) ← ok (readFooter (exact bytes) crc)
  let withFooter (changed : Footer) : ByteArray :=
    bytes.extract 0 endAt ++ Unified.encodePacket crc 0 footerKind 0 (encodeFooter changed)
  for height in [0, 64, 2^64 - 1] do
    let failed ← (openChecked (exact (withFooter { footer with height })) crc layout.tableId).toBaseIO
    require (!failed.isOk) "invalid index height accepted"
  let wrongId ← (openNativeChecked path (layout.tableId + 1)).toBaseIO
  require (!wrongId.isOk) "independent expected ID ignored"

  let handle ← ok (openChecked (exact bytes) crc layout.tableId)
  let some child := handle.root[0]? | throw (IO.userError "missing recursive root child")
  let moved := { child with offset := handle.rootOffset }
  let rootBody := Unified.encodeIndex #[moved]
  let badRoot := Unified.encodePacket crc layout.tableId (indexKind handle.height)
    handle.rootOffset rootBody
  let childCount := child.count
  let badFooter : Footer :=
    { footer with base := { footer.base with count := childCount, rootSize := badRoot.size } }
  let selfEdge := bytes.extract 0 handle.rootOffset ++ badRoot ++
    Unified.encodePacket crc 0 footerKind 0 (encodeFooter badFooter)
  let cycle ← (openChecked (exact selfEdge) crc layout.tableId).toBaseIO
  require (!cycle.isOk) "self edge accepted with recomputed CRC"

  let sourceWithFault : Source (EIO String) :=
    { size := pure bytes.size
      readAt := fun offset size =>
        if offset = child.offset then throw "injected interior read failure"
        else pure (bytes.extract offset (offset + size)) }
  let withFault ← ok (openChecked sourceWithFault crc layout.tableId)
  match ← (withFault.lookup ⟨#[0]⟩).toBaseIO with
  | .ok _ => throw (IO.userError "failed index read became a successful lookup")
  | .error error => require (error == "injected interior read failure") "interior error was masked"
  require ((← ok (withFault.lookup ⟨#[255]⟩)).isNone) "lookup after a reported read error"

private def exerciseLargeFences (path : System.FilePath) : IO Unit := do
  let width := maxRowSize - Unified.refPrefixSize - Unified.checksumSize
  let layout : Unified.Layout := ⟨some width, some 0, 902⟩
  let rows : List Entry := (List.range 3).map fun i =>
    ⟨⟨(Array.replicate width 0).set! (width - 1) i.toUInt8⟩, .empty⟩
  save path layout rows { dataTarget := 1, indexTarget := 1 }
  let handle ← ok (openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path layout.tableId)
  require (handle.height == 2) "maximal fence keys did not reduce the level"
  for expected in rows do
    require ((← ok (handle.lookup expected.key)) == some .empty) "split index packet lookup"

private def exerciseFilter (dir : System.FilePath) : IO Unit := do
  let path := dir / "filtered"
  let layout : Unified.Layout := ⟨some 1, some 1, 904⟩
  let byte (n : Nat) : ByteArray := ⟨#[n.toUInt8]⟩
  let rows : List Entry := (List.range 121).map fun i =>
    ⟨byte (2 * i), byte (if i == 5 then 0 else 1)⟩
  save path layout rows { dataTarget := 28, indexTarget := 1, membershipFilter := true }
  let filtered ← ok (openNativeFiltered path layout.tableId)
  for query in [:243] do
    let key := byte query
    require ((← ok (filtered.lookup key)) == Contents.lookup rows key) "filtered lookup oracle"
  require ((← ok (filtered.lookup (byte 10))) == some (byte 0)) "filter lost tombstone"

  let bytes ← IO.FS.readBinFile path
  let crc := Alvoki.CRC32C.extend
  let extract := fun offset count => bytes.extract offset (offset + count)
  let source : Source (EIO String) := ⟨pure bytes.size, fun offset count => pure (extract offset count)⟩
  let reader ← ok (openChecked source crc layout.tableId)
  require (reader.filtered && reader.height ≥ 3) "filtered tree fixture layout"
  let query := byte 10
  let before := fun (ref : Unified.Ref) => decide (ref.lastKey < query)
  let some child := Unified.findRef reader.root before
    | throw (IO.userError "filtered fixture root")
  let (data, _) ← ok (descend source crc layout.tableId before child reader.rootOffset (reader.height - 1))
  require (useFilter data.count) "filtered fixture region unexpectedly unfiltered"
  let filterStart := data.offset - filterPacketSize data.count
  let damaged := bytes.set! filterStart (bytes[filterStart]! ^^^ 1)
  let damagedPath := dir / "filter-crc-mismatch"
  IO.FS.writeBinFile damagedPath damaged
  let damagedTable ← ok (openNativeFiltered damagedPath layout.tableId)
  match ← (damagedTable.lookup query).toBaseIO with
  | .error error => require (error == "SSTable CRC32C mismatch") "filter corruption masked"
  | .ok _ => throw (IO.userError "corrupt filter produced a successful result")
  require ((← ok (damagedTable.seek query)) == 5) "seek touched a corrupt filter"
  require ((← ok (damagedTable.next 5)) == Contents.next rows 5) "next touched a corrupt filter"

  for (label, failAt) in [
    ("short SSTable packet read", fun _ : Nat => (pure .empty : EIO String ByteArray)),
    ("injected filter read failure", fun _ : Nat => throw "injected filter read failure")] do
    let withFault : Source (EIO String) := { source with
      readAt := fun offset count =>
        if offset == filterStart then failAt count else pure (extract offset count) }
    let handle ← ok (openChecked withFault crc layout.tableId)
    match ← (handle.filteredTable.lookup query).toBaseIO with
    | .error error => require (error == label) "unavailable filter changed the reported error"
    | .ok _ => throw (IO.userError "unavailable filter produced a successful result")
    require ((← ok (handle.filteredTable.lookup (byte 240))) == some (byte 1))
      "unfiltered fringe did not use its data packet"

  let legacy ← ok (openNativeFiltered (dir / "empty") 903)
  require ((← ok (legacy.lookup .empty)).isNone) "unfiltered file fallback"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  for keyWidth in [none, some 2] do
    for valueWidth in [none, some 2] do
      let layout : Unified.Layout := ⟨keyWidth, valueWidth, 900⟩
      exerciseLayout (dir / s!"recursive-{keyWidth.isSome}-{valueWidth.isSome}") layout
  exerciseMalformed (dir / "malformed")
  exerciseLargeFences (dir / "large-fences")
  let path := dir / "empty"
  let layout : Unified.Layout := ⟨some 0, some 0, 903⟩
  save path layout []
  let empty ← ok (openNativeChecked path layout.tableId)
  require (empty.rowCount == 0 && (← ok (empty.lookup .empty)).isNone) "empty recursive table"
  exerciseFilter dir
  IO.println "ALVSST06 recursive SSTable native fixtures passed"

end ImmutableSSTable.Recursive.Fixtures

def main : IO Unit :=
  ImmutableSSTable.Recursive.Fixtures.run
