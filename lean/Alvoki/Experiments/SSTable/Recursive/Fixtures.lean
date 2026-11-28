import Alvoki.Experiments.SSTable.Recursive.Native
import Alvoki.Experiments.SSTable.Recursive.BlockIterator

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
  save path layout rows ⟨1, 1⟩
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

private def exerciseIterator (path : System.FilePath) (layout : Unified.Layout) : IO Unit := do
  let rows := (List.range 51).map fun i =>
    let key : ByteArray := ⟨if layout.keyWidth.isSome then #[i.toUInt8 * 2, 0] else
      if i % 2 == 0 then #[i.toUInt8 * 2] else #[i.toUInt8 * 2, 0]⟩
    ⟨key, ⟨Array.replicate (layout.valueWidth.getD (i % 5)) i.toUInt8⟩⟩
  save path layout rows ⟨80, 90⟩
  let crc := Alvoki.CRC32C.extend
  let bytes ← IO.FS.readBinFile path
  let reads ← IO.mkRef 0
  let fault ← IO.mkRef (none : Option Nat)
  let corrupt ← IO.mkRef (none : Option Nat)
  let source : Source (EIO String) := ⟨pure bytes.size, fun offset size => do
    reads.modify (· + 1)
    if (← fault.get) == some offset then throw "injected block transition failure"
    let packet := bytes.extract offset (offset + size)
    if (← corrupt.get) == some offset then return packet.set! 0 (packet[0]! ^^^ 1)
    return packet⟩
  let handle ← ok (openChecked source crc layout.tableId)
  require (2 ≤ handle.height) "iterator did not exercise interior index frames"
  reads.set 0
  let mut cursor := handle.cursorAt 0
  let mut cachedRows := 0
  let mut transitions := 0
  let mut boundary : Option (BlockCursor (EIO String) × Nat) := none
  for expected in rows do
    let previous := cursor
    let priorReads ← reads.get
    let some (row, next) ← ok cursor.pull | throw (IO.userError "iterator ended early")
    let now ← reads.get
    require (row == expected && next.index == cursor.index + 1) "iterator row or progress"
    if let some position := cursor.position then
      if BlockIterator.contains position.block.ref cursor.index then
        require (now == priorReads) "iterator reread inside a block"
        cachedRows := cachedRows + 1
      else
        require (now > priorReads) "iterator boundary did not read a packet"
        transitions := transitions + 1
        if let some crossed := next.position then
          boundary := some (previous, crossed.block.ref.offset)
    cursor := next
  require (cachedRows > 0 && transitions > 0) "iterator did not exercise both kinds of step"
  let scanReads ← reads.get
  require ((← ok cursor.pull).isNone && (← reads.get) == scanReads) "iterator EOF read"
  reads.set 0
  for i in [:rows.length] do
    require ((← ok (handle.next i)) == Contents.next rows i) "arbitrary cursor changed"
  require ((← reads.get) > scanReads) "iterator did not reduce positional reads"

  for b in [0, 1, 17, 49, 99, 100, 255] do
    let key : ByteArray := ⟨#[b.toUInt8]⟩
    let expectedIndex := (rows.takeWhile (fun row => row.key < key)).length
    let sought ← ok (handle.seekCursor key)
    require (sought.index == expectedIndex) "iterator lower bound"
    let before ← reads.get
    let step ← ok sought.pull
    require (step.map Prod.fst == rows[expectedIndex]? && (← reads.get) == before)
      "iterator seek reloaded its selected block"
  let some (before, offset) := boundary | throw (IO.userError "missing iterator boundary")
  fault.set (some offset)
  match ← before.pull.toBaseIO with
  | .ok _ => throw (IO.userError "iterator did not propagate a failing boundary read")
  | .error error => require (error == "injected block transition failure") "iterator changed error"
  fault.set none
  corrupt.set (some offset)
  match ← before.pull.toBaseIO with
  | .ok _ => throw (IO.userError "iterator accepted a corrupted boundary packet")
  | .error error => require (error == "SSTable CRC32C mismatch") "iterator changed CRC error"
  corrupt.set none
  require ((← ok before.pull).map Prod.fst == rows[before.index]?) "retry skipped a boundary row"
  require ((← ok (handle.cursorAt (rows.length + 3)).pull).isNone) "arbitrary cursor past EOF"

private def exerciseMalformed (path : System.FilePath) : IO Unit := do
  let layout : Unified.Layout := ⟨some 1, some 0, 901⟩
  let rows : List Entry := (List.range 9).map fun i => ⟨⟨#[i.toUInt8 * 2]⟩, .empty⟩
  save path layout rows ⟨1, 1⟩
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
  match ← (withFault.cursorAt 0).pull.toBaseIO with
  | .ok _ => throw (IO.userError "failed interior read became an iterator item")
  | .error error => require (error == "injected interior read failure") "iterator changed index error"
  match ← (withFault.seekCursor ⟨#[0]⟩).toBaseIO with
  | .ok _ => throw (IO.userError "failed interior read became a seek cursor")
  | .error error => require (error == "injected interior read failure") "iterator changed seek error"
  require ((← ok (withFault.lookup ⟨#[255]⟩)).isNone) "lookup after a reported read error"

private def exerciseLargeFences (path : System.FilePath) : IO Unit := do
  let width := maxRowSize - Unified.refPrefixSize - Unified.checksumSize
  let layout : Unified.Layout := ⟨some width, some 0, 902⟩
  let rows : List Entry := (List.range 3).map fun i =>
    ⟨⟨(Array.replicate width 0).set! (width - 1) i.toUInt8⟩, .empty⟩
  save path layout rows ⟨1, 1⟩
  let handle ← ok (openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path layout.tableId)
  require (handle.height == 2) "maximal fence keys did not reduce the level"
  let mut cursor := handle.cursorAt 0
  for expected in rows do
    require ((← ok (handle.lookup expected.key)) == some .empty) "split index packet lookup"
    let some (row, rest) ← ok cursor.pull | throw (IO.userError "split index iterator ended early")
    require (row == expected) "split index iterator"
    cursor := rest
  require ((← ok cursor.pull).isNone) "split index iterator EOF"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  for keyWidth in [none, some 2] do
    for valueWidth in [none, some 2] do
      let layout : Unified.Layout := ⟨keyWidth, valueWidth, 900⟩
      exerciseLayout (dir / s!"recursive-{keyWidth.isSome}-{valueWidth.isSome}") layout
      exerciseIterator (dir / s!"iterator-{keyWidth.isSome}-{valueWidth.isSome}") layout
  exerciseMalformed (dir / "malformed")
  exerciseLargeFences (dir / "large-fences")
  let path := dir / "empty"
  let layout : Unified.Layout := ⟨some 0, some 0, 903⟩
  save path layout []
  let empty ← ok (openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path layout.tableId)
  require (empty.rowCount == 0 && (← ok (empty.lookup .empty)).isNone) "empty recursive table"
  require ((← ok (empty.cursorAt 0).pull).isNone && (← ok (empty.seekCursor .empty)).index == 0)
    "empty recursive iterator"
  IO.println "ALVSST06 recursive SSTable native fixtures passed"

end ImmutableSSTable.Recursive.Fixtures

def main : IO Unit :=
  ImmutableSSTable.Recursive.Fixtures.run
