import Alvoki.Experiments.SSTable.FixedNative

open ImmutableSSTable

namespace ImmutableSSTable.FixedNativeTests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def ok (action : EIO String α) : IO α := action.adapt IO.userError

private def expectError (action : EIO String α) (message : String) : IO Unit := do
  check (!(← action.toBaseIO).isOk) message

private def build (path : System.FilePath) (layout : Fixed.Layout) (rows : List Entry) : IO Nat := do
  let remaining ← IO.mkRef rows
  Fixed.buildFile path layout do
    match ← remaining.get with
    | [] => return none
    | row :: rest =>
      remaining.set rest
      return some row

private def layout : Fixed.Layout := {
  keyWidth := 1
  valueWidth := 2
  rowsPerBlock := 128
  tableId := 9
}

-- Independent literal image containing one short block and its footer.
private def golden : ByteArray := ⟨#[
  1, 2, 3, 4, 5, 6, 39, 235, 70, 29, 40, 78, 122, 251,
  65, 76, 86, 83, 83, 84, 48, 52,
  2, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0,
  128, 0, 0, 0, 0, 0, 0, 0,
  9, 0, 0, 0, 0, 0, 0, 0,
  40, 5, 46, 115, 108, 123, 4, 18]⟩

private def byte (value : Nat) : ByteArray := ⟨#[value.toUInt8]⟩

private def row (index : Nat) : Entry :=
  ⟨byte index, ⟨#[index.toUInt8, (255 - index).toUInt8]⟩⟩

private def checkGolden (dir : System.FilePath) : IO Unit := do
  let path := dir / "golden"
  let first : Entry := ⟨byte 1, ⟨#[2, 3]⟩⟩
  let second : Entry := ⟨byte 4, ⟨#[5, 6]⟩⟩
  IO.FS.writeBinFile path golden
  let table ← ok (Fixed.openNative path)
  check (table.rowCount == 2) "fixed footer count"
  check ((← ok (table.next 0)) == some (first, 1)) "fixed literal first row"
  check ((← ok (table.lookup second.key)) == some second.value) "fixed literal point hit"
  check ((← ok (table.seek (byte 3))) == 1) "fixed literal lower bound"
  check ((← ok (table.lookup (byte 3))).isNone) "fixed literal point miss"
  let written ← build (dir / "golden-build") layout [first, second]
  check (written == 2) "fixed literal build count"
  check ((← IO.FS.readBinFile (dir / "golden-build")) == golden) "fixed literal wire bytes"
  expectError (openNative path) "variable reader accepted fixed footer"
  IO.FS.writeBinFile path (encodeImage [first, second])
  expectError (Fixed.openNative path) "fixed reader accepted variable footer"

  for offset in [0, 1, 6] do
    IO.FS.writeBinFile path (golden.set! offset (golden[offset]! ^^^ 1))
    let corrupted ← ok (Fixed.openNative path)
    expectError (corrupted.next 0) "fixed corrupted block admitted"
  for bytes in [golden.set! 22 3, golden.set! 69 0, golden ++ byte 1,
                golden.extract 0 (golden.size - 1)] do
    IO.FS.writeBinFile path bytes
    expectError (Fixed.openNative path) "fixed corrupt footer or extent admitted"

private def checkExtent (dir : System.FilePath) : IO Unit := do
  let emptyPath := dir / "empty"
  check ((← build emptyPath layout []) == 0) "fixed empty build count"
  check ((← IO.FS.readBinFile emptyPath).size == 56) "fixed empty image size"
  let empty ← ok (Fixed.openNative emptyPath)
  check (empty.rowCount == 0) "fixed empty footer"
  check ((← ok (empty.lookup ByteArray.empty)).isNone) "fixed empty lookup"
  check ((← ok (empty.next 0)).isNone) "fixed empty next"

  for rowsPerBlock in [1, 128] do
    let path := dir / s!"short-{rowsPerBlock}"
    let count := 131
    let selected := { layout with rowsPerBlock := rowsPerBlock }
    let written ← build path selected ((List.range count).map row)
    let expectedBytes := count * 3 + ((count + rowsPerBlock - 1) / rowsPerBlock) * 8 + 56
    check (written == count) "fixed streamed count"
    check ((← IO.FS.readBinFile path).size == expectedBytes) "fixed image extent"
    let table ← ok (Fixed.openNative path)
    for index in List.range count do
      check ((← ok (table.next index)) == some (row index, index + 1)) "fixed indexed row"
    for index in [0, 127, 128, count - 1] do
      check ((← ok (table.lookup (row index).key)) == some (row index).value) "fixed boundary lookup"
    check ((← ok (table.next count)).isNone) "fixed end cursor"
    check ((← ok (table.seek (byte 255))) == count) "fixed seek past end"
    check ((← ok (table.seek ⟨#[127, 0]⟩)) == 128) "fixed query need not match stored width"

private def checkRelocation (dir : System.FilePath) : IO Unit := do
  let path := dir / "position"
  let otherPath := dir / "identity"
  let rows := (List.range 256).map row
  discard <| build path layout rows
  discard <| build otherPath { layout with tableId := 10 } rows
  let image ← IO.FS.readBinFile path
  let other ← IO.FS.readBinFile otherPath
  let blockSize := 128 * 3 + 8
  let first := image.extract 0 blockSize
  let last := image.extract (2 * blockSize) image.size
  IO.FS.writeBinFile path (first ++ first ++ last)
  let misplaced ← ok (Fixed.openNative path)
  check ((← ok (misplaced.next 0)) == some (row 0, 1)) "untouched fixed block"
  expectError (misplaced.next 128) "fixed block accepted at another ordinal"

  IO.FS.writeBinFile otherPath (first ++ other.extract blockSize other.size)
  let transplanted ← ok (Fixed.openNative otherPath)
  check ((← ok (transplanted.next 128)) == some (row 128, 129)) "untouched other table block"
  expectError (transplanted.next 0) "fixed block accepted from another table"

private def checkBuildFailures (dir : System.FilePath) : IO Unit := do
  let path := dir / "bad"
  for invalid in [{ layout with rowsPerBlock := 0 },
                  { layout with keyWidth := maxRowSize, rowsPerBlock := 1 },
                  { layout with rowsPerBlock := maxRowSize + 1 }] do
    check (!(← (build path invalid []).toBaseIO).isOk) "fixed writer accepted invalid layout"
    check (!(← path.pathExists)) "fixed invalid layout left destination"
    let invalidFooterPath := dir / "invalid-footer"
    IO.FS.writeBinFile invalidFooterPath (Fixed.encodeFooter invalid 0)
    expectError (Fixed.openNative invalidFooterPath) "fixed reader accepted checksummed invalid layout"
  for rows in [[⟨ByteArray.empty, (row 0).value⟩], [⟨(row 0).key, byte 0⟩],
               [row 0, row 0], [row 1, row 0]] do
    check (!(← (build path layout rows).toBaseIO).isOk) "fixed writer accepted invalid rows"
    check (!(← path.pathExists)) "fixed invalid rows left destination"

private def checkRequiredRead : IO Unit := do
  let source : Source (EStateM String Nat) := {
    size := pure golden.size
    readAt := fun offset count => do
      modify (· + 1)
      if offset == 0 then throw "injected block read failure"
      return golden.extract offset (offset + count)
  }
  let .ok table 1 := Fixed.openTable source 0
    | throw (IO.userError "fixed open should read only the footer")
  match table.lookup (byte 1) 10 with
  | .error "injected block read failure" state =>
    check (state == 11) "fixed lookup continued after failed block read"
  | _ => throw (IO.userError "fixed lookup lost the block read error")
  match table.next 2 10 with
  | .ok none 10 => pure ()
  | _ => throw (IO.userError "fixed logical EOF issued a read")

def run : IO Unit := IO.FS.withTempDir fun dir => do
  checkGolden dir
  checkExtent dir
  checkRelocation dir
  checkBuildFailures dir
  checkRequiredRead
  IO.println "immutable fixed SSTable native fixtures passed"

end ImmutableSSTable.FixedNativeTests

def main : IO Unit := ImmutableSSTable.FixedNativeTests.run
