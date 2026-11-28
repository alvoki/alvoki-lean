import Alvoki.Experiments.SortedRun.SSTable

open ImmutableSSTable ImmutableSSTable.Unified SortedRun

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def entry (key value : UInt8) : Entry :=
  ⟨⟨#[key]⟩, ⟨#[value]⟩⟩

private def putInput (path : System.FilePath) (id : UInt64) (rows : List Entry)
    (options : BuildOptions) : IO Unit := do
  let input ← IO.mkRef rows
  let count ← buildFileSynced path ⟨none, none, id⟩ (do
    match ← input.get with
    | [] => return none
    | row :: rest =>
      input.set rest
      return some row) options
  check (count == rows.length) "input fixture count"

private def matrixOptions : BuildOptions := ⟨64, 128⟩

private def checkMerge (dir : System.FilePath) (newRows oldRows expected : List Entry) : IO Unit := do
  IO.FS.withTempDir fun paths => do
    let newerPath := paths / "newer"
    let olderPath := paths / "older"
    let outputPath := dir / "merged"
    putInput newerPath 11 newRows matrixOptions
    putInput olderPath 12 oldRows matrixOptions
    let newer ← (openNativeChecked newerPath 11).adapt IO.userError
    let older ← (openNativeChecked olderPath 12).adapt IO.userError
    let count ← buildMergedFileSynced newer older outputPath ⟨none, none, 13⟩ matrixOptions
    let output ← (openNativeChecked outputPath 13).adapt IO.userError
    check (count == expected.length && output.rowCount == count) "merged row count"
    for (row, index) in expected.zipIdx do
      check ((← (output.next index).adapt IO.userError) == some (row, index + 1))
        "merged cursor differs from oracle"
      check ((← (output.lookup row.key).adapt IO.userError) == some row.value)
        "merged lookup differs from oracle"
    check ((← (output.next count).adapt IO.userError).isNone) "merged EOF"
    IO.FS.removeFile outputPath

private def expectBuildError (output : System.FilePath) (expected : String)
    (action : IO Nat) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw (IO.userError s!"build succeeded despite: {expected}")
  | .error (.userError actual) => check (actual == expected) s!"unexpected builder error: {actual}"
  | .error error => throw error
  check (!(← output.pathExists)) "failed merge left its fresh destination"

private def faultAfterRow (dir : System.FilePath) : IO Unit := do
  let newerPath := dir / "fault-newer"
  let olderPath := dir / "fault-older"
  putInput newerPath 21 [entry 1 10, entry 3 30] matrixOptions
  putInput olderPath 22 [entry 2 20] matrixOptions
  let armed ← IO.mkRef false
  let reads ← IO.mkRef (0 : Nat)
  let calls ← IO.mkRef ([] : List Nat)
  let readOps := { nativeReadPrimitives with pread := fun held offset count => do
    if ← armed.get then
      reads.modify (· + 1)
      throw "required pread failed after first output row"
    nativeReadPrimitives.pread held offset count }
  let acquired ← (openCheckedWith readOps Alvoki.CRC32C.extend newerPath 21).adapt IO.userError
  let newer := { acquired with next := fun index => do
    calls.modify (· ++ [index])
    let result ← acquired.next index
    if index == 0 then armed.set true
    return result }
  let older ← (openNativeChecked olderPath 22).adapt IO.userError
  let output := dir / "fault-output"
  expectBuildError output "required pread failed after first output row"
    (buildMergedFileSynced newer older output ⟨none, none, 23⟩ matrixOptions)
  check ((← calls.get) == [0, 1] && (← reads.get) == 1)
    "required read was retried, skipped or made before the first row"

private def decodeAfterRow (dir : System.FilePath) : IO Unit := do
  let newerPath := dir / "decode-newer"
  let olderPath := dir / "decode-older"
  putInput newerPath 31 [entry 1 10, entry 3 30] matrixOptions
  putInput olderPath 32 [entry 2 20] matrixOptions
  let bytes : Codec ByteArray := ⟨id, Except.ok⟩
  let values : Codec ByteArray := ⟨id, fun v =>
    if v == (entry 3 30).value then .error "required value decode failed" else .ok v⟩
  let newer : TypedTable (EIO String) ByteArray ByteArray :=
    ⟨← (openNativeChecked newerPath 31).adapt IO.userError, bytes, values⟩
  let older : TypedTable (EIO String) ByteArray ByteArray :=
    ⟨← (openNativeChecked olderPath 32).adapt IO.userError, bytes, values⟩
  let cursor ← IO.mkRef (Frontier.start (row := ByteArray × ByteArray) 0 0)
  let slot : Slot IO (Frontier Nat Nat (ByteArray × ByteArray)) := ⟨cursor.get, cursor.set⟩
  let output := dir / "decode-output"
  expectBuildError output "required value decode failed"
    (buildMergedWith Prod.fst (Entry.encode bytes values)
      (fun i => (newer.next i).adapt IO.userError) (fun i => (older.next i).adapt IO.userError)
      slot (nativeOutputOps syncFileHandle) Alvoki.CRC32C.extend
      output ⟨none, none, 33⟩ IO.userError matrixOptions)

private def rootCapacity (dir : System.FilePath) : IO Unit := do
  let newerPath := dir / "large-newer"
  let olderPath := dir / "large-older"
  let wide (byte : UInt8) : Entry := ⟨⟨Array.replicate (maxRowSize / 2) byte⟩, .empty⟩
  putInput newerPath 41 [wide 1] matrixOptions
  putInput olderPath 42 [wide 2] matrixOptions
  let newer ← (openNativeChecked newerPath 41).adapt IO.userError
  let older ← (openNativeChecked olderPath 42).adapt IO.userError
  let output := dir / "large-output"
  expectBuildError output "SSTable root index exceeds size limit"
    (buildMergedFileSynced newer older output ⟨none, none, 43⟩ matrixOptions)
  check ((← (newer.next 0).adapt IO.userError).isSome && (← (older.next 0).adapt IO.userError).isSome)
    "capacity rejection damaged a valid input"

def main : IO Unit := IO.FS.withTempDir fun dir => do
  let big := (List.range 180).map (fun i => entry i.toUInt8 9)
  let tombstone : Entry := ⟨(entry 7 0).key, .empty⟩
  let wins := [tombstone, entry 139 12]
  let expected := big.map (fun row => (wins.find? (·.key == row.key)).getD row)
  checkMerge dir wins big expected
  checkMerge dir big wins big
  checkMerge dir [] big big
  checkMerge dir big [] big
  checkMerge dir [] [] []
  faultAfterRow dir
  decodeAfterRow dir
  rootCapacity dir
  IO.println "native sorted-run merge fixtures passed"
