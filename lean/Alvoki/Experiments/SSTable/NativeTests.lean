import Alvoki.Experiments.SSTable.Native

open ImmutableSSTable

namespace ImmutableSSTable.NativeTests

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def ok (act : EIO String α) : IO α := act.adapt IO.userError

private def expectError (act : EIO String α) (label : String) : IO Unit := do
  check (!(← act.toBaseIO).isOk) label

private def build (path : System.FilePath) (rows : List Entry) : IO Nat := do
  let ref ← IO.mkRef rows
  buildFile path do
    match ← ref.get with
    | [] => return none
    | r :: rs => ref.set rs; return some r

private def keyCodec : Codec UInt8 where
  encode key := ⟨#[key, 0]⟩
  decode bytes :=
    match bytes.data.toList with
    | [key, 0] => .ok key
    | _ => .error "invalid test key"

private def valueCodec : Codec UInt8 where
  encode value := ⟨#[255 - value]⟩
  decode bytes :=
    match bytes.data.toList with
    | [value] => .ok (255 - value)
    | _ => .error "invalid test value"

private def checkNativeReads (dir : System.FilePath) : IO Unit := do
  let path := dir / "run"
  let key := keyCodec.encode
  let value := valueCodec.encode
  let rows : List Entry := ⟨.empty, .empty⟩ :: [(2, 20), (7, 70)].map (Entry.encode keyCodec valueCodec)
  check ((← build path rows) == 3) "streamed count"
  check ((← IO.FS.readBinFile path) == encodeImage rows) "native builder image"
  let table ← ok (openNative path)
  let typed := TypedTable.mk table keyCodec valueCodec
  check ((← ok (typed.lookup 7)) == some 70) "typed point hit"
  check ((← ok (typed.lookup 3)).isNone) "typed point miss"
  check ((← ok (table.lookup .empty)) == some .empty) "empty key/value"
  check ((← ok (typed.seek 3)) == 2) "typed lower bound"
  check ((← ok (typed.next 1)) == some ((2, 20), 2)) "typed iteration"
  check ((← ok (typed.next 3)).isNone) "typed logical EOF"
  expectError (typed.next 0) "typed iteration hid caller decoding error"

  -- Replacing the path cannot retarget pread on this live table.
  IO.FS.rename path (dir / "old")
  discard <| build path [⟨key 7, value 77⟩]
  check ((← ok (table.lookup (key 7))) == some (value 70)) "retained inode after rename"
  let other ← ok (openNative path)
  check ((← ok (other.lookup (key 7))) == some (value 77)) "replacement file"
  expectError (openNative (dir / "missing")) "missing file"
  check (!(← (build path []).toBaseIO).isOk) "builder overwrote existing file"
  check ((← ok (other.lookup (key 7))) == some (value 77)) "failed build modified existing file"

  -- Truncate the same inode after open. The offset pair now reads short.
  let image ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (image.extract 0 (image.size - footerSize - 1))
  expectError (other.next 0) "short index pair accepted"
  expectError (openNative path) "truncated extent accepted"
  IO.FS.writeBinFile path .empty
  expectError (other.lookup (key 7)) "physical EOF reported as key miss"
  check ((← ok (other.next 1)).isNone) "logical EOF after truncation"

private def checkBuildFailures (dir : System.FilePath) : IO Unit := do
  let path := dir / "bad"
  let byte (x : UInt8) := ByteArray.mk #[x]
  for invalid in [[(⟨byte 2, .empty⟩ : Entry), ⟨byte 2, byte 3⟩],
                  [⟨byte 2, .empty⟩, ⟨byte 1, .empty⟩],
                  [⟨.empty, ⟨Array.replicate maxRowSize 0⟩⟩]] do
    check (!(← (build path invalid).toBaseIO).isOk) "builder accepted invalid row"
    check (!(← path.pathExists)) "failed construction left an incomplete file"

  -- The input callback fails after the builder has already written a row.
  -- Removing the unfinished file also makes final cleanup encounter ENOENT.
  let primary := IO.userError "input stream failed"
  let supplied ← IO.mkRef false
  let result ← (buildFile path do
    if ← supplied.get then
      IO.FS.removeFile path
      throw primary
    supplied.set true
    return some ⟨.empty, .empty⟩).toBaseIO
  match result with
  | .error err => check (err.toString == primary.toString) "cleanup masked input error"
  | .ok _ => throw (IO.userError "failed input reported success")

  discard <| build path []
  let empty ← ok (openNative path)
  check ((← IO.FS.readBinFile path) == encodeImage []) "empty file image"
  check ((← ok (empty.seek .empty)) == 0 && (← ok (empty.next 0)).isNone) "empty table"

  let image := encodeImage []
  for invalid in [image ++ byte 0, image.set! 8 0, image.set! 15 50, byte 1] do
    IO.FS.writeBinFile path invalid
    expectError (openNative path) "invalid footer accepted"

  -- fstat succeeds on a write-only regular file; pread itself returns EBADF.
  let writeOnly ← IO.FS.Handle.mk path .write
  writeOnly.write image
  writeOnly.flush
  let source := handleSource writeOnly
  check ((← ok source.size) == image.size) "fixture extent"
  expectError (source.readAt 0 16) "pread error became EOF"
  expectError (source.readAt 0 (maxRowSize + 1)) "oversized read accepted"
  expectError (source.readAt (2^64) 1) "offset wrapped before pread"

private def checkStreamedIndex (dir : System.FilePath) : IO Unit := do
  let path := dir / "large"
  let count := 16385
  let row (i : Nat) : Entry :=
    ⟨⟨#[(i / 256).toUInt8, (i % 256).toUInt8]⟩,
      ⟨Array.replicate (i % 5) (i % 256).toUInt8⟩⟩
  let cursor ← IO.mkRef 0
  let written ← buildFile path do
    let i ← cursor.get
    if i == count then return none
    cursor.set (i + 1)
    return some (row i)
  check (written == count) "large streamed row count"
  let table ← ok (openNative path)
  for i in [0, 8191, 8192, count - 1] do
    check ((← ok (table.next i)) == some (row i, i + 1)) "large index offset"
    check ((← ok (table.lookup (row i).key)) == some (row i).value) "large index lookup"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  checkNativeReads dir
  checkBuildFailures dir
  checkStreamedIndex dir
  IO.println "immutable SSTable native fixtures passed"

end ImmutableSSTable.NativeTests

def main : IO Unit := ImmutableSSTable.NativeTests.run
