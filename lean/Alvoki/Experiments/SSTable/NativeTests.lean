import Alvoki.Experiments.SSTable.Native

open ImmutableSSTable

namespace ImmutableSSTable.NativeTests

private def check (condition : Bool) (label : String) : IO Unit := do
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

def run : IO Unit := IO.FS.withTempDir fun dir => do
  let path := dir / "run"
  let rows : List Entry := [⟨2, 200⟩, ⟨7, 700⟩, ⟨11, 1100⟩]
  check ((← build path rows) == 3) "streamed count"
  check ((← IO.FS.readBinFile path) == encodeImage rows) "native builder image"
  let table ← ok (openNative path)
  check ((← ok (table.lookup 7)) == some 700) "point hit"
  check ((← ok (table.lookup 3)) == none) "point miss"
  check ((← ok (table.seek 3)) == 1) "lower bound"
  check ((← ok (table.next 3)).isNone) "logical EOF"

  -- Replacing the path cannot retarget pread on this live table.
  IO.FS.rename path (dir / "old")
  discard <| build path [⟨7, 77⟩]
  check ((← ok (table.lookup 7)) == some 700) "retained inode after rename"
  let other ← ok (openNative path)
  check ((← ok (other.lookup 7)) == some 77) "replacement file"
  expectError (openNative (dir / "missing")) "missing file"
  check (!(← (build path []).toBaseIO).isOk) "builder overwrote existing file"

  let bad := dir / "bad"
  for invalid in [[(⟨2, 1⟩ : Entry), ⟨2, 2⟩], [⟨2, 1⟩, ⟨1, 2⟩]] do
    check (!(← (build bad invalid).toBaseIO).isOk) "builder accepted unordered key"
    check (!(← bad.pathExists)) "failed construction left an incomplete file"
  -- Force both failures: the input callback removes the incomplete file before
  -- throwing, so the builder's cleanup sees ENOENT.
  let primary := IO.userError "input stream failed"
  let result ← (buildFile bad (do IO.FS.removeFile bad; throw primary)).toBaseIO
  match result with
  | .error err => check (err.toString == primary.toString) "cleanup masked input error"
  | .ok _ => throw <| IO.userError "failed input reported success"
  discard <| build bad []
  let empty ← ok (openNative bad)
  check ((← ok (empty.next 0)).isNone) "empty table"

  -- Truncate the same inode after open. An in-range short or empty read is an
  -- error; the cursor one past the end still denotes logical EOF.
  IO.FS.writeBinFile path ((encodeHeader 1) ++ ByteArray.mk #[1, 2, 3])
  expectError (other.next 0) "short row accepted"
  expectError (openNative path) "truncated extent accepted"
  IO.FS.writeBinFile path (encodeHeader 1)
  expectError (other.lookup 7) "physical EOF reported as key miss"
  check ((← ok (other.next 1)).isNone) "logical EOF after truncation"
  IO.FS.writeBinFile path ((encodeHeader 0) ++ ByteArray.mk #[0])
  expectError (openNative path) "trailing bytes accepted"
  IO.FS.writeBinFile path (ByteArray.mk (Array.replicate 16 0))
  expectError (openNative path) "bad magic accepted"
  IO.FS.writeBinFile path ((encodeHeader 0).set! 7 49)
  expectError (openNative path) "accepted v1 table as v2"
  IO.FS.writeBinFile path (ByteArray.mk #[1])
  expectError (openNative path) "short header accepted"

  -- fstat succeeds on a write-only regular file; pread itself returns EBADF.
  let writeOnly ← IO.FS.Handle.mk bad .write
  writeOnly.write (encodeHeader 0)
  writeOnly.flush
  let source := handleSource writeOnly
  check ((← ok source.size) == 16) "fixture extent"
  expectError (source.readAt 0 16) "pread error became EOF"
  expectError (source.readAt 0 25) "oversized read accepted"
  expectError (source.readAt (2^64) 1) "offset wrapped before pread"
  IO.println "immutable SSTable native fixtures passed"

end ImmutableSSTable.NativeTests

def main : IO Unit := ImmutableSSTable.NativeTests.run
