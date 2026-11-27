import Alvoki.Experiments.L0.TableRows
import Alvoki.Experiments.L0.TableSchedule

open ExperimentalL0 ImmutableSSTable
open System

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := IO.FS.withTempDir fun dir => do
  let make (id : UInt64) (rows : Rows) := do
    let supplier ← IO.mkRef rows
    Unified.buildFileSynced (tablePath dir id) ⟨some 8, none, id⟩
      (nextTableRow supplier.get supplier.set)
  require ((← make 1 [(12, .delete)]) == 1) "first writer count"
  require ((← make 2 [(5, .put 42), (12, .put 99)]) == 2) "second writer count"
  let times ← IO.mkRef ([] : List UInt64)
  let failSelectedData ← IO.mkRef false
  let lookup (id key : UInt64) : ExceptT String IO (Option Mutation) := do
    liftM (times.modify (· ++ [id]) : IO Unit)
    withTableAt (m := ExceptT String IO) (fun path => liftM path.symlinkMetadata)
      (fun path use => ExceptT.mk (IO.FS.withFile path .read fun h => (use h).run))
      dir id fun h => do
        let inject ← liftM (failSelectedData.get : IO Bool)
        if inject && id == 2 then
          let source := handleSource h
          let failingSource : Source (EIO String) := {
            source with readAt := fun offset count => do
              -- This fixture's first data packet begins at byte zero.
              if offset == 0 then throw "injected data pread error"
              source.readAt offset count
          }
          ExceptT.mk (withTableSource failingSource id (·.lookup key)).toBaseIO
        else nativeTableAction h id (·.lookup key)
  let tables : Tables (ExceptT String IO) := ⟨fun _ => throw "unused create", fun _ => pure (), lookup⟩
  let probe key := (lookupTables tables key [1, 2]).run
  let hit ← probe 5
  require (hit.toOption == some (some (.put 42))) "first miss must allow later hit"
  let deleted ← probe 12
  require (deleted.toOption == some (some .delete)) "tombstone must stop search"
  let absent ← probe 6
  require (absent.toOption == some none) "healthy miss"
  require ((← make 4 [(5, .put 7)]) == 1) "older table writer count"
  times.set []
  failSelectedData.set true
  let err ← (lookupTables tables 5 [1, 2, 4]).run
  match err with
  | .ok _ => throw (IO.userError "failed data pread must abort lookup")
  | .error message => require (message == "injected data pread error") "unexpected pread error"
  require ((← times.get) == [1, 2]) "failed selected read must not fall back to an older hit"
  failSelectedData.set false
  let damaged := tablePath dir 1
  let bytes ← IO.FS.readBinFile damaged
  IO.FS.writeBinFile damaged (bytes.set! 0 (bytes[0]! ^^^ 1))
  times.set []
  let err ← probe 12
  match err with
  | .ok _ => throw (IO.userError "corrupt data must abort lookup")
  | .error message => require (message == "SSTable CRC32C mismatch") "unexpected read error"
  require ((← times.get) == [1]) "L0 must not probe the next table after an error"
  IO.FS.writeBinFile damaged bytes
  let malformed := tablePath dir 3
  let supplied ← IO.mkRef (some (Entry.mk (keyCodec.encode 5) ByteArray.empty))
  let count ← Unified.buildFileSynced malformed ⟨some 8, none, 3⟩
    (supplied.modifyGet fun pending => (pending, none))
  require (count == 1) "malformed value fixture"
  -- The first probe is a healthy miss. The second opens and checks the bytes
  -- successfully, but typed decoding fails before the third can produce a hit.
  times.set []
  let err ← (lookupTables tables 5 [1, 3, 2]).run
  match err with
  | .ok _ => throw (IO.userError "typed decode error must abort lookup")
  | .error message => require (message == "invalid L0 table mutation") "unexpected decoder error"
  require ((← times.get) == [1, 3]) "L0 must stop on a typed error after a miss"
  IO.println "L0 SSTable scoped consumer checks passed"
