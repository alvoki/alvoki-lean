import SnapshotTable

open Alvoki.Sequential

private def expect (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def requireSome (result : Option α) (message : String) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError message)

private def checkPins : IO Unit := do
  let empty : SnapshotTable UInt64 := .empty
  let _ ← requireSome (SnapshotPins.empty.advance 1) "empty pin list blocked floor advance"
  let base ← requireSome (empty.write 9 (some 10)) "initial write failed"
  expect ((base.acquireAt 2).isNone) "acquisition accepted a future sequence"
  let (first, base) ← requireSome base.acquire "first pin failed"
  let (other, base) ← requireSome base.acquire "second pin failed"
  expect (decide (first.handle ≠ other.handle ∧ first.sequence = other.sequence))
    "two acquisitions at one sequence must get distinct handles"
  let newer ← requireSome (base.flush.write 9 (some 20)) "second write failed"
  let compacted ← requireSome (newer.flush.compact 0) "adjacent compaction failed"
  expect (decide (compacted.lookup first.handle 9 = some (some 10))) "point read changed across write and compaction"
  expect (decide (compacted.range first.handle 9 10 = base.range first.handle 9 10))
    "range read changed across write and compaction"
  expect ((compacted.advanceFloor 2).isNone) "advancement crossed active pins"

  let released := (compacted.release first.handle).release first.handle
  expect ((released.lookup first.handle 9).isNone) "released handle remained visible"
  expect (decide (released.lookup other.handle 9 = some (some 10))) "duplicate release cleared another pin"
  expect ((released.advanceFloor 2).isNone) "second pin stopped constraining the floor"
  let advanced ← requireSome ((released.release other.handle).advanceFloor 2) "advancement failed after releases"
  expect ((advanced.advanceFloor 1).isNone) "floor moved backwards"
  expect ((advanced.advanceFloor 3).isNone) "floor crossed the committed sequence"
  expect ((advanced.acquireAt 1).isNone) "snapshot below the floor was acquired"
  let (latest, advanced) ← requireSome advanced.acquire "latest snapshot acquisition failed"
  expect (decide (other.handle.id < latest.handle.id)) "retired handle was reused"
  expect (decide (advanced.lookup latest.handle 9 = some (some 20))) "latest snapshot missed the second write"
  expect ((advanced.lookup first.handle 9).isNone) "stale handle became active"

private def checkPurge : IO Unit := do
  let older : History UInt64 := .singleton ⟨9, 4, some 10⟩
  let tombstone : History UInt64 := .singleton ⟨9, 4, none⟩
  let tied : Table UInt64 := ⟨[older, tombstone], .empty⟩
  expect ((tied.purgeAt 1 9 4 4).isNone) "purge exposed the older equal-sequence version"

  let laterTombstone : History UInt64 := .singleton ⟨9, 5, none⟩
  let later : Table UInt64 := ⟨[older, laterTombstone], .empty⟩
  expect ((later.purgeAt 1 9 5 4).isNone) "purge missed exposure after the floor"
  expect ((later.purgeAt 2 9 5 4).isNone) "purge accepted an out-of-range run index"

  let put : History UInt64 := .singleton ⟨10, 5, some 20⟩
  let isolated : Table UInt64 := ⟨[laterTombstone, put], .empty⟩
  let purged ← requireSome (isolated.purgeAt 0 9 5 4) "purge rejected an isolated tombstone"
  expect (decide (purged.runs.head?.map (·.rows.length) = some 0)) "purge did not remove the physical row"
  expect (decide (purged.lookup 9 5 = none ∧ purged.range 9 11 5 = isolated.range 9 11 5))
    "safe purge changed point or range results"

def main : IO Unit := do
  checkPins
  checkPurge
  IO.println "Snapshot floor, handle, read stability, and physical-run purge regressions passed."
