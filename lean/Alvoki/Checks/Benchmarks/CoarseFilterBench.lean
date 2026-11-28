import Alvoki.Checks.Benchmarks.CoarseFilter

namespace ImmutableSSTable.Recursive.CoarseFilter

private abbrev OpenTable := Handle (EIO String)
private abbrev OpenSession := Session (EIO String)
private abbrev Query := ByteArray × Option ByteArray

private def crc := Alvoki.CRC32C.extend

private def run (action : EIO String α) : IO α :=
  action.adapt IO.userError

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def key (n : Nat) : ByteArray :=
  ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
    (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

private def value (i : Nat) : ByteArray :=
  encodeOffset (if i % 7 = 0 then 0 else i + 1)

private def nextEntry (lane rows : Nat) : IO (IO (Option Entry)) := do
  let index ← IO.mkRef 0
  return do
    let row ← index.get
    if row ≥ rows then return none
    index.set (row + 1)
    return some ⟨key (8 * row + 2 * lane), value row⟩

private structure Files where
  primary : System.FilePath
  companion : System.FilePath
  tableId : UInt64

private def create (dir : System.FilePath) (lane rows : Nat) :
    IO (Files × Nat × Nat) := do
  let files : Files := ⟨dir / s!"data-{lane}", dir / s!"filters-{lane}", (100 + lane).toUInt64⟩
  let next ← nextEntry lane rows
  let opts := nativeOutputOps (fun _ => pure ())
  let start ← IO.monoNanosNow
  let actual ← buildFileWith opts crc files.primary (⟨some 8, some 8, files.tableId⟩)
    next IO.userError { dataTarget := 4096, indexTarget := 1024 }
  let dataTime := (← IO.monoNanosNow) - start
  require (actual == rows) "data supplier ended at a different count"
  let maskSupply ← supply (← nextEntry lane rows)
  let start ← IO.monoNanosNow
  let partitions ← buildFileWith opts crc files.companion (layout files.tableId) maskSupply
    IO.userError { dataTarget := 4096, indexTarget := 1024 }
  let filterTime := (← IO.monoNanosNow) - start
  require (partitions == (rows + partitionRows - 1) / partitionRows)
    "coarse supplier ended at a different count"
  return (files, dataTime, filterTime)

private structure Reads where
  dataCalls : Nat := 0
  dataBytes : Nat := 0
  filterCalls : Nat := 0
  filterBytes : Nat := 0

private def source (path : System.FilePath) (filters : Bool) (reads : IO.Ref Reads) :
    IO (Source (EIO String)) := do
  let raw := handleSource (← IO.FS.Handle.mk path .read)
  return { raw with readAt := fun offset count => do
    reads.modify fun stat =>
      if filters then
        { stat with filterCalls := stat.filterCalls + 1, filterBytes := stat.filterBytes + count }
      else
        { stat with dataCalls := stat.dataCalls + 1, dataBytes := stat.dataBytes + count }
    raw.readAt offset count }

private def openBase (files : Files) (reads : IO.Ref Reads) : IO OpenTable := do
  run (openChecked (← source files.primary false reads) crc files.tableId)

private def openPair (files : Files) (reads : IO.Ref Reads) (representation : Representation)
    (policy : Policy) : IO OpenSession := do
  let base ← openBase files reads
  let filters ← run (openChecked (← source files.companion true reads) crc files.tableId)
  run (openSession base filters representation policy)

private inductive Mode where
  | plain
  | coarse (representation : Representation) (policy : Policy)

private inductive Member where
  | plain (base : OpenTable)
  | coarse (session : OpenSession)

private def Member.lookup (member : Member) (key : ByteArray) :
    EIO String (Probe × Member) :=
  match member with
  | .plain base => do return (⟨← base.lookup key, false, none⟩, member)
  | .coarse session => do
    let (probe, next) ← session.probe key
    return (probe, .coarse next)

private def Member.retained : Member → Nat
  | .plain _ => 0
  | .coarse session => session.resident.bytes

private structure Batch where
  members : Array Member
  cacheHits : Nat := 0
  positives : Nat := 0
  tests : Nat := 0

private def Batch.resident (batch : Batch) : Nat :=
  batch.members.foldl (fun total member => total + member.retained) 0

private def chain (batch : Batch) (key : ByteArray) :
    EIO String (Option ByteArray × Batch) := do
  let mut batch := batch
  for i in [:batch.members.size] do
    let some member := batch.members[i]? | throw "invalid chain index"
    let (probe, updated) ← member.lookup key
    batch := {
      members := batch.members.set! i updated
      cacheHits := batch.cacheHits + (if probe.cacheHit then 1 else 0)
      tests := batch.tests + (if probe.filterTest.isSome then 1 else 0)
      positives := batch.positives + (if probe.filterTest == some true then 1 else 0) }
    if probe.value.isSome then return (probe.value, batch)
  return (none, batch)

private def queryBatch (rows : Nat) (workload : String) : Array Query := Id.run do
  let mut seed := 12345
  let mut queries := #[]
  for _ in [:4096] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let i := if workload == "repeat-miss" then rows / 3 else (seed >>> 8) % (rows - 1)
    let (suffix, expected) := if workload == "recent" then (0, some (value i))
      else if workload == "oldest" then (6, some (value i)) else (1, none)
    queries := queries.push (key (8 * i + suffix), expected)
  return queries

private def openBatch (tables : Array Files) (mode : Mode) (reads : IO.Ref Reads) :
    IO Batch := do
  let mut members := #[]
  for table in tables do
    let member ← match mode with
      | .plain => .plain <$> openBase table reads
      | .coarse representation policy => .coarse <$> openPair table reads representation policy
    members := members.push member
  return ⟨members, 0, 0, 0⟩

private def report (rows : Nat) (label workload stage : String) (items elapsed : Nat)
    (stats : Reads := {}) (batch : Batch := ⟨#[], 0, 0, 0⟩) : IO Unit := do
  IO.println s!"{rows},{label},{workload},{stage},{items},{elapsed},{stats.dataCalls},{stats.dataBytes},{stats.filterCalls},{stats.filterBytes},{batch.cacheHits},{batch.tests},{batch.positives},{batch.resident}"

private def exercise (rows : Nat) (tables : Array Files) (label : String) (mode : Mode) :
    IO Unit := do
  let reads ← IO.mkRef ({} : Reads)
  for workload in ["repeat-miss", "uniform-miss", "oldest", "recent"] do
    reads.set {}
    let start ← IO.monoNanosNow
    let mut batch ← openBatch tables mode reads
    report rows label workload "startup" 1 ((← IO.monoNanosNow) - start) (← reads.get) batch
    let queries := queryBatch rows workload
    let mut beginAt := 0
    for (stage, stop) in [("first", 1), ("follow-up", queries.size)] do
      reads.set {}
      batch := { batch with cacheHits := 0, tests := 0, positives := 0 }
      let start ← IO.monoNanosNow
      for (query, expected) in queries.extract beginAt stop do
        let (out, after) ← run (chain batch query)
        require (out == expected) s!"wrong result in {workload} from {label}"
        batch := after
      report rows label workload stage (stop - beginAt) ((← IO.monoNanosNow) - start) (← reads.get) batch
      beginAt := stop

private def failureCheck (table other : Files) : IO Unit := do
  let reads ← IO.mkRef ({} : Reads)
  let base ← openBase table reads
  let otherFilters ← run (openChecked (← source other.companion true reads) crc other.tableId)
  match ← (openSession base otherFilters .packed (.latest (32 * 1024))).toBaseIO with
  | .ok _ => throw (IO.userError "coarse filter opened for the wrong table ID")
  | .error message => require (message == "coarse filter table identity mismatch") message

  let source ← source table.companion true reads
  let fault ← IO.mkRef (0 : Nat)
  let switched := { source with readAt := fun offset count => do
    let mode ← fault.get
    if mode == 1 then throw "injected coarse filter read failure"
    let bytes ← source.readAt offset count
    return if mode == 2 then bytes.set! 0 (bytes[0]! ^^^ 1) else bytes }
  let filters ← run (openChecked switched crc table.tableId)
  let session ← run (openSession base filters .packed (.latest (32 * 1024)))
  let hit := key 0
  let (first, session) ← run (session.probe hit)
  require (!first.cacheHit && first.value == some (value 0)) "cold tombstone probe"
  reads.set {}
  fault.set 1
  let (again, _) ← run (session.probe hit)
  require (again.cacheHit && again.value == first.value) "cached tombstone probe"
  require ((← reads.get).filterCalls == 0) "cache hit issued a filter read"
  let nextPartition := key (8 * partitionRows)
  for (mode, expected) in [(1, "injected coarse filter read failure"), (2, "SSTable CRC32C mismatch")] do
    fault.set mode
    match ← (session.probe nextPartition).toBaseIO with
    | .ok _ => throw (IO.userError "a filter packet fault was treated as a successful probe")
    | .error message => require (message == expected) message

def main (args : List String) : IO Unit := IO.FS.withTempDir fun path => do
  let [count] := args | throw (IO.userError "usage: coarseFilterCheck ROWS")
  let some rows := count.toNat? | throw (IO.userError "expected rows")
  unless partitionRows < rows && rows ≤ 1024 * 1024 + 1 do
    throw (IO.userError "row count outside benchmark limits")
  IO.println "rows_per_table,mode,workload,stage,items,elapsed_ns,data_reads,data_bytes,filter_reads,filter_bytes,cache_hits,filter_tests,filter_positives,resident_bytes"
  let mut tables := #[]
  let mut dataTime := 0
  let mut filterTime := 0
  for lane in [:4] do
    let (table, data, filters) ← create path lane rows
    tables := tables.push table
    dataTime := dataTime + data
    filterTime := filterTime + filters
  report rows "plain" "build" "construct" (4 * rows) dataTime
  report rows "coarse" "build" "construct" (4 * rows) filterTime
  let some table := tables[0]? | throw (IO.userError "missing fixture table")
  let some other := tables[1]? | throw (IO.userError "missing alternate table")
  failureCheck table other
  exercise rows tables "plain" .plain
  exercise rows tables "no-cache" (.coarse .packed (.latest 0))
  exercise rows tables "packed-latest" (.coarse .packed (.latest (32 * 1024)))
  exercise rows tables "decoded-latest" (.coarse .decoded (.latest (32 * 1024)))
  if rows ≤ 2 * partitionRows + 1 then
    exercise rows tables "packed-eager" (.coarse .packed (.eager (64 * 1024)))
    exercise rows tables "decoded-eager" (.coarse .decoded (.eager (64 * 1024)))

end ImmutableSSTable.Recursive.CoarseFilter

def main := ImmutableSSTable.Recursive.CoarseFilter.main
