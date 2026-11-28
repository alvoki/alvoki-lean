import Alvoki.Checks.Benchmarks.SSTableWorkload

open ImmutableSSTable

namespace SSTableIndexCacheBench

private def checked (action : EIO String α) : IO α := action.adapt IO.userError

private def format (recursive : Bool) : String :=
  if recursive then "ALVSST06" else "ALVSST05"

private structure IndexPage where
  ref : Unified.Ref
  height : Nat
  isRoot : Bool := false

private def readRefs (recursive : Bool) (layout : Unified.Layout) (page : IndexPage)
    (wire : ByteArray) : Except String (Array Unified.Ref) := do
  let kind := if recursive then Recursive.indexKind page.height else if page.isRoot then 3 else 2
  unless wire.size = page.ref.size do throw "short benchmark index packet"
  let raw ← Unified.decodePacket Alvoki.CRC32C.extend layout.tableId kind page.ref.offset wire
  if recursive then
    Recursive.pageChildren raw page.ref (!page.isRoot)
  else
    let refs ← Unified.decodeIndex raw
    Unified.checkChildren refs page.ref.firstRow page.ref.count page.ref.offset
    unless page.isRoot || (refs.back?).map Unified.Ref.lastKey == some page.ref.lastKey do
      throw "benchmark index fence mismatch"
    return refs

private def collectPages (file : Source (EIO String)) (recursive : Bool) (layout : Unified.Layout)
    (refs : Array Unified.Ref) : Nat → EIO String (Array IndexPage × Nat)
  | 0 => pure (#[], refs.size)
  | h + 1 => do
    let mut pages := #[]
    let mut dataBlocks := 0
    for ref in refs do
      let page : IndexPage := ⟨ref, h + 1, false⟩
      let wire ← file.readAt ref.offset ref.size
      let children ← liftDecode (readRefs recursive layout page wire)
      let (descendants, leafBlocks) ← collectPages file recursive layout children h
      pages := (pages.push page) ++ descendants
      dataBlocks := dataBlocks + leafBlocks
    return (pages, dataBlocks)

private structure Inventory where
  footerAt : Nat
  root : IndexPage
  lower : Array IndexPage
  blocks : Nat

private def inventory (file : Source (EIO String)) (layout : Unified.Layout)
    (recursive : Bool) : EIO String Inventory := do
  let crc := Alvoki.CRC32C.extend
  if recursive then
    let (footer, endAt) ← Recursive.readFooter file crc
    let handle ← Recursive.openChecked file crc layout.tableId
    let (pages, blocks) ← collectPages file recursive layout handle.root (handle.height - 1)
    return ⟨endAt, ⟨footer.rootRef, handle.height, true⟩, pages, blocks⟩
  else
    let (footer, endAt) ← Unified.readFooter file crc
    let handle ← Unified.openChecked file crc layout.tableId
    let (pages, blocks) ← collectPages file recursive layout handle.root 1
    return ⟨endAt, ⟨⟨.empty, footer.rootOffset, footer.rootSize, 0, footer.count⟩, 2, true⟩, pages, blocks⟩

private def Inventory.pages (inv : Inventory) : Array IndexPage :=
  (#[inv.root] ++ inv.lower).qsort fun left right =>
    left.height > right.height || (left.height == right.height && left.ref.offset < right.ref.offset)

private structure WireCache where
  entries : Std.HashMap Nat ByteArray := {}
  used : Nat := 0

private def WireCache.get (cache : WireCache) (offset count : Nat) : Option ByteArray :=
  (cache.entries[offset]?).filter (·.size == count)

private def fillCache (file : Source (EIO String)) (pages : Array IndexPage) (budget : Nat) :
    EIO String WireCache := do
  let mut cache : WireCache := {}
  for page in pages do
    let ref := page.ref
    if cache.used + ref.size ≤ budget then
      let bytes ← file.readAt ref.offset ref.size
      unless bytes.size = ref.size do throw "short cache fill"
      cache := { entries := cache.entries.insert ref.offset bytes, used := cache.used + ref.size }
  return cache

private def cachedSource (file : Source (EIO String)) (cache : WireCache) :
    Source (EIO String) :=
  ⟨file.size, fun offset count =>
    match cache.get offset count with
    | some bytes => pure bytes
    | none => file.readAt offset count⟩

private structure Trace where
  sizeCalls : Nat := 0
  footerCalls : Nat := 0
  footerBytes : Nat := 0
  dataCalls : Nat := 0
  dataBytes : Nat := 0
  indexReads : Nat := 0
  indexReadBytes : Nat := 0
  indexHits : Nat := 0
  indexHitBytes : Nat := 0
  indexOffsets : Array Nat := #[]

private def tracedSource (file : Source (EIO String)) (cache : WireCache)
    (pages : Std.HashMap Nat IndexPage) (footerAt : Nat) (trace : IO.Ref Trace) :
    Source (EIO String) where
  size := do
    trace.modify fun state => { state with sizeCalls := state.sizeCalls + 1 }
    file.size
  readAt offset count := do
    let resident := cache.get offset count
    trace.modify fun state =>
      if offset == footerAt then
        { state with footerCalls := state.footerCalls + 1, footerBytes := state.footerBytes + count }
      else if pages.contains offset then
        let state := { state with indexOffsets := state.indexOffsets.push offset }
        if resident.isSome then
          { state with indexHits := state.indexHits + 1, indexHitBytes := state.indexHitBytes + count }
        else
          { state with indexReads := state.indexReads + 1, indexReadBytes := state.indexReadBytes + count }
      else
        { state with dataCalls := state.dataCalls + 1, dataBytes := state.dataBytes + count }
    match resident with
    | some bytes => pure bytes
    | none => file.readAt offset count

private def openTable (recursive : Bool) (layout : Unified.Layout) (source : Source (EIO String)) :
    EIO String (Table (EIO String)) :=
  if recursive then
    (·.table) <$> Recursive.openChecked source Alvoki.CRC32C.extend layout.tableId
  else
    Unified.openTableChecked source Alvoki.CRC32C.extend layout.tableId

private structure Probe where
  key : ByteArray
  expected : UInt64

private def probes (layout : Unified.Layout) (rows : Nat) :
    Array Probe × Array Probe × Array Probe := Id.run do
  let mut seed := 12345
  let mut hit := #[]
  let mut miss := #[]
  let mut seek := #[]
  for i in [:512] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let index := (seed >>> 8) % rows
    let n := i % 2
    let key := SSTableWorkload.benchKeyFor layout (2 * index + n)
    seek := seek.push ⟨key, (index + n).toUInt64⟩
    if n == 0 then
      hit := hit.push ⟨key, (index + 1).toUInt64⟩
    else
      miss := miss.push ⟨key, 0⟩
  return (hit, miss, seek)

private inductive Operation where
  | openTable | hit | miss | seek
  deriving BEq

private def Operation.name : Operation → String
  | .openTable => "open"
  | .hit => "hit"
  | .miss => "miss"
  | .seek => "seek"

private def runOperation (operation : Operation) (acquire : EIO String (Table (EIO String)))
    (queries : Array Probe) (rows : Nat) : EIO String Unit := do
  if operation == .openTable then
    let table ← acquire
    unless table.rowCount == rows do throw "wrong checked row count"
  else
    for query in queries do
      let table ← acquire
      let observed ← if operation == .seek then
          (·.toUInt64) <$> table.seek query.key
        else
          (fun value => value.elim 0 (Alvoki.word · 0)) <$> table.lookup query.key
      unless observed == query.expected do throw "benchmark probe differs from oracle"

private def replay (recursive : Bool) (layout : Unified.Layout) (file : Source (EIO String))
    (pages : Std.HashMap Nat IndexPage) (offsets : Array Nat) : IO (Nat × Nat × Nat) := do
  let mut wire : Std.HashMap Nat (IndexPage × ByteArray) := {}
  let mut trace : Array (IndexPage × ByteArray) := #[]
  let mut nbytes := 0
  for offset in offsets do
    let pair ← match wire[offset]? with
      | some cached => pure cached
      | none =>
        let some page := pages[offset]? | throw (IO.userError "missing index in decoder replay")
        let bytes ← checked (file.readAt page.ref.offset page.ref.size)
        pure (page, bytes)
    wire := wire.insert offset pair
    trace := trace.push pair
    nbytes := nbytes + pair.2.size
  let start ← IO.monoNanosNow
  for (page, bytes) in trace do
    match readRefs recursive layout page bytes with
    | .ok refs => unless !refs.isEmpty do throw (IO.userError "empty decoded index")
    | .error error => throw (IO.userError error)
  return (trace.size, nbytes, (← IO.monoNanosNow) - start)

private structure Case where
  recursive : Bool
  label : String
  layout : Unified.Layout
  rows : Nat
  dataTarget : Nat
  indexTarget : Nat
  bytes : Nat
  inv : Inventory

private def Case.report (config : Case) (mode operation : String) (budget used trial items : Nat)
    (elapsed : Option Nat) (trace : Trace := {}) (decode : Nat × Nat × Nat := (0, 0, 0)) :
    IO Unit := do
  let fields := [format config.recursive, config.label, toString config.rows, toString config.dataTarget,
    toString config.indexTarget, toString config.inv.root.height, toString config.inv.root.ref.size,
    toString config.bytes, toString config.inv.lower.size, toString config.inv.blocks, mode, operation,
    toString budget, toString used, toString trial, toString items, elapsed.elim "" toString,
    toString trace.sizeCalls, toString trace.footerCalls, toString trace.footerBytes,
    toString trace.indexReads, toString trace.indexReadBytes, toString trace.indexHits,
    toString trace.indexHitBytes, toString trace.dataCalls, toString trace.dataBytes,
    toString decode.1, toString decode.2.1, toString decode.2.2]
  IO.println (String.intercalate "," fields)

private def benchmarkMode (file : Source (EIO String)) (config : Case)
    (pages : Std.HashMap Nat IndexPage) (mode : String) (budget : Nat) (cache : WireCache)
    (keepRoot : Bool) : IO Unit := do
  let traceRef ← IO.mkRef ({} : Trace)
  let timedSource := if budget == 0 then file else cachedSource file cache
  let tracked := tracedSource file cache pages config.inv.footerAt traceRef
  let timedOpen := openTable config.recursive config.layout timedSource
  let trackedOpen := openTable config.recursive config.layout tracked
  let timedProbe ← if keepRoot then pure <$> checked timedOpen else pure timedOpen
  let trackedProbe ← if keepRoot then pure <$> checked trackedOpen else pure trackedOpen
  let (hits, misses, seeks) := probes config.layout config.rows
  for (op, queries) in [(Operation.openTable, #[]), (.hit, hits), (.miss, misses), (.seek, seeks)] do
    let items := if op == .openTable then 1 else queries.size
    let timed := runOperation op (if op == .openTable then timedOpen else timedProbe) queries config.rows
    let traced := runOperation op (if op == .openTable then trackedOpen else trackedProbe) queries config.rows
    traceRef.set {}
    checked traced
    let stats ← traceRef.get
    execute config op items timed stats
    if budget != 0 then
      -- A trace-only decoded-cache counterfactual. Its misses replay the real decoder.
      let misses := stats.indexOffsets.filter (fun offset => !cache.entries.contains offset)
      let replayResult ← replay config.recursive config.layout file pages misses
      config.report "resident-decoded-model" op.name budget cache.used 0 items none stats replayResult
where
  execute (config : Case) (op : Operation) (items : Nat) (timed : EIO String Unit) (stats : Trace) :
      IO Unit := do
    let replayResult ← replay config.recursive config.layout file pages stats.indexOffsets
    for trial in [:3] do
      let start ← IO.monoNanosNow
      checked timed
      let elapsed := (← IO.monoNanosNow) - start
      config.report mode op.name budget cache.used trial items (some elapsed) stats replayResult

private def run (rows dataTarget indexTarget budget : Nat) : IO Unit := IO.FS.withTempDir fun dir => do
  IO.println "format,layout,rows,data_target,index_target,height,root_bytes,file_bytes,nonroot_index_pages,data_blocks,mode,operation,budget,resident_bytes,trial,items,elapsed_ns,size_calls,footer_reads,footer_bytes,index_reads,index_read_bytes,index_hits,index_hit_bytes,data_reads,data_bytes,decode_packets,decode_bytes,decode_ns"
  for (label, keyWidth, valueWidth) in [
      ("fixed-fixed", some 8, some 8), ("fixed-variable", some 8, none),
      ("variable-fixed", none, some 8), ("variable-variable", none, none)] do
    let layout : Unified.Layout := ⟨keyWidth, valueWidth, 84⟩
    for recursive in (if rows % 2 == 0 then [true, false] else [false, true]) do
      let path := dir / s!"{label}-{format recursive}"
      let start ← IO.monoNanosNow
      let count ← SSTableWorkload.benchmarkBuild path layout rows dataTarget indexTarget recursive
      let elapsed := (← IO.monoNanosNow) - start
      unless count == rows do throw (IO.userError "wrong benchmark row count")
      let handle ← IO.FS.Handle.mk path .read
      let file := handleSource handle
      let inv ← checked (inventory file layout recursive)
      let fileBytes ← checked file.size
      let config : Case := ⟨recursive, label, layout, rows, dataTarget, indexTarget, fileBytes, inv⟩
      let pages := inv.pages
      let catalog := pages.foldl (fun (m : Std.HashMap Nat IndexPage) page =>
        m.insert page.ref.offset page) {}
      config.report "file" "build" 0 0 0 rows (some elapsed)
      benchmarkMode file config catalog "no-index-cache" 0 {} false
      benchmarkMode file config catalog "default" 0 {} true
      let startFill ← IO.monoNanosNow
      let cache ← checked (fillCache file pages budget)
      let fillTime := (← IO.monoNanosNow) - startFill
      config.report "resident-wire" "populate" budget cache.used 0 cache.entries.size (some fillTime)
        { indexReads := cache.entries.size, indexReadBytes := cache.used }
      benchmarkMode file config catalog "resident-wire" budget cache false
      IO.FS.removeFile path

end SSTableIndexCacheBench

def main (args : List String) : IO Unit := do
  let [rowArg, dataArg, indexArg, budgetArg] := args
    | throw (IO.userError "usage: sstableIndexCacheBench ROWS DATA_TARGET INDEX_TARGET METADATA_BUDGET")
  let some rows := rowArg.toNat? | throw (IO.userError "expected a row count")
  let some data := dataArg.toNat? | throw (IO.userError "expected a data target")
  let some index := indexArg.toNat? | throw (IO.userError "expected an index target")
  let some budget := budgetArg.toNat? | throw (IO.userError "expected a byte budget")
  unless rows > 0 && budget > 0 do throw (IO.userError "expected positive rows and budget")
  SSTableIndexCacheBench.run rows data index budget
