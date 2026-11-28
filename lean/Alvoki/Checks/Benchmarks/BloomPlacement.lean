import Alvoki.Checks.Benchmarks.BloomWord
import Alvoki.Experiments.SSTable.Recursive.FilteredReader

namespace ImmutableSSTable.BloomPlacement

open Unified (Layout Ref findRef)

private abbrev RHandle := Recursive.Handle (EIO String)

private def crc := Alvoki.CRC32C.extend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def run (action : EIO String α) : IO α :=
  action.adapt IO.userError

private def key (layout : Layout) (n : Nat) : ByteArray :=
  let bytes : ByteArray :=
    ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
      (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩
  if layout.keyWidth.isSome then bytes
  else bytes ++ ⟨Array.replicate ((n / 2) % 8) 0x42⟩

private def value (layout : Layout) (n : Nat) : ByteArray :=
  -- Zero represents a tombstone for the fixture. Equality checks still require a hit.
  let body := encodeOffset (if n % 7 = 0 then 0 else n + 1)
  if layout.valueWidth.isSome then body
  else body ++ ⟨Array.replicate (n % 16) 0x56⟩

private def fixture (layout : Layout) (rows : Nat) : Array Entry :=
  (List.range rows).toArray.map fun i => ⟨key layout (2 * i), value layout i⟩

private def queries (layout : Layout) (rows : Nat) :
    List (String × Array (ByteArray × Option ByteArray)) := Id.run do
  let mut hits := #[]
  let mut misses := #[]
  let mut clusteredMisses := #[]
  let mut seed := 12345
  for probe in [:4096] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let i := (seed >>> 8) % (rows - 1)
    hits := hits.push (key layout (2 * i), some (value layout i))
    misses := misses.push (key layout (2 * i + 1), none)
    let partition := (probe / 64) % max 1 ((rows - 1) / 16384)
    let localRow := partition * 16384 + ((seed >>> 8) % min 16384 (rows - 1))
    clusteredMisses := clusteredMisses.push (key layout (2 * localRow + 1), none)
  return [("hit", hits), ("miss", misses), ("clustered-miss", clusteredMisses)]

private def makeTable (path : System.FilePath) (layout : Layout) (rows : Array Entry)
    (dataTarget indexTarget : Nat) (withFilter : Bool) : IO Nat := do
  let cursor ← IO.mkRef 0
  let next := do
    let i ← cursor.get
    cursor.set (i + 1)
    return rows[i]?
  let start ← IO.monoNanosNow
  let count ← Recursive.buildFileWith (nativeOutputOps (fun _ => pure ())) crc path layout next
    IO.userError { dataTarget, indexTarget, membershipFilter := withFilter }
  let elapsed := (← IO.monoNanosNow) - start
  check (count == rows.size) "table build did not consume the fixture"
  return elapsed

private structure Counts where
  calls : Nat := 0
  bytes : Nat := 0
  filterCalls : Nat := 0
  filterBytes : Nat := 0
  attachedBytes : Nat := 0
  decisions : Nat := 0
  positives : Nat := 0

private def countTable (source : Source (EIO String)) (counts : IO.Ref Counts) : Source (EIO String) where
  size := source.size
  readAt offset size := do
    counts.modify fun n => { n with calls := n.calls + 1, bytes := n.bytes + size }
    source.readAt offset size

private def countSidecar (source : Source (EIO String)) (counts : IO.Ref Counts) : Source (EIO String) where
  size := source.size
  readAt offset size := do
    counts.modify fun n =>
      { n with filterCalls := n.filterCalls + 1, filterBytes := n.filterBytes + size }
    source.readAt offset size

private structure Region where
  start : Nat
  count : Nat
  fence : ByteArray

private def region (rows : Array Entry) (start count : Nat) : Region :=
  ⟨start, count, (rows[start + count - 1]?.map Entry.key).getD .empty⟩

private def fixedRegions (rows : Array Entry) (target : Nat) : Array Region := Id.run do
  let mut result := #[]
  for block in [:(rows.size + target - 1) / target] do
    let start := block * target
    result := result.push (region rows start (min target (rows.size - start)))
  return result

private def leafRegions (handle : RHandle) (refs : Array Ref) (parent : Nat) :
    Nat → EIO String (Array (Nat × Region))
  | 0 => return #[]
  | 1 => return refs.map fun ref => (ref.offset, ⟨ref.firstRow, ref.count, ref.lastKey⟩)
  | height + 2 => do
    let mut leaves := #[]
    for ref in refs do
      let raw ← Recursive.readIndexPacket handle.source crc handle.layout.tableId (height + 2) ref parent
      let children ← liftDecode (Recursive.pageChildren raw ref true)
      leaves := leaves ++ (← leafRegions handle children ref.offset (height + 1))
    return leaves

private def noteFilter (counts : IO.Ref Counts) (mask : ByteArray) (query : ByteArray) :
    EIO String Bool := do
  let positive := Bloom.mayContain mask query
  counts.modify fun n => { n with
    decisions := n.decisions + 1
    positives := n.positives + (if positive then 1 else 0) }
  return positive

private def buildMask (rows : Array Entry) (range : Region) : IO (ByteArray × Nat) := do
  let slice := rows.extract range.start (range.start + range.count)
  check (slice.size == range.count && !slice.isEmpty && (slice.back?.map Entry.key) == some range.fence)
    "filter range does not match fixture"
  let start ← IO.monoNanosNow
  let mask := Bloom.build slice
  let result := mask.size
  let elapsed := (← IO.monoNanosNow) - start
  check (result == Bloom.bytesFor range.count) "wrong mask size"
  for row in slice do
    check (Bloom.mayContain mask row.key) "filter omitted an inserted key"
  return (mask, elapsed)

private structure MaskFile where
  refs : Array Ref
  bytes : Nat
  build : Nat

private def writeMasks (path : System.FilePath) (layout : Layout) (rows : Array Entry)
    (regions : Array Region) : IO MaskFile := do
  let file ← IO.FS.Handle.mk path .write
  let mut refs := #[]
  let mut offset := 0
  let mut elapsed := 0
  for range in regions do
    let (mask, duration) ← buildMask rows range
    let start ← IO.monoNanosNow
    let packet := Unified.encodePacket crc layout.tableId Recursive.filterKind offset mask
    file.write packet
    elapsed := elapsed + duration + ((← IO.monoNanosNow) - start)
    refs := refs.push ⟨range.fence, offset, packet.size, range.start, range.count⟩
    offset := offset + packet.size
  let start ← IO.monoNanosNow
  file.flush
  return ⟨refs, offset, elapsed + ((← IO.monoNanosNow) - start)⟩

private def loadMask (source : Source (EIO String)) (layout : Layout) (ref : Ref) (endAt : Nat) :
    EIO String ByteArray :=
  Unified.readPacket source crc layout.tableId Recursive.filterKind ref.offset ref.size endAt

private def withMasks (handle : RHandle) (maskFile : MaskFile)
    (load : Ref → EIO String ByteArray) (counts : IO.Ref Counts)
    (query : ByteArray) : EIO String (Option ByteArray) := do
  let before := fun ref : Ref => decide (ref.lastKey < query)
  let some _ := findRef handle.root before | return none
  let some ref := findRef maskFile.refs before | throw "filter directory does not cover query"
  if ← noteFilter counts (← load ref) query then handle.lookup query else return none

private def withLeafMasks (handle : RHandle) (masks : Std.HashMap Nat ByteArray)
    (counts : IO.Ref Counts) (query : ByteArray) : EIO String (Option ByteArray) := do
  let before := fun (ref : Ref) => decide (ref.lastKey < query)
  let some rootChild := findRef handle.root before | return none
  let mut ref := rootChild
  let mut parent := handle.rootOffset
  for height in (List.range (handle.height - 1)).reverse do
    let raw ← Recursive.readIndexPacket handle.source crc handle.layout.tableId (height + 1) ref parent
    let children ← liftDecode (Recursive.pageChildren raw ref true)
    if height = 0 then
      let some mask := masks[ref.offset]? | throw "missing leaf projection"
      unless ref.size + mask.size ≤ maxRowSize do throw "enlarged leaf does not fit one request"
      counts.modify fun n => { n with attachedBytes := n.attachedBytes + mask.size }
      unless ← noteFilter counts mask query do return none
    let some child := findRef children before | throw "invalid child range in leaf projection"
    parent := ref.offset
    ref := child
  if handle.height = 1 then
    let some mask := masks[handle.rootOffset]? | throw "missing root leaf projection"
    unless ← noteFilter counts mask query do return none
  handle.lookupInData ref parent query

private def probe (lookup : ByteArray → EIO String (Option ByteArray))
    (batch : Array (ByteArray × Option ByteArray)) : IO Unit :=
  run do
    for (query, expected) in batch do
      unless (← lookup query) == expected do
        throw "lookup did not match the fixture"

private structure Case where
  rows : Nat
  layout : String
  dataTarget : Nat
  indexTarget : Nat
  height : Nat

private def output (configuration : Case) (label workload : String) (items : Nat)
    (counts : Counts) (metadata retained build : Nat := 0) : IO Unit := do
  let row := [
    toString configuration.rows, configuration.layout, toString configuration.dataTarget,
    toString configuration.indexTarget, toString configuration.height, label, workload, toString items,
    toString counts.calls, toString counts.bytes, toString counts.filterCalls, toString counts.filterBytes,
    toString counts.attachedBytes, toString counts.decisions, toString counts.positives,
    toString metadata, toString retained, toString build]
  IO.println (String.intercalate "," row)

private def benchmark (configuration : Case) (label : String) (counts : IO.Ref Counts)
    (prepare : IO (ByteArray → EIO String (Option ByteArray)))
    (batches : List (String × Array (ByteArray × Option ByteArray)))
    (metadata retained build : Nat := 0) : IO Unit := do
  for (name, batch) in batches do
    counts.set {}
    let lookup ← prepare
    output configuration label s!"open-{name}" 1 (← counts.get) metadata retained build
    counts.set {}
    probe lookup batch
    output configuration label name batch.size (← counts.get)

private def place (layout : Layout) (name : String)
    (rows : Array Entry) (targets : Nat × Nat) : IO Unit := IO.FS.withTempDir fun dir => do
  let plain := dir / "plain"
  let filtered := dir / "filtered"
  let plainTime ← makeTable plain layout rows targets.1 targets.2 false
  let filteredTime ← makeTable filtered layout rows targets.1 targets.2 true
  let plainSource := handleSource (← IO.FS.Handle.mk plain .read)
  let filteredSource := handleSource (← IO.FS.Handle.mk filtered .read)
  let filteredSize ← run filteredSource.size
  let plainSize ← run plainSource.size
  let original ← run (Recursive.openChecked plainSource crc layout.tableId)
  let config : Case := ⟨rows.size, name, targets.1, targets.2, original.height⟩
  let batches := queries layout rows.size
  let counts ← IO.mkRef ({} : Counts)
  benchmark config "unfiltered" counts (do
    let handle ← run (Recursive.openChecked (countTable plainSource counts) crc layout.tableId)
    return handle.lookup) batches 0 0 plainTime
  benchmark config "block-on-disk" counts (do
    let handle ← run (Recursive.openChecked (countTable filteredSource counts) crc layout.tableId)
    return handle.filteredLookup) batches (filteredSize - plainSize) 0 filteredTime
  let leaves ← if original.height = 1 then
      pure #[(original.rootOffset, region rows 0 rows.size)]
    else run (leafRegions original original.root original.rootOffset (original.height - 1))
  let mut masks : Std.HashMap Nat ByteArray := {}
  let mut maskBuild := 0
  let mut addedBytes := 0
  for (offset, range) in leaves do
    let (mask, elapsed) ← buildMask rows range
    maskBuild := maskBuild + elapsed
    addedBytes := addedBytes + mask.size
    masks := masks.insert offset mask
  let rootMaskBytes := if original.height = 1 then addedBytes else 0
  if original.height == 1 then
    check ((Unified.encodeIndex original.root).size + Unified.checksumSize + rootMaskBytes ≤ maxRowSize)
      "enlarged root leaf does not fit one request"
  benchmark config "leaf-attached" counts (do
    let handle ← run (Recursive.openChecked (countTable plainSource counts) crc layout.tableId)
    counts.modify fun n => { n with attachedBytes := rootMaskBytes }
    return withLeafMasks handle masks counts) batches addedBytes rootMaskBytes maskBuild
  for (label, ranges) in [("coarse", fixedRegions rows 16384), ("table", #[region rows 0 rows.size])] do
    let masksPath := dir / s!"{label}-masks"
    let maskFile ← writeMasks masksPath layout rows ranges
    let source := handleSource (← IO.FS.Handle.mk masksPath .read)
    let corrupted : Source (EIO String) := { source with
      readAt := fun offset size => do
        let bytes ← source.readAt offset size
        return bytes.set! 0 (bytes[0]! ^^^ 1) }
    let firstKey := key layout 0
    match ← (withMasks original maskFile
        (fun ref => loadMask corrupted layout ref maskFile.bytes) counts firstKey).toBaseIO with
    | .ok _ => throw (IO.userError "corrupt mask reached the lookup result")
    | .error message => check (message == "SSTable CRC32C mismatch") message
    let unreadable : Source (EIO String) := { source with
      readAt := fun _ _ => throw "injected mask read failure" }
    match ← (withMasks original maskFile
        (fun ref => loadMask unreadable layout ref maskFile.bytes) counts firstKey).toBaseIO with
    | .ok _ => throw (IO.userError "mask read failure reached the lookup result")
    | .error message => check (message == "injected mask read failure") message
    let sideSource := countSidecar source counts
    let modes := if label == "table" then ["table-cached"]
      else ["coarse-on-disk", "coarse-last", "coarse-cached"]
    let bytes := maskFile.bytes + (Unified.encodeIndex maskFile.refs).size
    for placement in modes do
      let preloaded := placement == "table-cached" || placement == "coarse-cached"
      benchmark config placement counts (do
        let handle ← run (Recursive.openChecked (countTable plainSource counts) crc layout.tableId)
        let load := fun ref => loadMask sideSource layout ref maskFile.bytes
        if preloaded then
          let mut cache : Std.HashMap Nat ByteArray := {}
          for ref in maskFile.refs do
            cache := cache.insert ref.offset (← run (load ref))
          return withMasks handle maskFile (fun ref => do
            let some mask := cache[ref.offset]? | throw "missing checked mask"
            return mask) counts
        else if placement == "coarse-last" then
          let cached ← IO.mkRef (none : Option (Nat × ByteArray))
          return withMasks handle maskFile (fun ref => do
            if let some (offset, mask) ← cached.get then
              if offset == ref.offset then return mask
            let mask ← load ref
            cached.set (some (ref.offset, mask))
            return mask) counts
        else
          return withMasks handle maskFile load counts) batches bytes
        (if preloaded then maskFile.bytes - 4 * maskFile.refs.size
          else if placement == "coarse-last" then maskFile.refs.foldl (fun peak ref => max peak (ref.size - 4)) 0
          else 0) maskFile.build

private def placements (rows : Nat) : IO Unit := do
  IO.println "rows,layout,data_target,index_target,index_height,placement,operation,items,table_reads,table_bytes,sidecar_reads,sidecar_bytes,attached_bytes,filter_tests,filter_positives,metadata_bytes,retained_mask_bytes,build_ns"
  for (name, layout) in [("fixed-fixed", (⟨some 8, some 8, 84⟩ : Layout)),
      ("variable-variable", (⟨none, none, 84⟩ : Layout))] do
    let entries := fixture layout rows
    for targets in [(4096, 1024), (16384, 16384)] do
      place layout name entries targets

private def foldPlans (plans : Array (List Nat)) (bytes : Nat) : ByteArray :=
  plans.foldl (fun mask probes => probes.foldl Bloom.setBit mask) (blank bytes)

private def profileTrial (name phase : String) (regionSize trial keys rounds : Nat)
    (input : α) (sample : α → UInt64) (expected : UInt64) : IO Unit := do
  -- Fetch through an effect each round so the repeated pure operation stays inside the timer.
  let source ← IO.mkRef input
  let start ← IO.monoNanosNow
  let mut checksum : UInt64 := 0
  for _ in [:rounds] do
    checksum := checksum + sample (← source.get)
  let elapsed := (← IO.monoNanosNow) - start
  check (checksum == rounds.toUInt64 * expected) s!"profile checksum mismatch for {phase}"
  IO.println s!"{name},{regionSize},{phase},{keys},{rounds},{trial},{elapsed},{checksum}"

private def hashChecksum (keyHash : ByteArray → UInt64) (rows : Array Entry) : UInt64 :=
  rows.foldl (fun acc row => acc + keyHash row.key) 0

private def probeChecksum (position : Nat → ByteArray → List Nat)
    (regions : Array (Array Entry)) : UInt64 :=
  regions.foldl (fun total rows =>
    rows.foldl (fun acc row =>
      (position (Bloom.bytesFor rows.size) row.key).foldl (fun sum probe => sum + probe.toUInt64) acc)
      total) 0

private def maskChecksum (acc : UInt64) (mask : ByteArray) : UInt64 :=
  acc + (crc 0 mask).toUInt64

private def profileCase (name : String) (rows : Array Entry) (regionSize rounds : Nat) : IO Unit := do
  let regions := (fixedRegions rows regionSize).map fun range =>
    rows.extract range.start (range.start + range.count)
  let mut plans := #[]
  for part in regions do
    let bytes := Bloom.bytesFor part.size
    let expected := Bloom.build part
    let planned := part.map fun row => Bloom.positions bytes row.key
    check (foldPlans planned bytes == expected) "precomputed positions changed the mask"
    check (packedWordBuild part == expected) "packed-word build changed the mask"
    for row in part do
      check (copiedHash row.key == packedHash row.key) "packed fold changed the hash"
      check (Bloom.positions bytes row.key == wordPositions copiedHash bytes row.key)
        "word modulo changed the positions"
    plans := plans.push (planned, bytes)
  let hash := hashChecksum copiedHash rows
  let positions := probeChecksum Bloom.positions regions
  let mask := regions.foldl (fun total part => maskChecksum total (Bloom.build part)) 0
  for trial in [:3] do
    profileTrial name "hash-copy" regionSize trial rows.size rounds
      rows (hashChecksum copiedHash) hash
    profileTrial name "hash-packed" regionSize trial rows.size rounds
      rows (hashChecksum packedHash) hash
    profileTrial name "positions-nat" regionSize trial rows.size rounds
      regions (probeChecksum Bloom.positions) positions
    profileTrial name "positions-word" regionSize trial rows.size rounds
      regions (probeChecksum (wordPositions copiedHash)) positions
    profileTrial name "planned-bitset" regionSize trial rows.size rounds
      plans (fun input => input.foldl (fun total (plan, bytes) => maskChecksum total (foldPlans plan bytes)) 0)
      mask
    profileTrial name "build-current" regionSize trial rows.size rounds
      regions (fun input => input.foldl (fun total part => maskChecksum total (Bloom.build part)) 0) mask
    profileTrial name "build-packed-word" regionSize trial rows.size rounds
      regions (fun input => input.foldl (fun total part => maskChecksum total (packedWordBuild part)) 0) mask

private def profile (rounds : Nat) : IO Unit := do
  IO.println "layout,region_rows,phase,keys,rounds,trial,elapsed_ns,checksum"
  for (name, layout) in [("fixed-fixed", (⟨some 8, some 8, 84⟩ : Layout)),
      ("variable-variable", (⟨none, none, 84⟩ : Layout))] do
    let rows := fixture layout 65536
    for regionSize in [128, 16384] do
      profileCase name rows regionSize rounds

def benchmarkMain : List String → IO Unit
  | ["--placements", size] => do
    let some rows := size.toNat? | throw (IO.userError "expected a row count")
    unless 1 < rows && rows ≤ 8 * 1024 * 1024 do
      throw (IO.userError "row count outside the benchmark limits")
    placements rows
  | ["--profile", count] => do
    let some rounds := count.toNat? | throw (IO.userError "expected a round count")
    unless 0 < rounds do throw (IO.userError "expected at least one round")
    profile rounds
  | _ => throw (IO.userError "usage: bloomPlacementCheck [--placements ROWS | --profile ROUNDS]")

end ImmutableSSTable.BloomPlacement

def main := ImmutableSSTable.BloomPlacement.benchmarkMain
