import Alvoki.Experiments.SSTable.Recursive.Native
import Alvoki.Experiments.SSTable.Recursive.ReadSafety
import Alvoki.Experiments.SortedRun.Proofs

open ImmutableSSTable ImmutableSSTable.Recursive

namespace BlockIteratorBenchmark

abbrev ExactCursor (source : Source (ReadM world)) (image : ByteArray) (rows : List Entry) :=
  { cursor : BlockCursor (ReadM world) //
    ∃ reference, cursor.SameImage reference source image ∧ reference.Observes image rows }

def exactPull (h : ImageReads (fun _ : world => True) source image) :
    SortedRun.Pull (ReadM world) (ExactCursor source image rows) Entry := fun cursor start =>
  match ran : cursor.val.pull start with
  | .error error reached => .error error reached
  | .ok none reached => .ok none reached
  | .ok (some (row, next)) reached =>
    .ok (some (row, ⟨next, by
      obtain ⟨reference, same, observed⟩ := cursor.property
      have step := BlockCursor.pull_framed h same observed start trivial
      rw [ran] at step
      obtain ⟨_, afterRef, afterSame, afterObs, _, _⟩ := step
      exact ⟨afterRef, afterSame, afterObs⟩⟩)) reached

theorem exactPull_contract (h : ImageReads (fun _ : world => True) source image) :
    (exactPull h (rows := rows)).Exact (fun cursor => rows.drop cursor.val.index) := by
  intro cursor start item reached ok
  obtain ⟨reference, same, observed⟩ := cursor.property
  have step := BlockCursor.pull_framed h same observed start trivial
  unfold exactPull at ok
  split at ok
  · contradiction
  · rename_i ran
    cases ok
    rw [ran] at step
    exact step.2.symm
  · rename_i row next _ ran
    cases ok
    rw [ran] at step
    obtain ⟨_, _, _, _, _, suffix⟩ := step
    exact suffix.symm

private structure Counters where
  calls : Nat := 0
  bytes : Nat := 0

private def ok (action : EIO String α) : IO α :=
  action.adapt IO.userError

private def openCounted (path : System.FilePath) (tableId : UInt64)
    (counters : IO.Ref Counters) : IO (Handle (EIO String)) := ok do
  let held ← nativeReadPrimitives.openFile path .read
  let source := nativeReadPrimitives.source held
  openChecked { source with readAt := fun offset count => do
    counters.modify fun stats => ⟨stats.calls + 1, stats.bytes + count⟩
    source.readAt offset count } Alvoki.CRC32C.extend tableId

private def input (i value marker : Nat) : Entry :=
  ⟨⟨#[(i / 16777216).toUInt8, (i / 65536).toUInt8, (i / 256).toUInt8, i.toUInt8]⟩,
    ⟨Array.replicate value marker.toUInt8⟩⟩

private def fixture (path : System.FilePath) (layout : Unified.Layout)
    (rows stride offset value : Nat) (options : BuildOptions) : IO Unit := do
  let index ← IO.mkRef 0
  let _ ← buildFileSynced path layout (index.modifyGet fun i =>
    if i < rows then (some (input (i * stride + offset) value offset), i + 1) else (none, i)) options

private def scan (pull : SortedRun.Pull (EIO String) α Entry) (initial : α) : IO Nat := do
  let mut cursor := initial
  let mut seen := 0
  let mut checksum := 0
  repeat
    match ← ok (pull cursor) with
    | none => break
    | some (row, next) =>
      seen := seen + 1
      checksum := checksum + row.key.size + row.value.size
      cursor := next
  return seen + checksum

private def merge (left : SortedRun.Pull (EIO String) α Entry)
    (right : SortedRun.Pull (EIO String) β Entry) (initialL : α) (initialR : β)
    (path : System.FilePath) (layout : Unified.Layout) (options : BuildOptions) : IO Nat := do
  let front ← IO.mkRef (SortedRun.Frontier.start initialL initialR)
  let slot : SortedRun.Slot (EIO String) _ := ⟨front.get, front.set⟩
  buildFileSynced path layout (ok (SortedRun.next Entry.key left right slot)) options

private def measure (counters : IO.Ref Counters) (mode : String) (trial : Nat)
    (height rows : Nat) (action : IO Nat) : IO Nat := do
  counters.set {}
  let started ← IO.monoNanosNow
  let before ← IO.getNumHeartbeats
  let checksum ← action
  let allocations := (← IO.getNumHeartbeats) - before
  let nanos := (← IO.monoNanosNow) - started
  let stats ← counters.get
  IO.println s!"{mode},{trial},{height},{rows},{nanos},{stats.calls},{stats.bytes},{allocations},{checksum}"
  return checksum

def run (rows : Nat) : IO Unit := IO.FS.withTempDir fun dir => do
  IO.println "mode,trial,height,input_rows,nanos,reads,requested_bytes,small_allocations,checksum"
  let crc := Alvoki.CRC32C.extend
  for (name, options) in [("default", ({} : BuildOptions)), ("recursive", ⟨4096, 256⟩)] do
    let layout : Unified.Layout := ⟨some 4, some 40, 900⟩
    let path := dir / s!"even-{name}"
    let other := dir / s!"odd-{name}"
    fixture path layout rows 2 0 40 options
    fixture other layout rows 3 1 40 options
    let counters ← IO.mkRef ({} : Counters)
    let a ← openCounted path layout.tableId counters
    let b ← openCounted other layout.tableId counters
    for trial in [:3] do
      let rowScan := measure counters s!"{name}-scan-row" trial a.height rows (scan a.next 0)
      let blockScan := measure counters s!"{name}-scan-block" trial a.height rows
        (scan BlockCursor.pull (a.cursorAt 0))
      let mut rowDigest := 0
      let mut blockDigest := 0
      if trial % 2 == 0 then
        rowDigest ← rowScan
        blockDigest ← blockScan
      else
        blockDigest ← blockScan
        rowDigest ← rowScan
      unless rowDigest == blockDigest && rowDigest == rows * 45 do
        throw (IO.userError "streamed scan mismatch")
      let baseline := measure counters s!"{name}-merge-row" trial a.height (2 * rows)
        (merge a.next b.next 0 0 (dir / s!"out-{name}-row-{trial}") layout options)
      let iterator := measure counters s!"{name}-merge-block" trial a.height (2 * rows)
        (merge BlockCursor.pull BlockCursor.pull (a.cursorAt 0) (b.cursorAt 0)
          (dir / s!"out-{name}-block-{trial}") layout options)
      let mut rowCount := 0
      let mut blockCount := 0
      if trial % 2 == 0 then
        rowCount ← baseline
        blockCount ← iterator
      else
        blockCount ← iterator
        rowCount ← baseline
      unless rowCount == blockCount do throw (IO.userError "merge counts differ")
      let producedA ← IO.FS.readBinFile (dir / s!"out-{name}-row-{trial}")
      let producedB ← IO.FS.readBinFile (dir / s!"out-{name}-block-{trial}")
      unless producedA == producedB do throw (IO.userError "merged files differ")
      let _ ← ok (openCheckedWith nativeReadPrimitives crc (dir / s!"out-{name}-block-{trial}")
        layout.tableId)

end BlockIteratorBenchmark

def main (args : List String) : IO Unit :=
  BlockIteratorBenchmark.run (args.head?.bind String.toNat? |>.getD 50000)
