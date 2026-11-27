import Alvoki.Experiments.WAL.Recovery

namespace WalRecoverySlice

inductive Fault where | none | crashBefore | eioBefore | eioAfter | tear | tornCacheFullDisk deriving BEq, Repr
structure Sim where
  visible : Bytes := []
  durable : Bytes := []
  marker0 : Bytes := encodeMarker 0 0
  marker1 : Bytes := []
  durableMarker0 : Bytes := encodeMarker 0 0
  durableMarker1 : Bytes := []
  markerReadError : Option Nat := none
  faults : List Fault := []
  readError : Bool := false
  deriving Repr
abbrev M := ExceptT String (EStateM Unit Sim)

def stop : M α := liftM (show EStateM Unit Sim α from throw ())

def step (effect : Sim → Sim) : M Unit := do
  let s ← get
  let f := s.faults.headD .none
  set {s with faults := s.faults.drop 1}
  if f == .crashBefore then stop
  if f == .eioBefore then throw "eio"
  modify effect
  if f == .eioAfter then throw "eio"

def simOps : Ops M where
  append b := do
    if (← get).faults.headD .none == .tear then
      let partialBytes := b.take 12 ++ List.replicate (b.length - 12) 0
      modify fun s => {s with faults := s.faults.drop 1, visible := s.visible ++ partialBytes,
                              durable := s.durable ++ partialBytes}
      stop
    step fun s => {s with visible := s.visible ++ b}
  syncData := step fun s => {s with durable := s.visible}
  writeMarker slot bytes := do
    if (← get).faults.headD .none == .tornCacheFullDisk then
      let s ← get
      set (if slot == 0 then {s with faults := s.faults.drop 1, marker0 := [], durableMarker0 := bytes}
        else {s with faults := s.faults.drop 1, marker1 := [], durableMarker1 := bytes})
      stop
    if (← get).faults.headD .none == .tear then
      let s ← get
      let previous := if slot == 0 then s.marker0 else s.marker1
      let tornMarker := bytes.take 4 ++ previous.drop 4
      set (if slot == 0 then {s with faults := s.faults.drop 1, marker0 := tornMarker, durableMarker0 := tornMarker}
        else {s with faults := s.faults.drop 1, marker1 := tornMarker, durableMarker1 := tornMarker})
      stop
    step fun s => if slot == 0 then {s with marker0 := bytes} else {s with marker1 := bytes}
  syncMarker slot := step fun s => if slot == 0 then {s with durableMarker0 := s.marker0}
    else {s with durableMarker1 := s.marker1}
  readData := do
    let s ← get
    if s.readError then throw "read eio"
    return s.visible
  readMarker slot := do
    let s ← get
    if s.markerReadError == some slot then throw "marker read eio"
    return if slot == 0 then s.marker0 else s.marker1
  truncate n := step fun s => {s with visible := s.visible.take n}

def run (m : M α) (s : Sim) : Except String α × Sim :=
  match (m.run).run s with
  | .ok r state => (r, state)
  | .error _ state => (.error "crash", state)

def powerLoss (s : Sim) : Sim := {s with visible := s.durable, marker0 := s.durableMarker0, marker1 := s.durableMarker1, faults := [], readError := false, markerReadError := none}
def processExit (s : Sim) : Sim := {s with faults := [], readError := false}

def require (b : Bool) (msg : String) : IO Unit := unless b do throw <| IO.userError msg

def expectOpen (policy : Policy) (s : Sim) (expected : List Bytes) : IO (Cursor × Sim) := do
  let (r, s) := run (reopen simOps policy) s
  match r with
  | .error e => throw <| IO.userError s!"unexpected open failure: {e}"
  | .ok d =>
    require (d.batches == expected) s!"history mismatch: {repr d.batches}"
    return (d.cursor, s)

def checkPolicy (policy : Policy) : IO Unit := do
  let a := [10, 11]
  let b := [20, 21, 22]
  let c := [30]
  let (ra, s) := run (appendBatch simOps policy {} a) {}
  let .ok afterA := ra | throw <| IO.userError "A failed"
  -- B's full declared extent is durable, but its payload is torn before sync.
  let (stopped, tornImage) := run (appendBatch simOps policy afterA b) {s with faults := [.tear]}
  match stopped with
  | .error "crash" => pure ()
  | _ => throw <| IO.userError "torn append must stop"
  let (_, recovered) ← expectOpen policy (powerLoss tornImage) [a]
  let (cursor, recovered) ← expectOpen policy (powerLoss recovered) [a]
  let (rc, afterC) := run (appendBatch simOps policy cursor c) recovered
  require rc.isOk "C failed"
  let _ ← expectOpen policy (powerLoss afterC) [a, c]
  -- A valid B visible in cache is retained only by log-only recovery.
  let (rb, dirty) := run (appendBatch simOps policy afterA b) {s with faults := [.none, .eioBefore]}
  require (!rb.isOk) "B must report error before sync"
  let expected := if policy == .logOnly then [a, b] else [a]
  let (_, recovered) ← expectOpen policy (processExit dirty) expected
  let (cursor, recovered) ← expectOpen policy (powerLoss recovered) expected
  let (rc, afterC) := run (appendBatch simOps policy cursor c) recovered
  require rc.isOk "C after process exit failed"
  let _ ← expectOpen policy (powerLoss afterC) (expected ++ [c])
  -- An error after an effective sync must preserve effects; no ACK was observed.
  let (rb, synced) := run (appendBatch simOps policy afterA b) {s with faults := [.none, .eioAfter]}
  require (!rb.isOk) "B must report error after sync"
  let _ ← expectOpen policy (powerLoss synced) (if policy == .logOnly then [a, b] else [a])
  let (readResult, _) := run (reopen simOps policy) {s with readError := true}
  require (!readResult.isOk) "read EIO must fail open"
  -- Recovery interrupted before the repair sync can be retried after reboot.
  let (repairResult, interrupted) := run (reopen simOps policy) {tornImage with faults := (if policy == .boundary then [.none, .none] else []) ++ [.none, .crashBefore]}
  require (repairResult matches .error "crash") "repair should stop before its sync"
  let _ ← expectOpen policy (powerLoss interrupted) [a]
  if policy == .boundary then
    -- The process stops after the marker write. Open must settle B before exposing it.
    let (stoppedAtWrite, written) := run (appendBatch simOps policy afterA b)
      {s with faults := [.none, .none, .none, .crashBefore]}
    require (stoppedAtWrite matches .error "crash") "expected interrupted marker sync"
    let _ ← expectOpen policy (powerLoss written) [a]
    let (_, adopted) ← expectOpen policy (processExit written) [a, b]
    let _ ← expectOpen policy (powerLoss adopted) [a, b]
    for fault in [Fault.eioBefore, .eioAfter] do
      let (submitted, reached) := run (appendBatch simOps policy afterA b)
        {s with faults := [.none, .none, .none, fault]}
      require (!submitted.isOk) "publication error acknowledged B"
      let history := if fault == .eioAfter then [a, b] else [a]
      let _ ← expectOpen policy (powerLoss reached) history
    -- The uncertain write left B's full marker durable but unreadable in cache.
    -- Adopting A on process restart must retire that durable marker before truncating B.
    let (uncertain, mixed) := run (appendBatch simOps policy afterA b)
      {s with faults := [.none, .none, .tornCacheFullDisk]}
    require (uncertain matches .error "crash") "expected interrupted marker write"
    let _ ← expectOpen policy (powerLoss mixed) [a, b]
    let (_, repaired) ← expectOpen policy (processExit mixed) [a]
    let _ ← expectOpen policy (powerLoss repaired) [a]
    for fault in [Fault.eioBefore, .eioAfter] do
      let (failure, atFailure) := run (reopen simOps policy)
        {(processExit mixed) with faults := [.none, fault]}
      require (!failure.isOk) "sibling barrier error must stop recovery"
      require (atFailure.visible == mixed.visible) "repair truncated before both barriers succeeded"
      let _ ← expectOpen policy (powerLoss atFailure) (if fault == .eioAfter then [a] else [a, b])
    -- B tears while overwriting the inactive slot; A's slot remains intact.
    let (tornResult, tornSlot) := run (appendBatch simOps policy afterA b)
      {s with faults := [.none, .none, .tear]}
    require (tornResult matches .error "crash") "marker tear must stop"
    let (cursor, recovered) ← expectOpen policy (powerLoss tornSlot) [a]
    let (rc, afterC) := run (appendBatch simOps policy cursor c) recovered
    require rc.isOk "C after torn marker failed"
    let _ ← expectOpen policy (powerLoss afterC) [a, c]
    for slot in [0, 1] do
      let (result, _) := run (reopen simOps policy) {s with markerReadError := some slot}
      require (!result.isOk) "either marker read EIO must fail"
    let (misplaced, _) := run (reopen simOps policy) {s with marker0 := encodeMarker 1 1}
    require (!misplaced.isOk) "checksum-valid wrong-slot marker must fail"
    let (missing, _) := run (reopen simOps policy) {s with marker0 := [], marker1 := []}
    require (!missing.isOk) "missing marker must fail"
    let (rb, committed) := run (appendBatch simOps policy afterA b) s
    require rb.isOk "B should be acknowledged"
    let damage := committed.durable.modify (committed.durable.length - 1) (fun byte => byte ^^^ 1)
    let damaged := {committed with visible := damage, durable := damage}
    let (result, _) := run (reopen simOps policy) (powerLoss damaged)
    require (!result.isOk) "published damaged B must fail"

/-- Pin the v3 encoding and corrupt each stored byte in turn. -/
private def checkWireFormat : IO Unit := do
  let expectedFrame : Bytes := [42, 1, 1, 1, 215, 106, 120, 20, 181, 42, 29, 193,
    0, 106, 119, 2, 69, 192, 189, 77, 176]
  let expectedMarker : Bytes := [77, 2, 1, 1, 1, 35, 168, 85, 170, 16, 12, 173, 192, 97]
  require (frame 1 [0] == expectedFrame) "v3 frame wire vector changed"
  require (encodeMarker 291 1 == expectedMarker) "v3 marker wire vector changed"
  require ((scan expectedFrame expectedFrame.length .boundary) matches .ok _) "valid frame rejected"
  require ((decodeMarker 1 expectedMarker) matches .ok (some _)) "valid marker rejected"
  for i in [:expectedFrame.length] do
    let damaged := expectedFrame.modify i (fun byte => byte ^^^ 1)
    require ((scan damaged damaged.length .boundary) matches .error _) s!"accepted damaged frame byte {i}"
  for i in [:expectedMarker.length] do
    let damaged := expectedMarker.modify i (fun byte => byte ^^^ 1)
    require ((decodeMarker 1 damaged) matches .ok none) s!"accepted damaged marker byte {i}"
  -- The old modulo-251 checksum gave these one-byte payloads the same trailer.
  let collision := expectedFrame.set 12 251
  require ((scan collision collision.length .boundary) matches .error "damaged batch")
    "accepted changed payload with the old checksum collision"

def main : IO Unit := do
  checkWireFormat
  checkPolicy .logOnly
  checkPolicy .boundary
  -- A byte-perfect prefix has no internal indication that the last frame was lost.
  -- The intact marker for B supplies the larger expected extent.
  let a := frame 1 [10]
  let ab := a ++ frame 2 [20]
  let shortened : Sim := {
    visible := a, durable := a
    marker0 := encodeMarker ab.length 2, marker1 := encodeMarker a.length 1 }
  let _ ← expectOpen .logOnly shortened [[10]]
  let (withMarker, after) := run (reopen simOps .boundary) shortened
  require (withMarker matches .error "missing bytes") "accepted deletion of acknowledged B under intact marker"
  require (after.visible == a) "failed recovery changed the surviving prefix"
  -- A deliberately early ACK loses the supposedly acknowledged batch on reboot.
  let (_, bad) := run (simOps.append (frame 1 [9])) {}
  let (result, _) := run (reopen simOps .logOnly) (powerLoss bad)
  match result with
  | .ok d => require (d.batches != [[9]]) "oracle failed to catch early ACK"
  | .error e => throw <| IO.userError e
  IO.println "WAL recovery slice: all checks passed"
end WalRecoverySlice

def main : IO Unit := WalRecoverySlice.main
