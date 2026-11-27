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
      let partialBytes := b.take 13 ++ List.replicate (b.length - 13) 0
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

/-- The oracle tracks the exact history established by ACKs and successful
opens, plus at most one submitted batch with an unknown result. -/
private structure ClientHistory where
  known : List Bytes := []
  pending : Option Bytes := none

private def ClientHistory.submit (c : ClientHistory) (batch : Bytes) : ClientHistory :=
  {c with pending := some batch}

private def ClientHistory.ack (c : ClientHistory) : ClientHistory :=
  match c.pending with
  | none => c
  | some batch => {known := c.known ++ [batch], pending := none}

private def ClientHistory.allows (c : ClientHistory) (history : List Bytes) : Bool :=
  history == c.known || match c.pending with
    | none => false
    | some batch => history == c.known ++ [batch]

private def oracleOpen (policy : Policy) (s : Sim) (client : ClientHistory) : IO (Decoded × Sim × ClientHistory) := do
  let (result, reached) := run (reopen simOps policy) s
  match result with
  | .error e => throw <| IO.userError s!"oracle open failed: {e}"
  | .ok decoded =>
    require (client.allows decoded.batches) s!"oracle rejected history {repr decoded.batches}"
    return (decoded, reached, {known := decoded.batches, pending := none})

/-- Background writeback is not a caller barrier. It can make the reached
volatile bytes durable at a primitive cut without returning an ACK. -/
private def writebackData (s : Sim) : Sim := {s with durable := s.visible}

private def checkAdversarial (policy : Policy) : IO Unit := do
  let a : Bytes := [11, 12]
  let b : Bytes := [21, 22, 23]
  let c : Bytes := [31]
  let alternate : Bytes := [81, 82, 83]
  let initial : ClientHistory := {}
  let submittedA := initial.submit a
  let (ackA, stateA) := run (appendBatch simOps policy {} a) {}
  let .ok cursorA := ackA | throw <| IO.userError "A was not acknowledged"
  let clientA := submittedA.ack
  let clientB := clientA.submit b
  -- Same-block, full-length tear happens inside B's append, before its data sync.
  let (stopped, torn) := run (appendBatch simOps policy cursorA b) {stateA with faults := [.tear]}
  require (stopped matches .error "crash") "torn B must stop before sync"
  require (torn.durable.length == stateA.durable.length + (frame 2 b).length) "tear changed declared extent"
  require (torn.durable.length < 512) "fixture batches must share a block"
  require ((torn.durable.drop stateA.durable.length).take 13 == (frame 2 b).take 13)
    "tear did not preserve the first payload byte"
  -- Probe the settled-prefix assumption: a tear in B's block also damages A's
  -- header checksum. The two small frames together fit within one possible tail.
  let damagedPrefix := torn.durable.modify 4 (fun byte => byte ^^^ 1)
  let (lost, _) := run (reopen simOps policy) (powerLoss {torn with durable := damagedPrefix})
  match policy, lost with
  | .logOnly, .ok decoded =>
    require (decoded.batches.isEmpty && !clientB.allows decoded.batches)
      "expected an undetectable loss of acknowledged A"
  | .boundary, .error "damaged header" => pure ()
  | _, _ => throw <| IO.userError "unexpected response to a damaged acknowledged prefix"
  -- Start with a cached tear only. Write it back just before recovery truncates;
  -- process death after the truncate must still leave that old extent durable.
  let beforeTrim : Ops M := {simOps with truncate := fun n => do
    modify writebackData
    simOps.truncate n}
  let cuts := if policy == .boundary then [.none, .none, .none, .crashBefore]
    else [.none, .crashBefore]
  let (aborted, cropped) := run (reopen beforeTrim policy)
    {torn with durable := stateA.durable, faults := cuts}
  require (aborted matches .error "crash") "repair must stop after truncate"
  require (cropped.visible == stateA.visible && cropped.durable == torn.visible)
    "pre-truncate writeback lost the older durable extent"
  let (retry, _, _) ← oracleOpen policy (powerLoss cropped) clientB
  require (retry.batches == [a]) "retry after pre-truncate writeback lost A"
  let (recovered, repaired, recoveredClient) ← oracleOpen policy (powerLoss torn) clientB
  require (recovered.batches == [a]) "invalid torn B survived"
  require (!recoveredClient.allows [a, b]) "oracle allowed discarded B to reappear"
  let (_, repairedAgain, recoveredClient) ← oracleOpen policy (powerLoss repaired) recoveredClient
  -- The first open's published decision is the new client base before C.
  let clientC := recoveredClient.submit c
  let (ackC, afterC) := run (appendBatch simOps policy recovered.cursor c) repairedAgain
  require ackC.isOk "C was not acknowledged after torn B"
  let _ ← oracleOpen policy (powerLoss afterC) clientC.ack
  -- Valid dirty B becomes durable through background writeback, before B's sync.
  let (failed, dirty) := run (appendBatch simOps policy cursorA b)
    {stateA with faults := [.none, .eioBefore]}
  require (failed matches .error "eio") "expected ordinary pre-sync EIO"
  let persisted := powerLoss (writebackData dirty)
  let (recovered, afterOpen, observed) ← oracleOpen policy persisted clientB
  let expected := if policy == .logOnly then [a, b] else [a]
  require (recovered.batches == expected) "background data writeback decision changed"
  let reversed := if policy == .logOnly then [a] else [a, b]
  require (!observed.allows reversed) "oracle allowed first open decision to reverse"
  let (again, afterAgain, observed) ← oracleOpen policy (powerLoss afterOpen) observed
  let nextClient := observed.submit c
  let (ackNext, afterNext) := run (appendBatch simOps policy again.cursor c) afterAgain
  require ackNext.isOk "C after adopted or discarded B failed"
  let _ ← oracleOpen policy (powerLoss afterNext) nextClient.ack
  -- Interrupt recovery immediately before data sync. Then let the repair's
  -- truncate (boundary) or adopted cached bytes (log-only) reach the disk.
  let interruptedInput := processExit dirty
  let cuts := if policy == .boundary then [.none, .none, .none, .crashBefore] else [.crashBefore]
  let (interrupted, duringRepair) := run (reopen simOps policy) {interruptedInput with faults := cuts}
  require (interrupted matches .error "crash") "recovery must stop before data barrier"
  require (duringRepair.visible == (if policy == .boundary then stateA.visible else dirty.visible))
    "unexpected repair effect before data barrier"
  let (afterRetry, _, _) ← oracleOpen policy (powerLoss (writebackData duringRepair)) clientB
  require (afterRetry.batches == expected) "writeback during interrupted repair changed decision"
  if policy == .boundary then
    -- Background writeback can publish a complete marker before its explicit
    -- sync. A retry must preserve B even when that retry is interrupted.
    let (stopped, written) := run (appendBatch simOps policy cursorA b)
      {stateA with faults := [.none, .none, .none, .crashBefore]}
    require (stopped matches .error "crash") "marker sync cut did not stop"
    let writtenBack := {written with durableMarker0 := written.marker0}
    let (interrupted, cut) := run (reopen simOps policy)
      {(processExit writtenBack) with faults := [.none, .crashBefore]}
    require (interrupted matches .error "crash") "marker recovery cut did not stop"
    let (afterRetry, _, _) ← oracleOpen policy (powerLoss cut) clientB
    require (afterRetry.batches == [a, b]) "background marker writeback lost B"
  -- A byte-for-byte valid replacement with B's generation and sequence is not
  -- an admitted torn-write image. The wire checksum cannot authenticate its origin.
  -- Exercise that limitation explicitly: the independent client oracle rejects it.
  let replacement := stateA.durable ++ frame 2 alternate
  require (replacement.length == stateA.durable.length + (frame 2 b).length) "replacement extent changed"
  let beforeBarrier : Sim := {dirty with visible := replacement, durable := replacement}
  let (early, _) := run (reopen simOps policy) (powerLoss beforeBarrier)
  match early with
  | .ok decoded =>
    if policy == .logOnly then
      require (!clientB.allows decoded.batches) "oracle accepted pre-sync replacement"
    else
      require (clientB.allows decoded.batches && decoded.batches == [a]) "unpublished replacement was exposed"
  | .error e => throw <| IO.userError s!"unexpected pre-sync replacement failure: {e}"
  let (ackB, stateB) := run (appendBatch simOps policy cursorA b) stateA
  require ackB.isOk "B must be acknowledged before replacement"
  let substituted : Sim := {stateB with visible := replacement, durable := replacement}
  let (result, _) := run (reopen simOps policy) (powerLoss substituted)
  match result with
  | .ok decoded =>
    require (decoded.batches == [a, alternate]) "expected coherent replacement to decode"
    require (!clientB.ack.allows decoded.batches) "oracle accepted an unsubmitted replacement"
  | .error e => throw <| IO.userError s!"coherent replacement unexpectedly failed: {e}"

def main : IO Unit := do
  checkWireFormat
  checkPolicy .logOnly
  checkPolicy .boundary
  checkAdversarial .logOnly
  checkAdversarial .boundary
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
