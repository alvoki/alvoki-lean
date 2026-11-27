import Alvoki.Experiments.WAL.Recovery

namespace WalRecoverySlice

inductive Fault where | none | crashBefore | eioBefore | eioAfter | tear deriving BEq, Repr
structure Sim where
  visible : Bytes := []
  durable : Bytes := []
  marker : Option (Nat × Nat) := some (0, 0)
  durableMarker : Option (Nat × Nat) := some (0, 0)
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
      let partialBytes := b.take 6 ++ List.replicate (b.length - 6) 0
      modify fun s => {s with faults := s.faults.drop 1, visible := s.visible ++ partialBytes,
                              durable := s.durable ++ partialBytes}
      stop
    step fun s => {s with visible := s.visible ++ b}
  syncData := step fun s => {s with durable := s.visible}
  replaceMarker n seq := step fun s => {s with marker := some (n, seq)}
  syncDirectory := step fun s => {s with durableMarker := s.marker}
  readData := do
    let s ← get
    if s.readError then throw "read eio"
    return s.visible
  readMarker := do
    match (← get).marker with
    | some marker => return marker
    | none => throw "missing marker"
  truncate n := step fun s => {s with visible := s.visible.take n}

def run (m : M α) (s : Sim) : Except String α × Sim :=
  match (m.run).run s with
  | .ok r state => (r, state)
  | .error _ state => (.error "crash", state)

def powerLoss (s : Sim) : Sim := {s with visible := s.durable, marker := s.durableMarker, faults := [], readError := false}
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
  let (repairResult, interrupted) := run (reopen simOps policy) {tornImage with faults := (if policy == .boundary then [.none] else []) ++ [.none, .crashBefore]}
  require (repairResult matches .error "crash") "repair should stop before its sync"
  let _ ← expectOpen policy (powerLoss interrupted) [a]
  if policy == .boundary then
    -- The process stops after rename. Open must settle B before exposing it.
    let (stoppedAtRename, renamed) := run (appendBatch simOps policy afterA b)
      {s with faults := [.none, .none, .none, .crashBefore]}
    require (stoppedAtRename matches .error "crash") "expected interrupted directory sync"
    let _ ← expectOpen policy (powerLoss renamed) [a]
    let (_, adopted) ← expectOpen policy (processExit renamed) [a, b]
    let _ ← expectOpen policy (powerLoss adopted) [a, b]
    for fault in [Fault.eioBefore, .eioAfter] do
      let (submitted, reached) := run (appendBatch simOps policy afterA b)
        {s with faults := [.none, .none, .none, fault]}
      require (!submitted.isOk) "publication error acknowledged B"
      let history := if fault == .eioAfter then [a, b] else [a]
      let _ ← expectOpen policy (powerLoss reached) history
    let (missing, _) := run (reopen simOps policy) {s with marker := none}
    require (!missing.isOk) "missing marker must fail"
    let (rb, committed) := run (appendBatch simOps policy afterA b) s
    require rb.isOk "B should be acknowledged"
    let damage := committed.durable.take (committed.durable.length - 1) ++ [0]
    let damaged := {committed with visible := damage, durable := damage}
    let (result, _) := run (reopen simOps policy) (powerLoss damaged)
    require (!result.isOk) "published damaged B must fail"

def main : IO Unit := do
  checkPolicy .logOnly
  checkPolicy .boundary
  -- A deliberately early ACK loses the supposedly acknowledged batch on reboot.
  let (_, bad) := run (simOps.append (frame 1 [9])) {}
  let (result, _) := run (reopen simOps .logOnly) (powerLoss bad)
  match result with
  | .ok d => require (d.batches != [[9]]) "oracle failed to catch early ACK"
  | .error e => throw <| IO.userError e
  IO.println "WAL recovery slice: all checks passed"
end WalRecoverySlice

def main : IO Unit := WalRecoverySlice.main
