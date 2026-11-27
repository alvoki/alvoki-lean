import Alvoki.Experiments.WAL.Segmented.Protocol

/-! Deterministic segmented-WAL tests. The client oracle is deliberately
independent of the executable recovery scanner and simulated disk state. -/
namespace WalRecoverySlice.Segmented.Tests

private structure Oracle where
  known : List Bytes := []
  pending : Option Bytes := none
  base : Nat := 0
  requestedBase : Option Nat := none

private def Oracle.submit (o : Oracle) (batch : Bytes) : Oracle :=
  {o with pending := some batch}

private def Oracle.ack (o : Oracle) : Oracle :=
  match o.pending with
  | none => o
  | some batch => {o with known := o.known ++ [batch], pending := none}

private def Oracle.requestDiscard (o : Oracle) (through : Nat) : Oracle :=
  {o with requestedBase := some (max o.base through)}

private def Oracle.discardAck (o : Oracle) : Oracle :=
  {o with base := o.requestedBase.getD o.base, requestedBase := none}

private def Oracle.allows (o : Oracle) (base : Nat) (retained : List Bytes) : Bool :=
  let validBase := base == o.base || o.requestedBase == some base
  let sameHistory (history : List Bytes) := retained == history.drop base
  validBase && (sameHistory o.known || match o.pending with
    | none => false
    | some batch => sameHistory (o.known ++ [batch]))

/-- A successful recovery fixes both the chosen base and uncertain batch. -/
private def Oracle.observe (o : Oracle) (base : Nat) (retained : List Bytes) : Except String Oracle := do
  unless o.allows base retained do throw "unexpected recovered history"
  let history := if retained == (o.known.drop base) then o.known else o.known ++ o.pending.toList
  return {known := history, base := base}

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checkOracle : IO Unit := do
  let a : Bytes := [1]
  let b : Bytes := [2]
  let c : Bytes := [3]
  let o : Oracle := {known := [a, b], pending := some c}
  require (o.allows 0 [a, b] && o.allows 0 [a, b, c]) "oracle must permit uncertain suffix"
  require (!o.allows 0 [a, c]) "oracle accepted a gap"
  let .ok adopted := o.observe 0 [a, b, c] | throw <| IO.userError "oracle failed to adopt"
  require (!adopted.allows 0 [a, b]) "oracle allowed adopted batch to disappear"
  let checkpoint := ({known := [a, b, c]} : Oracle).requestDiscard 2
  require (checkpoint.allows 0 [a, b, c] && checkpoint.allows 2 [c]) "oracle lost a checkpoint outcome"
  let .ok released := checkpoint.observe 2 [c] | throw <| IO.userError "oracle failed to adopt checkpoint"
  require (!released.allows 0 [a, b, c]) "oracle allowed checkpoint to roll back"

inductive Tag where
  | prepare | root | stage | controlSync | rename | openSegment | appendSegment | list | remove
  deriving BEq, Repr
inductive Timing where | before | after | crashBefore | crashAfter | cacheOnly deriving BEq, Repr
structure Injection where
  tag : Tag
  skip : Nat := 0
  timing : Timing
  deriving Repr
structure Segment where
  policy : Policy
  live : List Bytes := []
  durable : List Bytes := []
  deriving Repr
structure Disk where
  names : List Nat := []
  durableNames : List Nat := []
  files : List (Nat × Segment) := []
  control : Option Control := none
  durableControl : Option Control := none
  staged : Option Control := none
  stagedDurable : Option Control := none
  fault : Option Injection := none
  deriving Repr
abbrev M := ExceptT String (EStateM Unit Disk)

private def stop : M α := liftM (show EStateM Unit Disk α from throw ())

private def gate (tag : Tag) (effect : Disk → Disk) : M Unit := do
  let state ← get
  let timing ← match state.fault with
    | some fault => do
      if fault.tag == tag then
        if fault.skip == 0 then
          set {state with fault := none}
          pure (some fault.timing)
        else
          set {state with fault := some {fault with skip := fault.skip - 1}}
          pure none
      else pure none
    | none => pure none
  if timing == some .before then throw "eio"
  if timing == some .crashBefore then stop
  modify effect
  if timing == some .after then throw "eio"
  if timing == some .crashAfter then stop

private def getFile (s : Disk) (id : Nat) : Option Segment :=
  (s.files.find? (fun pair => pair.1 == id)).map Prod.snd
private def putFile (s : Disk) (id : Nat) (file : Segment) : Disk :=
  {s with files := (id, file) :: s.files.filter (fun pair => pair.1 != id)}

private def simOps : Ops M where
  prepareSegment policy id := gate .prepare fun s =>
    let s := putFile s id ⟨policy, [], []⟩
    {s with names := id :: s.names.filter (· != id)}
  syncRoot := gate .root fun s => {s with durableNames := s.names, durableControl := s.control}
  stageControl c := gate .stage fun s => {s with staged := some c}
  syncControl := gate .controlSync fun s => {s with stagedDurable := s.staged}
  renameControl := do
    let s ← get
    if s.stagedDurable.isNone then throw "staged control not synced"
    gate .rename fun s => {s with control := s.stagedDurable}
  readControl := do
    let some c := (← get).control | throw "missing control"
    return c
  openSegment policy id := do
    let s ← get
    unless s.names.contains id do throw "missing segment"
    let some file := getFile s id | throw "missing file"
    unless file.policy == policy do throw "policy mismatch"
    let accepted := if policy == .logOnly then file.live else file.durable
    gate .openSegment (fun state => putFile state id {file with live := accepted, durable := accepted})
    return accepted
  appendSegment policy id batch := do
    let s ← get
    unless s.names.contains id do throw "missing segment"
    let some file := getFile s id | throw "missing file"
    unless file.policy == policy do throw "policy mismatch"
    if let some fault := s.fault then
      if fault.tag == .appendSegment && fault.skip == 0 && fault.timing == .cacheOnly then
        set (putFile {s with fault := none} id {file with live := file.live ++ [batch]})
        throw "eio"
    gate .appendSegment (fun state => putFile state id
      {file with live := file.live ++ [batch], durable := file.durable ++ [batch]})
  listSegments := do
    gate .list id
    return (← get).names
  removeSegment segment := gate .remove fun s => {s with names := s.names.filter (· != segment)}

private def run (action : M α) (s : Disk) : Except String α × Disk :=
  match action.run s with
  | .ok result state => (result, state)
  | .error _ state => (.error "crash", state)

private def powerLoss (s : Disk) : Disk :=
  {s with names := s.durableNames, control := s.durableControl, staged := s.stagedDurable, files := s.files.map (fun (id, file) => (id, {file with live := file.durable})), fault := none}

private def processExit (s : Disk) : Disk := {s with fault := none}

private def checked (r : Except String α) : IO α :=
  match r with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"unexpected error: {error}"

private def openChecked (s : Disk) (client : Oracle) : IO (Session × Disk × Oracle) := do
  let (result, after) := run (reopen simOps) s
  let session ← checked result
  let next ← checked (client.observe session.view.base session.view.batches)
  return (session, after, next)

private def submitBatch (s : Disk) (session : Session) (oracle : Oracle) (batch : Bytes) : IO (Session × Disk × Oracle) := do
  let submitted := oracle.submit batch
  let (result, state) := run (append simOps session batch) s
  let session ← checked result
  return (session, state, submitted.ack)

private def runScenario (policy : Policy) : IO Unit := do
  let a : Bytes := [1]; let b : Bytes := [2]; let c : Bytes := [3]
  let (created, state) := run (create simOps policy 2) {}
  let created ← checked created
  let (session, state, oracle) ← submitBatch state created {} a
  let (session, state, oracle) ← submitBatch state session oracle b
  for timing in [Timing.before, .after, .crashBefore, .crashAfter] do
    for (tag, skip) in [(Tag.prepare, 0), (.root, 0), (.stage, 0), (.controlSync, 0), (.rename, 0), (.root, 1), (.appendSegment, 0)] do
      let (result, stopped) := run (append simOps session c) {state with fault := some ⟨tag, skip, timing⟩}
      require (!result.isOk) s!"rotation cut did not fire: {repr tag}"
      for reboot in [powerLoss, processExit] do
        let (recovered, afterOpen, observed) ← openChecked (reboot stopped) (oracle.submit c)
        let (_, _, _) ← openChecked (powerLoss afterOpen) observed
        let d : Bytes := [4]
        let (_, afterD, next) ← submitBatch afterOpen recovered observed d
        let _ ← openChecked (powerLoss afterD) next
  -- Data visible in cache but lacking its segment commit is adopted only by log-only.
  let (result, dirty) := run (append simOps session c) {state with fault := some ⟨.appendSegment, 0, .cacheOnly⟩}
  require (!result.isOk) "expected uncertain segment append"
  let (opened, after, observed) ← openChecked (processExit dirty) (oracle.submit c)
  require (opened.view.batches == (if policy == .logOnly then [a, b, c] else [a, b]))
    "unexpected cached segment decision"
  let _ ← openChecked (powerLoss after) observed
  -- Four segments allow an interrupted collection to leave multiple retired names.
  let mut active := session
  let mut storage := state
  let mut client := oracle
  for value in [3, 4, 5, 6, 7] do
    let (next, nextDisk, nextOracle) ← submitBatch storage active client [value]
    active := next; storage := nextDisk; client := nextOracle
  for timing in [Timing.before, .after, .crashBefore, .crashAfter] do
    for (tag, skip) in [(Tag.stage, 0), (.controlSync, 0), (.rename, 0), (.root, 0), (.list, 0), (.remove, 0), (.remove, 1), (.root, 1)] do
      let (result, stopped) := run (discardThrough simOps active 6)
        {storage with fault := some ⟨tag, skip, timing⟩}
      require (!result.isOk) s!"discard cut did not fire: {repr tag}"
      for reboot in [powerLoss, processExit] do
        let (_, repaired, observed) ← openChecked (reboot stopped) (client.requestDiscard 6)
        let (opened, afterRetry, observed) ← openChecked (powerLoss repaired) observed
        let (_, afterNext, observed) ← submitBatch afterRetry opened observed [8]
        let _ ← openChecked (powerLoss afterNext) observed
  -- Publish the release, then fail before collection. Repeated recovery cuts
  -- must tolerate both persisted and unpersisted individual removals.
  let (releaseCut, uncollected) := run (discardThrough simOps active 6)
    {storage with fault := some ⟨.list, 0, .before⟩}
  require (!releaseCut.isOk) "expected failure after release publication"
  require (uncollected.durableControl == some {active.control with discarded := 6})
    "release was not durably published before collection"
  for timing in [Timing.before, .after, .crashBefore, .crashAfter] do
    for (tag, skip) in [(Tag.root, 0), (.openSegment, 0), (.list, 0), (.remove, 0), (.remove, 1), (.root, 1)] do
      let (failed, interrupted) := run (reopen simOps)
        {(processExit uncollected) with fault := some ⟨tag, skip, timing⟩}
      require (!failed.isOk) s!"reopen cut did not fire: {repr tag}"
      let (recovered, after, observed) ← openChecked (powerLoss interrupted) (client.requestDiscard 6)
      require (recovered.view.base == 6 && recovered.view.batches == [[7]])
        "retry failed to preserve published release and suffix"
      let _ ← openChecked (powerLoss after) observed
  -- A partial-segment release retains its suffix; a full active segment released
  -- through tail stays named and returns an empty view, never modulo zero.
  let (released, afterRelease) := run (discardThrough simOps active 5) storage
  let released ← checked released
  let releasedClient := (client.requestDiscard 5).discardAck
  require (released.view.batches == [[6], [7]]) "partial release lost suffix"
  let (opened, _, _) ← openChecked (powerLoss afterRelease) releasedClient
  require (opened.view.batches == [[6], [7]]) "reopen lost retained suffix"
  let (fullCreated, fullDisk) := run (create simOps policy 2) {}
  let fullCreated ← checked fullCreated
  let (full, fullDisk, fullOracle) ← submitBatch fullDisk fullCreated {} a
  let (full, fullDisk, fullOracle) ← submitBatch fullDisk full fullOracle b
  let (empty, afterEmpty) := run (discardThrough simOps full 2) fullDisk
  let empty ← checked empty
  require (empty.view.base == 2 && empty.view.batches.isEmpty) "full active release was not empty"
  require (afterEmpty.names.contains 0) "collection removed active segment"
  let (reopened, reopenedDisk, reopenedOracle) ← openChecked (powerLoss afterEmpty) ((fullOracle.requestDiscard 2).discardAck)
  require (reopened.view.batches.isEmpty) "full active release reappeared"
  let (_, afterNext, nextOracle) ← submitBatch reopenedDisk reopened reopenedOracle c
  let (nextOpen, _, _) ← openChecked (powerLoss afterNext) nextOracle
  require (nextOpen.view.base == 2 && nextOpen.view.batches == [c]) "append after full active release failed"
  let (same, _) := run (discardThrough simOps reopened 2) (powerLoss afterEmpty)
  require (same matches .ok _) "idempotent release failed"
  let (tooFar, _) := run (discardThrough simOps reopened 3) (powerLoss afterEmpty)
  require (!tooFar.isOk) "release beyond tail succeeded"

def main : IO Unit := do
  checkOracle
  runScenario .logOnly
  runScenario .boundary
  IO.println "Segmented WAL simulations passed"

end WalRecoverySlice.Segmented.Tests


def main : IO Unit := WalRecoverySlice.Segmented.Tests.main
