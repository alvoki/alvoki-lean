import Alvoki.Experiments.WAL.Segmented.Proofs.Model
import Alvoki.Experiments.WAL.Writeback

/-! Concrete regressions against the physical segmented interpreter. -/
namespace WalRecoverySlice.Segmented.ModelTests
open WalRecoverySlice.Segmented
open WalRecoverySlice.Segmented.Model

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def start (policy : Policy) : IO (Session × State) := do
  match (create (ops healthy) policy 2).run {} with
  | .ok (.ok session) state => return (session, state)
  | _ => throw <| IO.userError "physical create failed"

private def ack (session : Session) (state : State) (p : Bytes) : IO (Session × State) := do
  match (append (ops healthy) session p).run state with
  | .ok (.ok next) after => return (next, after)
  | _ => throw <| IO.userError "physical append failed"

private def openAfter (state : State) (expected : List Bytes) : IO (Session × State) := do
  match (reopen (ops healthy)).run state with
  | .ok (.ok session) after =>
    require (session.view.base == 0 && session.view.batches == expected) "physical recovery history mismatch"
    return (session, after)
  | _ => throw <| IO.userError "physical reopen failed"

private def powerLoss (state : State) : State := {state with disk := state.disk.powerLoss}

private def damagedTrailer : Bytes :=
  if checksumBytes [42, 1, 2, 3, 20, 0, 0] = List.replicate 8 0 then
    List.replicate 8 1
  else List.replicate 8 0

private theorem damagedTrailer_size : damagedTrailer.length = 8 := by
  unfold damagedTrailer
  split <;> rfl

private theorem damagedTrailer_ne : damagedTrailer ≠ checksumBytes [42, 1, 2, 3, 20, 0, 0] := by
  unfold damagedTrailer
  split <;> simp_all [Ne.symm]

private def tornCut : Persistence.TornAppend :=
  ⟨.torn [20, 0, 0] damagedTrailer, .torn [20, 0, 0] damagedTrailer, .interrupted⟩

private def tearEffects : Effects := {healthy with
  tornAppend := fun _ _ _ cursor payload =>
    if h : payload = [20, 21, 22] ∧ cursor.nextSeq = 2 then
      some ⟨tornCut, by
        obtain ⟨rfl, seq⟩ := h
        constructor
        · simp [tornCut, Persistence.TornAppend.SameExtent, Persistence.DataResidue.SameExtent, damagedTrailer_size]
        · intro _
          rw [seq]
          simpa [tornCut, Persistence.TornAppend.Detected, Persistence.DataResidue.Detected] using
            And.intro damagedTrailer_ne damagedTrailer_ne⟩
    else none}

private def writebackEffects : Effects := {healthy with
  appendSegment := fun _ _ => {Persistence.healthyReopen with
    appendData := .full .old none, dataSync := .before .error}
  appendWritebacks := fun _ _ => {dataSync := [.data]}}

private def checkTear (policy : Policy) : IO Unit := do
  let (initial, state) ← start policy
  let (withA, state) ← ack initial state [10, 11]
  let result := (append (ops tearEffects) withA [20, 21, 22]).run state
  let stopped ← match result with
    | .error _ s => pure s
    | _ => throw <| IO.userError "physical full-length tear did not interrupt"
  let segment := stopped.disk.segment 0
  let a := frame 1 [10, 11]
  require (segment.data.durable.length == a.length + (frame 2 [20, 21, 22]).length)
    "physical tear did not retain declared extent"
  require (segment.data.durable.take a.length == a) "physical tear damaged the acknowledged prefix"
  let (_, repaired) ← openAfter (powerLoss stopped) [[10, 11]]
  let (again, stable) ← openAfter (powerLoss repaired) [[10, 11]]
  let (_, appended) ← ack again stable [30]
  let _ ← openAfter (powerLoss appended) [[10, 11], [30]]

private def checkWriteback (policy : Policy) : IO Unit := do
  let (initial, state) ← start policy
  let (withA, state) ← ack initial state [10, 11]
  let result := (append (ops writebackEffects) withA [20, 21, 22]).run state
  let stopped ← match result with
    | .ok (.error _) s => pure s
    | _ => throw <| IO.userError "expected pre-barrier EIO"
  let child := stopped.disk.segment 0
  require (child.data.durable == child.data.live) "scheduled writeback did not settle the child"
  let expected := if policy == .logOnly then [[10, 11], [20, 21, 22]] else [[10, 11]]
  let (_, repaired) ← openAfter (powerLoss stopped) expected
  let (again, stable) ← openAfter (powerLoss repaired) expected
  let (_, appended) ← ack again stable [30]
  let _ ← openAfter (powerLoss appended) (expected ++ [[30]])

private def checkRecoveryWriteback (policy : Policy) : IO Unit := do
  let (initial, state) ← start policy
  let (withA, state) ← ack initial state [10, 11]
  let unsynced : Effects := {healthy with appendSegment := fun _ _ =>
    {Persistence.healthyReopen with appendData := .full .old none, dataSync := .before .error}}
  let failed := (append (ops unsynced) withA [20, 21, 22]).run state
  let dirty ← match failed with
    | .ok (.error _) s => pure s
    | _ => throw <| IO.userError "expected dirty child after EIO"
  let expected := if policy == .logOnly then [[10, 11], [20, 21, 22]] else [[10, 11]]
  let offline : State := {dirty with disk := dirty.disk.writeback 0 .data}
  let _ ← openAfter (powerLoss offline) expected
  let duringOpen : Effects := {healthy with
    reopenWritebacks := fun _ _ => {dataRead := [.data]}
    openSegment := fun _ _ => {Persistence.healthyReopen with dataSync := .before .error}}
  let interrupted := (reopen (ops duringOpen)).run dirty
  let reached ← match interrupted with
    | .ok (.error _) s => pure s
    | _ => throw <| IO.userError "expected recovery barrier EIO"
  let durable := (reached.disk.segment 0).data.durable
  require (durable == frame 1 [10, 11] ++ frame 2 [20, 21, 22])
    "recovery writeback did not persist dirty tail before repair"
  let (_, after) ← openAfter (powerLoss reached) expected
  let _ ← openAfter (powerLoss after) expected

def main : IO Unit := do
  checkTear .logOnly
  checkTear .boundary
  checkWriteback .logOnly
  checkWriteback .boundary
  checkRecoveryWriteback .logOnly
  checkRecoveryWriteback .boundary
  IO.println "Segmented WAL physical-model fixtures passed"

end WalRecoverySlice.Segmented.ModelTests


def main : IO Unit := WalRecoverySlice.Segmented.ModelTests.main
