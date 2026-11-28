import Alvoki.Experiments.WAL.Segmented.Native

open WalRecoverySlice.Segmented (Session)
open WalRecoverySlice.Segmented.Native (Phase installPhaseWith installReopenedWith)

private abbrev Slot := IO.Ref (Option (Nat × Nat))

/-- Use the issued slot for publication. The optional decoy deliberately makes
the phase point to another allocation containing exactly the same initial value. -/
private def install (slot : Slot) (decoy : Option Slot) (fail : Bool) :
    IO (IO.Ref (Phase Slot) × Std.BaseMutex) := do
  let session : Session := ⟨⟨.logOnly,1,0,0⟩,0,⟨0,[]⟩⟩
  let load := installReopenedWith (pure (session,7)) (fun active => do
    slot.set active
    return decoy.getD slot)
  let acquireMutex : IO Std.BaseMutex := do
    if fail then throw (IO.userError "injected mutex allocation failure")
    liftM Std.BaseMutex.new
  installPhaseWith (error := IO.Error) load (fun v => liftM (IO.mkRef v))
    acquireMutex (slot.set none)

/-- Observe the returned phase by spending its slot in a following operation.
Reading the original allocation detects a handle swap even for equal old values. -/
private def consume (slot : Slot) (p : IO.Ref (Phase Slot) × Std.BaseMutex) : IO Bool := do
  p.2.lock
  try
    let old ← p.1.swap .closed
    let .ready issued _ := old | return false
    unless (← issued.get) == some (0,7) do return false
    issued.set (some (1,8))
    let .closed ← p.1.get | return false
    return (← slot.get) == some (1,8)
  finally
    p.2.unlock

def main : IO Unit := do
  let slot : Slot ← IO.mkRef none
  let failed ← (install slot none true).toBaseIO
  unless (match failed with | .error (.userError "injected mutex allocation failure") => true | _ => false) &&
      (← slot.get) == none do
    throw (IO.userError "failed installation lost its error or active-slot cleanup")
  let retried ← install slot none false
  unless ← consume slot retried do
    throw (IO.userError "retry did not hand the installed slot to its consumer")
  let decoy : Slot ← IO.mkRef (some (0,7))
  let wrong ← install slot (some decoy) false
  if ← consume slot wrong then
    throw (IO.userError "consumer accepted a different slot with equal initial contents")
