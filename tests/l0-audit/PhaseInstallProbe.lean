import Alvoki.Experiments.WAL.Segmented.Native

open WalRecoverySlice.Segmented.Native

/-- Executable probe of a successful phase installation and of the two acquired
cells across a swap. The release branch is observed separately on failed load. -/
def main : IO Unit := do
  let slot ← IO.mkRef (none : Option Nat)
  let released ← IO.mkRef false
  let acquirePhase : IO (IO.Ref (Option Nat) × Std.BaseMutex) :=
    installPhaseWith (error := IO.Error) (pure (some 7)) (fun v => liftM (IO.mkRef v))
      Std.BaseMutex.new (released.set true)
  let (phase, mutex) ← acquirePhase
  mutex.lock
  let old ← phase.swap none
  slot.set old
  let stillClosed ← phase.get
  phase.set (some 9)
  let next ← phase.get
  let framed ← slot.get
  mutex.unlock
  unless old == some 7 && stillClosed == none && next == some 9 && framed == some 7 &&
      !(← released.get) do
    throw (IO.userError "unexpected phase or slot after successful installation")
  let failedLoad : IO (Option Nat) := throw (IO.userError "injected load failure")
  let failedInstall : IO (IO.Ref (Option Nat) × Std.BaseMutex) :=
    installPhaseWith (error := IO.Error) failedLoad (fun v => liftM (IO.mkRef v)) Std.BaseMutex.new (released.set true)
  let failed ← failedInstall.toBaseIO
  unless (match failed with | .error (.userError "injected load failure") => true | _ => false) &&
      (← released.get) do
    throw (IO.userError "failed installation lost its error or skipped release")
