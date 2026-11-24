namespace Alvoki.Storage.DiskSession

/-- Session availability, independent of the representation of installed data. -/
inductive Phase (α : Type) where
  | ready (installed : α)
  | poisoned
  | closed

/-- Allocate the ready state and a separate identity for its snapshot handles. -/
@[macro_inline] def installReady [Monad m] (installed : α)
    (allocatePhase : Phase α → m ρ) (allocateSession : Unit → m σ)
    (assemble : ρ → σ → m β) : m β := do
  let phase ← allocatePhase (.ready installed)
  let session ← allocateSession ()
  assemble phase session

/-- Run publication while the session is poisoned. Only successful
completion makes the prepared state accessible. -/
@[macro_inline] def publishPrepared [Monad m]
    (setPhase : Phase α → m Unit) (publish : m Unit) (install : m β) : m β := do
  setPhase .poisoned
  publish
  install

/-- Acknowledge the prepared sequence after the durable commit. -/
@[macro_inline] def publishPreparedWrite [Monad m] (next : α) (sequence : UInt64)
    (setPhase : Phase α → m Unit) (commit : m Unit) : m UInt64 :=
  publishPrepared setPhase commit do
    setPhase (.ready next)
    return sequence

@[macro_inline] def Phase.installed [Monad m] [MonadExceptOf IO.Error m] (phase : Phase α) : m α :=
  match phase with
  | .ready value => pure value
  | .poisoned => throw (IO.userError "publication failed; reopen the database")
  | .closed => throw (IO.userError "database is closed")

/-- Require a ready session before reading the opaque handle's allocation identity. -/
@[macro_inline] def withLocalHandle [Monad m] (installed : m α) (sameSession : m Bool)
    (foreign : β) (localAction : α → m β) : m β := do
  let state ← installed
  if ← sameSession then localAction state else pure foreign

/-- A successful lock is retained by the opened session. A recovery error
unlocks first, so a failure to unlock takes precedence. -/
@[macro_inline] def openWithLock [Monad m] [MonadExceptOf IO.Error m] (tryLock : m Bool)
    (alreadyOpen : Unit → IO.Error) (unlock : Unit → m Unit) (openLocked : Unit → m α) : m α := do
  unless ← tryLock do throw (alreadyOpen ())
  try openLocked () catch error =>
    unlock ()
    throw (error : IO.Error)

/-- A successful unlock precedes the change to the closed phase. -/
@[macro_inline] def Phase.close [Monad m] (phase : Phase α)
    (unlock recordClosed : Unit → m Unit) : m Unit := do
  match phase with
  | .closed => pure ()
  | _ =>
    unlock ()
    recordClosed ()

end Alvoki.Storage.DiskSession
