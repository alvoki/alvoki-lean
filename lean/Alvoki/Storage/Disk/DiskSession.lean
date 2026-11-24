namespace Alvoki.Storage.DiskSession

/-- Session availability, independent of the representation of installed data. -/
inductive Phase (α : Type) where
  | ready (installed : α)
  | poisoned
  | closed

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

end Alvoki.Storage.DiskSession
