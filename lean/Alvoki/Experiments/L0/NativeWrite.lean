import Alvoki.Experiments.L0.NativeRecoverAt

namespace ExperimentalL0.NativeWrite
open Lifecycle NativeScope
open WalRecoverySlice.Segmented (Contract.View)

private abbrev F := ExceptT String IO

private theorem checked_bind (a : F α) (f : α → F β) :
    Native.checked (a >>= f) = (Native.checked a >>= fun x => Native.checked (f x)) := by
  funext w
  unfold Native.checked
  rw [ExceptT.run_bind]
  cases ran : a.run w with
  | error e t => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
  | ok v t => cases v <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran,
      Pure.pure, instMonadEIO._aux_5, EST.pure] <;> rfl

private theorem checked_lift (a : IO α) : Native.checked (liftM a : F α) = a := by
  funext w
  have lifted : (liftM a : F α).run = (do return (Except.ok (← a) : Except String α) : IO _) := rfl
  cases ran : a w <;> simp [Native.checked, lifted, Bind.bind, instMonadEIO._aux_13, EST.bind, ran,
    Pure.pure, instMonadEIO._aux_5, EST.pure]

private theorem checked_pure (x : α) : Native.checked (pure x : F α) = pure x := rfl
private theorem checked_throw (e : String) :
    Native.checked (throw e : F α) = throw (IO.userError e) := rfl

private abbrev borrow (ref : Ref) (f : Wal → IO α) : IO α := do
  let some wal := (← (ref.get : IO (Phase Wal))).wal | throw (IO.userError "L0 cannot use the WAL in this phase")
  f wal

private theorem checked_borrow (ref : Ref) (f : Wal → IO α) :
    Native.checked ((Native.componentCell ref).borrowWal "L0 cannot use the WAL in this phase"
      (fun h => liftM (f h))) = borrow ref f := by
  unfold Cell.borrowWal Native.componentCell borrow
  rw [checked_bind, checked_lift]
  apply congrArg (Bind.bind (ref.get : IO (Phase Wal)))
  funext p
  cases p.wal <;> simp [checked_lift, checked_throw]

/-- The public write scans and appends through two independent reads of
the owned phase reference. The rejected position never enters append. -/
theorem write_atRoot (root : System.FilePath) (ref : Ref) (s : Session) (change : Change) :
    Native.checked (write (Native.callbackComponents root ref) s change) =
      (do
        let view ← borrow ref WalRecoverySlice.Segmented.Native.scan
        unless view.tail + 1 < UInt64.size do throw (IO.userError "absolute WAL position exhausted")
        borrow ref (fun h => do let _ ← WalRecoverySlice.Segmented.Native.append h (encode change); pure ())
        return {s with mem := insert s.mem change} : IO Session) := by
  unfold write Native.callbackComponents Cell.components Native.storageCallbacks
  rw [checked_bind, checked_borrow]
  apply congrArg (Bind.bind _)
  funext view
  split <;> simp only [checked_bind, checked_borrow, checked_pure, checked_throw]

end ExperimentalL0.NativeWrite
