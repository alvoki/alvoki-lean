import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCut

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Alvoki.NativePost (W)
open Model (Disk)

/-- Nonreturning observations of an otherwise ordinary IO action.
A continuation is issued only after its predecessor really returned. -/
structure Observed (α : Type) where
  run : IO α
  cuts : W → Disk → Prop

instance : Monad Observed where
  pure x := ⟨pure x, fun _ _ => False⟩
  bind a f := ⟨a.run >>= fun x => (f x).run, fun w d =>
    a.cuts w d ∨ ∃ x t, a.run w = .ok x t ∧ (f x).cuts t d⟩

instance : MonadExceptOf IO.Error Observed where
  throw e := ⟨throw e, fun _ _ => False⟩
  tryCatch a handler := ⟨tryCatchThe IO.Error a.run (fun e => (handler e).run), fun w d =>
    a.cuts w d ∨ ∃ e t, a.run w = .error e t ∧ (handler e).cuts t d⟩

/-- For every operation that calls the kernel, the abrupt observation is
provided by the actual issued primitive within that operation. The root
scheduler does not invent an exception or run the unwinder after a cut. -/
structure Sites (s : Store) where
  slotRead : W → Disk → Prop
  oldClose : W → Disk → Prop
  prepare : Policy → Nat → W → Disk → Prop
  close : SingleFile.Handle → W → Disk → Prop
  sync : W → Disk → Prop
  publish : Control → W → Disk → Prop
  write : SingleFile.Handle → Bytes → W → Disk → Prop
  slotSet : Option (Nat × SingleFile.Handle) → W → Disk → Prop

def Sites.appendSession (sites : Sites s) (session : Session) (batch : Bytes) : Observed Session :=
  appendOwnedWith (error := IO.Error) session batch ⟨checked (checkAppend session batch), fun _ _ => False⟩
    IO.userError ⟨s.active.get, sites.slotRead⟩ ⟨s.closeChild, sites.oldClose⟩
    (fun p n => ⟨s.prepareChild p n, sites.prepare p n⟩) (fun h => ⟨SingleFile.close h, sites.close h⟩)
    ⟨checked s.callbacks.syncRoot, sites.sync⟩
    (fun c => ⟨checked (s.callbacks.publishControl c), sites.publish c⟩)
    (fun h b => ⟨SingleFile.append h b, sites.write h b⟩) (fun slot => ⟨s.active.set slot, sites.slotSet slot⟩)

/-- Erasure uses exactly the ordinary monad operations, including both
exception handlers that release an unpublished child after a returned error. -/
theorem Sites.erase (sites : Sites s) (session : Session) (batch : Bytes) :
    (sites.appendSession session batch).run = s.appendSession session batch := by
  unfold Sites.appendSession Store.appendSession appendOwnedWith
  apply congrArg (Bind.bind (checked (checkAppend session batch)))
  funext _
  dsimp only
  split
  · rfl
  · apply congrArg (Bind.bind (s.active.get : IO _))
    funext value
    cases value with
    | none => rfl
    | some pair => rcases pair with ⟨i, h⟩; dsimp only; split <;> rfl

/-- A prefix ends while an instruction is active. The returning post is
separate: error unwinding is entered only on a returning IO exception. -/
structure Safe (a : Observed α) (w : W) (ok : α → W → Prop) (bad : W → Prop) (stopped : Disk → Prop) : Prop where
  returned : Alvoki.NativePost.IOReturns a.run w ok bad
  cut : ∀ d, a.cuts w d → stopped d

theorem Safe.bind (first : Safe a w mid bad stop)
    (next : ∀ x t, mid x t → Safe (f x) t ok bad stop) : Safe (a >>= f) w ok bad stop := by
  obtain ⟨run, stopped⟩ := first
  constructor
  · change Alvoki.NativePost.IOReturns (a.run >>= fun x => (f x).run) _ _ _
    unfold Alvoki.NativePost.IOReturns at run ⊢
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
    cases h : a.run w with
    | error e t => rw [h] at run; exact run
    | ok x t => rw [h] at run; exact (next x t run).returned
  · rintro d (early | ⟨x, t, ran, later⟩)
    · exact stopped d early
    · rw [Alvoki.NativePost.IOReturns, ran] at run
      exact (next x t run).cut d later

theorem Safe.handle (first : Safe a w ok mid stop)
    (handler : ∀ e t, a.run w = .error e t → mid t → Safe (f e) t ok bad stop) :
    Safe (tryCatchThe IO.Error a f) w ok bad stop := by
  obtain ⟨run, stopped⟩ := first
  constructor
  · change Alvoki.NativePost.IOReturns (tryCatchThe IO.Error a.run fun e => (f e).run) _ _ _
    unfold Alvoki.NativePost.IOReturns at run ⊢
    simp only [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch]
    cases h : a.run w with
    | ok x t => rw [h] at run; exact run
    | error e t => rw [h] at run; exact (handler e t h run).returned
  · rintro d (early | ⟨e, t, ran, later⟩)
    · exact stopped d early
    · rw [Alvoki.NativePost.IOReturns, ran] at run
      exact (handler e t ran run).cut d later

end WalRecoverySlice.Segmented.Native.AppendCut
