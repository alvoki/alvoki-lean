import Alvoki.Experiments.WAL.Segmented.Proofs.CutRuntime

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Alvoki.NativePost (W)
open Model (Disk)
open Observed (leaf finallyUnlock bindCuts bindRun)
open SingleFile.ConcreteAppend (PhaseRef)

private local instance : MonadExceptOf String Observed where
  throw e := throw (IO.userError e)
  tryCatch a f := tryCatchThe IO.Error a fun e => f e.toString

private def closeBody (stop : Stop) (cell : PhaseRef) : Observed Unit := do
  SingleFile.closeWith (← leaf stop (cell.get : IO _))
    (fun ph => leaf stop (cell.set ph : IO Unit)) (fun fd => leaf stop fd.unlock)

def closeProgram (stop : Stop) (cell : PhaseRef) (mutex : Std.BaseMutex) : Observed Unit := do
  let _ ← leaf stop (liftM mutex.lock : IO Unit)
  finallyUnlock (closeBody stop cell) mutex stop

theorem closeProgram_run (bound : h.Binds cell mu) (stop : Stop) (w : W) :
    (closeProgram stop cell mu).run w = SingleFile.close h w := by
  rw [SingleFile.close_run bound]
  let got := (cell.get : BaseIO _) (mu.lock w).state
  have lock : (leaf stop (liftM mu.lock : IO Unit)).run w = .ok () (mu.lock w).state := rfl
  have read : (leaf stop (cell.get : IO _)).run (mu.lock w).state = .ok got.val got.state := rfl
  simp only [closeProgram,closeBody,Observed.bindRun,lock,Observed.finallyUnlock_run,read]
  dsimp only [got]
  cases ((cell.get : BaseIO _) (mu.lock w).state).val with
  | closed => rfl
  | active fd _ _ _ | poisoned fd =>
    have set (v : W) : (cell.set .closed : IO Unit) v = .ok () ((cell.set .closed : BaseIO Unit) v).state := rfl
    simp only [SingleFile.closeWith,Observed.bindRun,Observed.leaf,set]
    cases fd.unlock ((cell.set .closed : BaseIO Unit) ((cell.get : BaseIO _) (mu.lock w).state).state).state <;> rfl

def closeSource (stop : Stop) (h : SingleFile.Handle) (w : W) (d : Disk) : Prop :=
  ∃ cell mutex, h.Binds cell mutex ∧ (closeProgram stop cell mutex).cuts w d

private theorem bodyCovered (bound : h.Binds cell mu)
    (cut : (finallyUnlock (closeBody stop cell) mu stop).cuts (mu.lock w).state d) :
    ∃ (α : Type) (a : IO α) (t : W), CloseSite h w a t ∧ stop a t d := by
  let got := (cell.get : BaseIO _) (mu.lock w).state
  have read : (Observed.leaf stop (cell.get : IO _)).run (mu.lock w).state = .ok got.val got.state := rfl
  change (closeBody stop cell).cuts _ d ∨ stop _ (returnedWorld ((closeBody stop cell).run _)) d at cut
  have live {fd} (op : AppendIO.CloseOperand h fd w) (cellEq : op.cell = cell) (muEq : op.mutex = mu)
      (here : (leaf stop (cell.set .closed : IO Unit) >>= fun _ => leaf stop fd.unlock).cuts got.state d ∨
        stop (liftM mu.unlock : IO Unit) (returnedWorld (fd.unlock op.issue)) d) :
      ∃ (α : Type) (a : IO α) (t : W), CloseSite h w a t ∧ stop a t d := by
    obtain ⟨r,m,b,phase⟩ := op
    change r = cell at cellEq
    change m = mu at muEq
    subst r m
    rcases here with inner | leave
    · rcases inner with clear | ⟨⟨⟩,t,ran,release⟩
      · exact ⟨_,_,_,.observed ⟨cell,mu,b,phase⟩ .close,clear⟩
      · change EST.Out.ok () ((cell.set .closed : BaseIO Unit) got.state).state = EST.Out.ok () t at ran
        cases ran
        exact ⟨_,_,_,.observed ⟨cell,mu,b,phase⟩ .unlock,release⟩
    · exact ⟨_,_,_,.observed ⟨cell,mu,b,phase⟩ .leave,leave⟩
  simp only [closeBody,bindCuts,bindRun,read] at cut
  rcases cut with (early | mid) | leave
  · exact ⟨_,_,_,.entry (.read bound),early⟩
  · cases ph : got.val with
    | closed => rw [ph] at mid; exact False.elim mid
    | poisoned fd =>
      rw [ph] at mid
      exact live ⟨cell,mu,bound,.inl ph⟩ rfl rfl (.inl mid)
    | active fd files cursor history =>
      rw [ph] at mid
      exact live ⟨cell,mu,bound,.inr ⟨_,_,_,ph⟩⟩ rfl rfl (.inl mid)
  · cases ph : got.val with
    | closed =>
      rw [ph] at leave
      exact ⟨_,_,_,.closed bound ph,leave⟩
    | poisoned fd =>
      rw [ph] at leave
      exact live ⟨cell,mu,bound,.inl ph⟩ rfl rfl (.inr leave)
    | active fd files cursor history =>
      rw [ph] at leave
      exact live ⟨cell,mu,bound,.inr ⟨_,_,_,ph⟩⟩ rfl rfl (.inr leave)

theorem closeCovered (cut : closeSource stop h w d) :
    ∃ (α : Type) (a : IO α) (t : W), CloseSite h w a t ∧ stop a t d := by
  obtain ⟨cell,mu,bound,hit⟩ := cut
  unfold closeProgram at hit
  rw [bindCuts] at hit
  rcases hit with early | inside
  · exact ⟨_,_,_,.entry (.mutex bound),early⟩
  · exact bodyCovered bound inside

def oldCloseProgram (s : Store) (stop : Stop) : Observed Unit :=
  closeChildWith (leaf stop (s.active.swap none : IO _))
    (fun h => ⟨SingleFile.close h, closeSource stop h⟩)

theorem oldCloseProgram_run (s : Store) (stop : Stop) : (oldCloseProgram s stop).run = s.closeChild := by
  unfold oldCloseProgram Store.closeChild closeChildWith
  rw [Observed.run_bind]
  apply congrArg (Bind.bind (s.active.swap none : IO _))
  funext slot
  cases slot with
  | none => rfl
  | some pair => cases pair; rfl

theorem oldCloseCovered (cut : (oldCloseProgram s stop).cuts w d) :
    ∃ (α : Type) (a : IO α) (t : W), OldClose s w a t ∧ stop a t d := by
  unfold oldCloseProgram closeChildWith at cut
  rw [bindCuts] at cut
  rcases cut with detach | child
  · exact ⟨_,_,_,.detach,detach⟩
  let slot := (s.active.swap none : BaseIO _) w
  have ran : (leaf stop (s.active.swap none : IO _)).run w = .ok slot.val slot.state := rfl
  simp only [ran] at child
  cases observed : slot.val with
  | none => rw [observed] at child; exact False.elim child
  | some pair =>
    obtain ⟨id,h⟩ := pair
    rw [observed] at child
    obtain ⟨_,a,t,site,hit⟩ := closeCovered child
    exact ⟨_,a,t,.child observed site,hit⟩

end WalRecoverySlice.Segmented.Native.AppendCut
