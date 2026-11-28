import Alvoki.Experiments.WAL.Segmented.Proofs.AppendSchedule

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open SingleFile (OpenReports)
open Model (AppendChild)
variable {id : Nat} {P bad done : W → Work → Prop}

theorem slot_get (store : Store) (s : Work) (w : W)
    (found : ((store.active.get : BaseIO _) w).val = some (id, child))
    (registered : s.1.activeEntry = some id)
    (kept : P ((store.active.get : BaseIO _) w).state s) :
    At (store.active.get : IO _) Model.readActiveEntry w s
      (fun a b t u => a = some (id, child) ∧ b = some (id, .stored id) ∧ P t u) bad := by
  change ((store.active.get : BaseIO _) w).val = _ ∧ (s.1.activeEntry.map _) = _ ∧ _
  exact ⟨found, by rw [registered]; rfl, kept⟩

theorem slot_register (store : Store) (s : Work) (w : W)
    (active : s.2 = .active .lock files cursor history)
    (kept : P ((store.active.set (some (id, child)) : BaseIO _) w).state
      ({s.1 with activeEntry := some id}, s.2)) :
    At (store.active.set (some (id, child)) : IO _) (Model.registerSuccessor id (some (id, .acquired id)))
      w s (fun _ _ => P) bad := by
  have model : (Model.registerSuccessor id (some (id, .acquired id))).run s =
      .ok (.ok ()) ({s.1 with activeEntry := some id}, s.2) := by
    simp [Model.registerSuccessor, ExceptT.run, active]
    rw [← active]
    rfl
  unfold At
  rw [model]
  exact kept

def closedWork (s : Work) : Work := ({s.1 with activeEntry := none}, .closed)
def LivePhase (s : Work) : Prop :=
  s.2 = .poisoned .lock ∨ ∃ files cursor history, s.2 = .active .lock files cursor history

theorem model_close (s : Work) (live : LivePhase s) (id : Nat) (p : Policy) (r : OpenReports) :
    (Model.closeActive id p r).run s =
       .ok (if r.unlockError then .error "primitive error" else .ok ()) (closedWork s) := by
  have eq := SingleFile.closeModel_owned p r {image := s.1.disk.segment id, held := true} live
  simp only [Model.closeActive, ExceptT.run, eq]; rfl

/-- A live active or poisoned phase contains the description used for unlock. -/
structure CloseOperand (h : SingleFile.Handle) (fd : IO.FS.Handle) (w : W) where
  cell : IO.Ref (SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle))
  mutex : Std.BaseMutex
  binds : h.Binds cell mutex
  observed :
    let value := ((cell.get : BaseIO _) (mutex.lock w).state).val
    value = .poisoned fd ∨ ∃ files cursor history, value = .active fd files cursor history

def CloseOperand.issue (op : CloseOperand h fd w) : W :=
  ((op.cell.set .closed : BaseIO _) ((op.cell.get : BaseIO _) (op.mutex.lock w).state).state).state

theorem CloseOperand.run (op : CloseOperand h fd w) : SingleFile.close h w =
    match fd.unlock op.issue with
    | .ok x t => .ok x (op.mutex.unlock t).state
    | .error e t => .error e (op.mutex.unlock t).state := by
  rw [SingleFile.close_run op.binds]
  rcases op.observed with phase | ⟨_, _, _, phase⟩ <;> simp only [phase]; all_goals rfl

/-- The outer slot is detached first. Only the exact old child's own
unlock report selects the old-close report in the branch schedule. -/
theorem close_old (store : Store) (s : Work) (w : W) (p : Policy) (r : OpenReports)
    (taken : ((store.active.swap none : BaseIO _) w).val = some (id,h))
    (op : CloseOperand h fd ((store.active.swap none : BaseIO _) w).state)
    (live : LivePhase s)
    (grant : match fd.unlock op.issue with
      | .ok _ t => r.unlockError = false ∧ done (op.mutex.unlock t).state (closedWork s)
      | .error _ t => r.unlockError = true ∧ bad (op.mutex.unlock t).state (closedWork s)) :
    At store.closeChild (Model.closeActive id p r) w s (fun _ _ => done) bad := by
  have swap : (store.active.swap none : IO _) w = .ok (some (id,h))
      ((store.active.swap none : BaseIO _) w).state := by
    change EST.Out.ok ((store.active.swap none : BaseIO _) w).val _ = _
    rw [taken]
    rfl
  unfold At
  rw [model_close s live id p r]
  simp only [Store.closeChild, closeChildWith, Bind.bind, instMonadEIO._aux_13, EST.bind, swap, op.run]
  cases call : fd.unlock op.issue <;> rw [call] at grant <;> simp [grant.1, grant.2]

/-- The successor is not in the store during an unwind. Even a different
secondary unlock error leaves the primary error and the same closed custody. -/
theorem close_unregistered (s : Work) (id : Nat) (p : Policy) (r : OpenReports)
    (live : LivePhase s) (op : CloseOperand h fd w)
    (released : P (op.mutex.unlock (returnedWorld (fd.unlock op.issue))).state (closedWork s)) :
    Finally (SingleFile.close h) (Model.closeActive id p r) w s P := by
  unfold Finally
  rw [model_close s live id p r, op.run]
  cases call : fd.unlock op.issue <;> simpa [returnedWorld, call] using released

end WalRecoverySlice.Segmented.Native.AppendIO
