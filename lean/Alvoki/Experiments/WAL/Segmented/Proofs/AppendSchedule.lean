import Alvoki.Experiments.WAL.Segmented.Proofs.AppendIO

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open Model (State Effects RootReports ActiveAppendM AppendChild successor)

abbrev Work := State × SingleFile.AppendPhase

structure Reports (batch : Bytes) where
  directory : Nat
  removal : RootReports
  effects : Effects
  create : SingleFile.CreateReports
  close : SingleFile.OpenReports
  append : ∀ policy cursor, SingleFile.AppendReports policy cursor batch

def Reports.action (r : Reports batch) (store : Store) (session : Session) :=
  Model.nativeAppendModel store.root r.directory r.removal r.effects r.create r.close
    session session.control.active (r.append session.control.policy)

def nextSession (session : Session) (batch : Bytes) : Session :=
  if session.activeCount = session.control.capacity then ⟨successor session, 1, session.view.append batch⟩
  else ⟨session.control, session.activeCount + 1, session.view.append batch⟩

/-- The slot read and the write use the same already registered child. -/
structure InPlace (store : Store) (session : Session) (r : Reports batch) (w : W) (s : Work)
    (done bad : W → Work → Prop) where
  owned : SingleFile.Handle → W → Work → Prop
  slot : At (store.active.get : IO _) Model.readActiveEntry w s
    (fun a b t u => ∃ h, a = some (session.control.active, h) ∧
      b = some (session.control.active, .stored session.control.active) ∧ owned h t u) bad
  write : ∀ h t u, owned h t u → At (SingleFile.append h batch)
    (Model.writeAs session (r.append session.control.policy) (.stored session.control.active)
      (.stored session.control.active) batch) t u (fun _ _ => done) bad

/-- Stage preconditions are consumed in execution order. The newly acquired
handle stays unregistered until its own data append has returned. -/
structure Rotation (store : Store) (session : Session) (r : Reports batch) (w : W) (s : Work)
    (done bad : W → Work → Prop) where
  cleared : W → Work → Prop
  prepared : SingleFile.Handle → W → Work → Prop
  synced : SingleFile.Handle → W → Work → Prop
  published : SingleFile.Handle → W → Work → Prop
  written : SingleFile.Handle → W → Work → Prop
  drop : SingleFile.Handle → W → Work → Prop
  closeOld : At store.closeChild (Model.closeActive session.control.active session.control.policy r.close) w s
    (fun _ _ => cleared) bad
  prepare : ∀ t u, cleared t u → At (store.prepareChild session.control.policy (successor session).active)
    (Model.acquireSuccessor store.root r.removal r.effects r.create session.control.policy (successor session).active)
    t u (fun h id t' u' => id = .acquired (successor session).active ∧ prepared h t' u') bad
  sync : ∀ h t u, prepared h t u → At (checked store.callbacks.syncRoot)
    (Model.liftRootAction (Model.nativeControlOps store.root r.directory r.effects).syncRoot)
    t u (fun _ _ => synced h) (drop h)
  publish : ∀ h t u, synced h t u → At (checked (store.callbacks.publishControl (successor session)))
    (Model.liftRootAction (Segmented.publish (Model.nativeControlOps store.root r.directory r.effects) (successor session)))
    t u (fun _ _ => published h) (drop h)
  write : ∀ h t u, published h t u → At (SingleFile.append h batch)
    (Model.writeAs session (r.append session.control.policy) (.acquired (successor session).active)
      (.acquired (successor session).active) batch) t u (fun _ _ => written h) (drop h)
  register : ∀ h t u, written h t u → At (store.active.set (some ((successor session).active, h)) : IO _)
    (Model.registerSuccessor (successor session).active
      (some ((successor session).active, .acquired (successor session).active)))
    t u (fun _ _ => done) (drop h)
  release : ∀ h t u, drop h t u → Finally (SingleFile.close h)
    (Model.closeActive (successor session).active session.control.policy r.close) t u bad

private theorem io_unit (k : Unit → IO α) : (pure () >>= k) = k () := rfl

private theorem check_ok (session : Session) (batch : Bytes)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition) :
    checked (checkAppend session batch) = pure () := by
  funext t
  simp [checkAppend, Nat.not_lt_of_ge size, Nat.not_le_of_lt position, checked]
  rfl

theorem appendSession (r : Reports batch) (store : Store) (session : Session)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (inside : session.activeCount ≠ session.control.capacity → InPlace store session r w s done bad)
    (full : session.activeCount = session.control.capacity → Rotation store session r w s done bad) :
    At (store.appendSession session batch) (r.action store session) w s
      (fun x y t u => x = nextSession session batch ∧ y = x ∧ done t u) bad := by
  unfold Store.appendSession Reports.action Model.nativeAppendModel appendOwnedWith
  rw [check_ok session batch size position]
  have modelCheck : (checkAppend session batch : ActiveAppendM Unit) = pure () := by
    simp [checkAppend, Nat.not_lt_of_ge size, Nat.not_le_of_lt position]
  rw [modelCheck]
  simp only [pure_bind]
  by_cases rotate : session.activeCount = session.control.capacity
  · let ops := full rotate
    simp only [rotate, ↓reduceIte]
    apply At.bind ops.closeOld
    intro _ _ u s' cleared
    unfold withActiveChild
    apply At.bind (ops.prepare u s' cleared)
    rintro h _ v state ⟨rfl, prepared⟩
    apply At.masked (unwind := ops.drop h) _ (ops.release h)
    apply At.bind (ops.sync h v state prepared)
    intro _ _ t st synced
    apply At.bind (ops.publish h t st synced)
    intro _ _ t st published
    apply At.bind (ops.write h t st published)
    intro _ _ t st written
    apply At.bind (ops.register h t st written)
    exact fun _ _ t st final => ⟨by simp [nextSession, rotate, successor], rfl, final⟩
  · let ops := inside rotate
    simp only [rotate, ↓reduceIte]
    simp only [io_unit]
    apply At.bind ops.slot
    rintro _ _ u st ⟨h, rfl, rfl, held⟩
    dsimp only
    simp only [BEq.rfl, ↓reduceIte]
    apply At.bind (ops.write h u st held)
    exact fun _ _ t s final => ⟨by simp [nextSession, rotate], rfl, final⟩

end WalRecoverySlice.Segmented.Native.AppendIO
