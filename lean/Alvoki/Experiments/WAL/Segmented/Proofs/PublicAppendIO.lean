import Alvoki.Experiments.WAL.Segmented.Proofs.AppendSchedule

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W IOReturns)
open Model (AppendReady)

def issuedWorld (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store) (start : W) : W :=
  let read := (cell.get : BaseIO _) (mutex.lock start).state
  ((cell.set (.poisoned store) : BaseIO _) read.state).state

def readyWorld (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store) (next : Session)
    (before : W) : W :=
  (mutex.unlock ((cell.set (.ready store next) : BaseIO _) before).state).state

/-- The model authority, custody and client reply below come from the returned
branch of the same schedule that the native phase update executed. -/
theorem append_admitted (r : Reports batch) (store : Store) (session : Session)
    (parts : h.Parts cell mutex) (start : W) (state : Work)
    (read : ((cell.get : BaseIO _) (mutex.lock start).state).val = .ready store session)
    (ready : AppendReady session state) (slot : state.1.activeEntry = some session.control.active)
    (size : batch.length ≤ 32) (room : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false)
    (done bad : W → Work → Prop)
    (inside : session.activeCount ≠ session.control.capacity →
      InPlace store session r (issuedWorld cell mutex store start) state done bad)
    (full : session.activeCount = session.control.capacity →
      Rotation store session r (issuedWorld cell mutex store start) state done bad) :
    IOReturns (append h batch) start
      (fun reply endWorld => ∃ next t u, endWorld = readyWorld cell mutex store next t ∧
        store.appendSession session batch (issuedWorld cell mutex store start) = .ok next t ∧ done t u ∧ next = nextSession session batch ∧ AppendReady next u ∧
        u.1.activeEntry = some next.control.active ∧
        Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
        reply = next.tailPosition ∧ reply = session.view.tail + 1)
      (fun endWorld => ∃ t u, endWorld = (mutex.unlock t).state ∧
        (∃ e, store.appendSession session batch (issuedWorld cell mutex store start) = .error e t) ∧ bad t u ∧
        (let entry := if session.activeCount = session.control.capacity then none else state.1.activeEntry
         u.1.activeEntry = entry ∧ u.2 = if entry.isSome then .poisoned .lock else .closed) ∧
        Recoverable session.view (some (.append batch)) u.1.disk) := by
  let begin := issuedWorld cell mutex store start
  have tied := appendSession r store session size room inside full
  have model := Model.nativeAppendModel_refines store.root r.directory r.removal r.effects r.create r.close session
    (r.append session.control.policy) state ready slot size room linux
  dsimp only at model
  unfold At at tied
  unfold IOReturns
  rw [append_ready_run parts batch start read]
  dsimp only
  rw [show ((cell.set (.poisoned store) : BaseIO _) ((cell.get : BaseIO _) (mutex.lock start).state).state).state = begin from rfl]
  cases actual : store.appendSession session batch begin <;>
    cases logical : (r.action store session).run state with
    | error =>
      rw [actual, logical] at tied
      contradiction
    | ok report reached =>
      rw [actual, logical] at tied
      unfold Reports.action at logical
      rw [logical] at model
      cases report <;> try contradiction
      first
      |
        obtain ⟨eqnext, rfl, completed⟩ := tied
        exact ⟨_, _, _, rfl, rfl, completed, eqnext, model.2.1, model.2.2, model.1.2.1, rfl, model.1.2.2⟩
      | exact ⟨_, _, rfl, ⟨_,rfl⟩, tied, model.2, model.1⟩

theorem rejected_worker (store : Store) (session : Session) (batch : Bytes) (w : W)
    (invalid : batch.length > 32 ∨ session.view.tail ≥ Contract.maxPosition) :
    ∃ e, store.appendSession session batch w = .error e w := by
  by_cases size : batch.length > 32
  · simp only [Store.appendSession, appendOwnedWith, checkAppend, size, ↓reduceIte]
    exact ⟨_,rfl⟩
  · have exhausted := invalid.resolve_left size
    simp only [Store.appendSession, appendOwnedWith, checkAppend, size, exhausted, ↓reduceIte]
    exact ⟨_,rfl⟩

/-- Rejection occurs after poisoning the outer handle, before the first
access to its child slot. The caller can therefore release the original child. -/
theorem append_rejected (parts : h.Parts cell mutex) (store : Store) (session : Session)
    (start : W) (batch : Bytes)
    (read : ((cell.get : BaseIO _) (mutex.lock start).state).val = .ready store session)
    (invalid : batch.length > 32 ∨ session.view.tail ≥ Contract.maxPosition) :
    ∃ e, append h batch start = .error e (mutex.unlock (issuedWorld cell mutex store start)).state := by
  rw [append_ready_run parts batch start read]
  by_cases size : batch.length > 32
  · simp only [Store.appendSession, appendOwnedWith, checkAppend, size, ↓reduceIte]
    exact ⟨_, rfl⟩
  · have exhausted := invalid.resolve_left size
    simp only [Store.appendSession, appendOwnedWith, checkAppend, size, exhausted, ↓reduceIte]
    exact ⟨_, rfl⟩

end WalRecoverySlice.Segmented.Native.AppendIO
