import Alvoki.Experiments.WAL.Segmented.Proofs.AppendBody

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open Model (Disk State AppendReady successor)

def Context.nextId (c : Context disk) : Nat := (successor c.session).active

def Context.Candidate (c : Context disk) (h : SingleFile.Handle) (w : W) (st : Work) : Prop :=
  c.Base none w st.1.disk ∧ c.Bound c.nextId h w st.2

theorem livePhase_of_bound (c : Context disk) (h : c.Bound id' child w s.2) : LivePhase s := by
  obtain ⟨a, lock, state⟩ := h
  unfold LivePhase
  cases phase : s.2 with
  | closed => rw [phase] at state; exact False.elim state
  | poisoned token => rw [phase] at state; exact .inl (by rw [state.1])
  | active token files pos bs => rw [phase] at state; exact .inr ⟨_, _, _, by rw [state.1]⟩

structure Detach (c : Context disk) (r : Reports batch) (old : SingleFile.Handle) (w : W) (s : Work) where
  fd : IO.FS.Handle
  source : OpenedChild (segmentPath c.store.root c.session.control.active) old fd
  close : CloseOperand old fd ((c.store.active.swap none : BaseIO _) w).state
  unlock : match fd.unlock close.issue with
    | .ok _ t => r.close.unlockError = false ∧ c.Base none (close.mutex.unlock t).state s.1.disk
    | .error _ t => r.close.unlockError = true ∧ c.Base none (close.mutex.unlock t).state s.1.disk

structure Unwind (c : Context disk) (h : SingleFile.Handle) (w : W) (s : Work) where
  fd : IO.FS.Handle
  source : OpenedChild (segmentPath c.store.root c.nextId) h fd
  close : CloseOperand h fd w
  unlock : c.Base none (close.mutex.unlock (returnedWorld (fd.unlock close.issue))).state s.1.disk

def phaseAt (phase : SingleFile.AppendPhase) (p : Policy) (id : Nat) (d : Disk) : Prop :=
  ∃ pos bs, phase = .active .lock (SingleFile.appendBindings p) pos bs ∧ d.cursor id = pos

/-- The control steps carry the same acquired (as yet unregistered)
description. Their final model cursor still indexes that description. -/
def Context.rootFrame (c : Context disk) (h : SingleFile.Handle) (phase : SingleFile.AppendPhase)
    (t : W) (u : State) : Prop :=
  c.Candidate h t (u,phase) ∧ phaseAt phase c.session.control.policy c.nextId u.disk

inductive Point where | cleared | prepared | synced | published | written | unwind

/-- Each stage consumes the return and corresponding model world of the
preceding operation from this particular invocation. Private proposals,
clock indices and old child identities cannot be exchanged between runs. -/
inductive Prefix (c : Context disk) (r : Reports batch) (origin : W) (initial : Work) :
    Point → Option SingleFile.Handle → W → Work → Prop where
  | close : Returned c.store.closeChild (Model.closeActive c.session.control.active c.session.control.policy r.close)
      origin initial () () t u → Prefix c r origin initial .cleared none t u
  | create : Prefix c r origin initial .cleared none t u →
      Returned (c.store.prepareChild c.session.control.policy c.nextId)
        (Model.acquireSuccessor c.store.root r.removal r.effects r.create c.session.control.policy c.nextId)
        t u h (.acquired c.nextId) v n → Prefix c r origin initial .prepared (some h) v n
  | sync : Prefix c r origin initial .prepared (some h) t u →
      Returned (checked c.store.callbacks.syncRoot)
        (Model.liftRootAction (Model.nativeControlOps c.store.root r.directory r.effects).syncRoot)
        t u () () v n → Prefix c r origin initial .synced (some h) v n
  | syncError : Prefix c r origin initial .prepared (some h) t u →
      Reported (checked c.store.callbacks.syncRoot)
        (Model.liftRootAction (Model.nativeControlOps c.store.root r.directory r.effects).syncRoot) t u v n →
      Prefix c r origin initial .unwind (some h) v n
  | publish : Prefix c r origin initial .synced (some h) t u →
      Returned (checked (c.store.callbacks.publishControl (successor c.session)))
        (Model.liftRootAction (Segmented.publish (Model.nativeControlOps c.store.root r.directory r.effects)
          (successor c.session))) t u () () v n → Prefix c r origin initial .published (some h) v n
  | publishError : Prefix c r origin initial .synced (some h) t u →
      Reported (checked (c.store.callbacks.publishControl (successor c.session)))
        (Model.liftRootAction (Segmented.publish (Model.nativeControlOps c.store.root r.directory r.effects)
          (successor c.session))) t u v n → Prefix c r origin initial .unwind (some h) v n
  | write : Prefix c r origin initial .published (some h) t u →
      Returned (SingleFile.append h batch)
        (Model.writeAs c.session (r.append c.session.control.policy) (.acquired c.nextId) (.acquired c.nextId) batch)
        t u () () v n → Prefix c r origin initial .written (some h) v n
  | writeError : Prefix c r origin initial .published (some h) t u →
      Reported (SingleFile.append h batch)
        (Model.writeAs c.session (r.append c.session.control.policy) (.acquired c.nextId) (.acquired c.nextId) batch)
        t u v n → Prefix c r origin initial .unwind (some h) v n

structure LocalRotation (c : Context disk) (r : Reports batch) (h : SingleFile.Handle) (w : W) (s : Work) where
  detach : Detach c r h w s
  prepare : ∀ t (u : Work), Prefix c r w s .cleared none t u → c.Base none t u.1.disk →
    PrepareIO.Successor c.store c.session.control.policy c.nextId r.removal r.effects r.create t u.1
      (fun v n => c.Base none v n.disk) (fun child phase v => c.Bound c.nextId child v phase)
  root : ∀ child t u, Prefix c r w s .prepared (some child) t u → c.ReadyFile none c.nextId child t u →
    At (syncHandle c.store.directory) (ControlIO.rootSync r.effects) t u.1
      (fun _ _ => c.rootFrame child u.2) (c.rootFrame child u.2)
  control : ∀ child t u, Prefix c r w s .synced (some child) t u → c.ReadyFile none c.nextId child t u →
    ControlIO.Primitives c.store (successor c.session) r.effects t u.1 (c.rootFrame child u.2)
  write : ∀ child t u, Prefix c r w s .published (some child) t u → c.ReadyFile none c.nextId child t u → WriteSteps c none c.nextId child r t u
  install : ∀ child t u, Prefix c r w s .written (some child) t u → c.Candidate child t u → (∃ files cursor history, u.2 = .active .lock files cursor history) →
    let v := ((c.store.active.set (some (c.nextId,child)) : BaseIO _) t).state
    c.Base (some (c.nextId,child)) v u.1.disk ∧ c.Bound c.nextId child v u.2
  release : ∀ child t u, Prefix c r w s .unwind (some child) t u → c.Candidate child t u → Unwind c child t u

private theorem prepare_matches (c : Context disk) (r : Reports batch) (s : Work)
    (linux : System.Platform.isWindows = false)
    (earned : (Model.acquireSuccessor c.store.root r.removal r.effects r.create c.session.control.policy c.nextId).run s =
        .ok (.ok tag) u) : Matches c.session.control.policy c.nextId u := by
  simp only [Model.acquireSuccessor, ExceptT.run] at earned
  split at earned <;> try cases earned
  rename_i ran
  have facts := Model.prepareNativeChild_authority _ _ _ _ _ _ linux ran
  exact ⟨_, [], facts.2.2.1, facts.2.1⟩

private def ActivePhase (s : Work) := ∃ files pos bs, s.2 = .active .lock files pos bs

private theorem wrote_active {r : Reports batch} (c : Context disk) (id : Nat) (src : Work)
    (ran : (Model.writeAs c.session (r.append c.session.control.policy) (.acquired id) (.acquired id) batch).run src =
      .ok (.ok ()) dst) (bound : c.Bound id h w dst.2) : ActivePhase dst := by
  simp [Model.writeAs, Model.writeRequested, Model.AppendChild.segment] at ran
  obtain ⟨fd, files, pos, bs, phase⟩ := Model.writeActive_success_active _ _ _ ran
  obtain ⟨a, _, stat⟩ := bound
  rw [phase] at stat
  exact ⟨files, pos, bs, stat.1 ▸ phase⟩

def LocalRotation.assemble {r : Reports batch} (io : LocalRotation c r old w s)
    (held : c.ReadyFile (some (c.session.control.active, old)) c.session.control.active old w s)
    (active : (successor c.session).active ≤ ControlCodec.wordMax)
    (discarded : (successor c.session).discarded ≤ ControlCodec.wordMax)
    (full : c.session.activeCount = c.session.control.capacity) (linux : System.Platform.isWindows = false) :
    Rotation c.store c.session r w s (c.Done batch) c.Failed := by
  let id := c.nextId
  refine ⟨fun t st => Prefix c r w s .cleared none t st ∧ c.Base none t st.1.disk,
    fun h t st => Prefix c r w s .prepared (some h) t st ∧ c.ReadyFile none id h t st,
    fun h t st => Prefix c r w s .synced (some h) t st ∧ c.ReadyFile none id h t st,
    fun h t st => Prefix c r w s .published (some h) t st ∧ c.ReadyFile none id h t st,
    fun h t st => Prefix c r w s .written (some h) t st ∧ c.Candidate h t st ∧ ActivePhase st,
    fun h t st => Prefix c r w s .unwind (some h) t st ∧ c.Candidate h t st,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have take := c.heap.swap none held.1.2.2.2
    apply (close_old c.store s w c.session.control.policy r.close take io.detach.close
      (livePhase_of_bound c held.2.1) (done := fun t st => c.Base none t st.1.disk)
      (bad := fun t st => c.Base none t st.1.disk) io.detach.unlock).record.map
    · rintro ⟨⟩ ⟨⟩ _ _ ⟨x, ran⟩; exact ⟨.close ran, x⟩
    · exact fun _ st x => c.base_empty st x.1
  · rintro t st ⟨earlier,frame⟩
    have acquired := (io.prepare t st earlier frame).acquire st.2
    apply acquired.trace.map
    · rintro h tag v after ⟨⟨rfl, bound, stayed⟩, returned, run⟩
      exact ⟨rfl, .create earlier ⟨returned, run⟩, stayed, bound, prepare_matches c r st linux run⟩
    · exact fun v after x => c.base_empty after x.2
  · rintro child t u ⟨earlier,held⟩
    have run := (ControlIO.syncRoot c.store r.directory (io.root child t u earlier held)).liftRoot u.2
    apply run.record.map
    · rintro ⟨⟩ ⟨⟩ v st ⟨⟨⟨frame, matched⟩, same⟩, ret⟩
      exact ⟨.sync earlier ret, frame.1, same ▸ frame.2, by change phaseAt st.2 _ _ st.1.disk; rw [same]; exact matched⟩
    · rintro v st ⟨⟨⟨frame, _⟩, same⟩, ret⟩
      exact ⟨.syncError earlier ret, frame.1, same ▸ frame.2⟩
  · rintro child t u ⟨earlier,held⟩
    have run := (ControlIO.publish (io.control child t u earlier held) r.directory active discarded).liftRoot u.2
    apply run.record.map
    · rintro ⟨⟩ ⟨⟩ v st ⟨⟨⟨frame, matched⟩, same⟩, ret⟩
      exact ⟨.publish earlier ret, frame.1, same ▸ frame.2, by change phaseAt st.2 _ _ st.1.disk; rw [same]; exact matched⟩
    · rintro v st ⟨⟨⟨frame, _⟩, same⟩, ret⟩
      exact ⟨.publishError earlier ret, frame.1, same ▸ frame.2⟩
  · rintro child t st ⟨earlier, held⟩
    have write := (io.write child t st earlier held).run held (.acquired id) rfl
    apply write.record.map
    · rintro ⟨⟩ ⟨⟩ v u ⟨frame, ran⟩
      exact ⟨.write earlier ran, frame, wrote_active c id st ran.2 frame.2⟩
    · exact fun _ _ x => ⟨.writeError earlier x.2, x.1⟩
  · rintro child t st ⟨earlier, candidate, active⟩
    obtain ⟨files,pos,bs,phase⟩ := active
    have frame := io.install child t st earlier candidate ⟨files,pos,bs,phase⟩
    apply (slot_register (P := fun v u => c.Base (some (id,child)) v u.1.disk ∧ c.Bound id child v u.2)
      (bad := fun _ _ => False) c.store st t phase frame).map
    · intro _ _ v u x
      unfold Context.Done
      simp only [nextSession, full, ↓reduceIte]
      exact ⟨child,x⟩
    · exact fun _ _ x => x.elim
  · rintro child t st ⟨earlier,candidate⟩
    let op := io.release child t st earlier candidate
    exact close_unregistered st id c.session.control.policy r.close (livePhase_of_bound c candidate.2)
      op.close (c.base_empty (closedWork st) op.unlock)

end WalRecoverySlice.Segmented.Native.AppendIO
