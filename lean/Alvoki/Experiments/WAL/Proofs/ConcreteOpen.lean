import Alvoki.Experiments.WAL.Proofs.ConcreteRecovery

namespace WalRecoverySlice.SingleFile.ConcreteRecovery
open Persistence System

abbrev Ref := IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle))
abbrev ModelOpened := Opened OpenTarget (AppendFiles OpenTarget)
abbrev ActualOpened := Opened IO.FS.Handle (AppendFiles IO.FS.Handle)

/-- A primitive may require an entry condition which is consumed by its
single call. The invariant R is retained on either reported outcome. -/
def SimResult (R : W → σ → Prop) (a : F α) (b : ExceptT String (EStateM Unit σ) β) (rel : α → β → Prop)
    (w : W) (s : σ) : Prop :=
  match a.run w, b.run s with
  | .ok (.ok x) t, .ok (.ok y) u => R t u ∧ rel x y
  | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => R t u
  | _, _ => False

/-- The two actual pathname opens returned their respective descriptors
at these very entry worlds. No capability is carried past a subsequent
read of the stamp or acquisition of the exclusive lock. -/
def Fresh (dir : FilePath) (p : Policy) (r : OpenReports) (R : W → OpenImage → Prop)
    (target : OpenTarget) (h : IO.FS.Handle) (t : W) (u : OpenImage) : Prop :=
  ∃ w s, R w s ∧ (nativeOpen.openTarget dir target).run w = .ok (.ok h) t ∧
    ((openEffects p r).openTarget dir target).run s = .ok (.ok target) u

theorem SimResult.bind {a : F α} {b : OpenM β} {f : α → F γ} {g : β → OpenM δ}
    (first : SimResult R a b rel w s)
    (next : ∀ x y t u, a.run w = .ok (.ok x) t → b.run s = .ok (.ok y) u →
      R t u → rel x y → SimResult R (f x) (g y) out t u) :
    SimResult R (a >>= f) (b >>= g) out w s := by
  unfold SimResult at *
  rw [ExceptT.run_bind, ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at first ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | contradiction | exact first | exact next _ _ _ _ ha hb first.1 first.2
  case error.ok _ _ y _ => cases y <;> first | contradiction | exact first
  all_goals first | contradiction | exact first

/-- The local namespace/descriptor assumptions required during single-file
acquisition. A relation B ties each acquired description to an OpenTarget. -/
structure OpenSteps (dir : FilePath) (policy : Policy) (r : OpenReports)
    (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop) : Prop where
  openFile : ∀ target, Sim R (nativeOpen.openTarget dir target)
    ((openEffects policy r).openTarget dir target) (fun h model => model = target ∧ B h target)
  unbuffered : ∀ h target w s, Fresh dir policy r R target h w s → B h target → R w s →
    SimResult R (nativeOpen.unbuffered h) ((openEffects policy r).unbuffered target) Eq w s
  policyRead : ∀ h w s, Fresh dir policy r R .policy h w s → B h .policy → R w s →
    SimResult R (nativeOpen.readPolicy (dir / "policy") h)
      ((openEffects policy r).readPolicy (dir / "policy") .policy)
      (fun x y => x = y ∧ y = stampText policy) w s
  lock : ∀ h w s, Fresh dir policy r R .lock h w s → B h .lock → R w s →
    SimResult R (nativeOpen.tryLock h) ((openEffects policy r).tryLock .lock) Eq w s
  unlock : ∀ h, B h .lock → Sim R (nativeOpen.unlock h) ((openEffects policy r).unlock .lock) Eq
  sync : ∀ h target, target = .policy ∨ target = .directory → B h target → Sim R (nativeOpen.sync h) ((openEffects policy r).sync target) Eq

theorem OpenSteps.bindFreshOpen (steps : OpenSteps dir p r R B) (target : OpenTarget)
    {f : IO.FS.Handle → F α} {g : OpenTarget → OpenM β}
    (next : ∀ h t u, Fresh dir p r R target h t u → B h target → R t u →
      SimResult R (f h) (g target) out t u) :
    Sim R (nativeOpen.openTarget dir target >>= f) ((openEffects p r).openTarget dir target >>= g) out := by
  intro w s frame
  change SimResult R _ _ out w s
  apply SimResult.bind (a := nativeOpen.openTarget dir target) (b := (openEffects p r).openTarget dir target)
    (rel := fun h model => model = target ∧ B h target) (steps.openFile target w s frame)
  rintro h _ t u actual model post ⟨rfl, bound⟩
  exact next _ _ _ ⟨w, s, frame, actual, model⟩ bound post

theorem SimResult.thenSim {a : F α} {b : OpenM β} {f : α → F γ} {g : β → OpenM δ}
    (first : SimResult R a b rel w s)
    (next : ∀ x y, rel x y → Sim R (f x) (g y) out) :
    SimResult R (a >>= f) (b >>= g) out w s :=
  first.bind fun _ _ _ _ _ _ frame pair => next _ _ pair _ _ frame

/-- Two native reads of the same stamp description reject a reusable
healthy stamp law: after the first call the second can observe EOF. -/
theorem stampRead_notReusable (p : Policy) (path : FilePath) (h : IO.FS.Handle)
    (entry : R w s)
    (first : (nativeOpen.readPolicy path h).run w = .ok (.ok (stampText p)) t)
    (eof : (nativeOpen.readPolicy path h).run t = .ok (.ok "") u) :
    ¬ Sim R (nativeOpen.readPolicy path h) ((openEffects p {}).readPolicy path .policy) Eq := by
  intro reused
  have model (v : OpenImage) : ((openEffects p {}).readPolicy path .policy).run v =
      .ok (.ok (stampText p)) v := rfl
  have step := reused w s entry
  rw [first, model] at step
  have second := reused t s step.1
  rw [eof, model] at second
  have impossible := second.2
  cases p <;> contradiction

def Markers (B : IO.FS.Handle → OpenTarget → Prop) (p : Policy)
    (markers : Option (IO.FS.Handle × IO.FS.Handle)) : Prop :=
  match p, markers with
  | .boundary, some (a,b) => B a .marker0 ∧ B b .marker1
  | .logOnly, none => True
  | _, _ => False

structure Files (B : IO.FS.Handle → OpenTarget → Prop) (p : Policy)
    (a : OpenFiles IO.FS.Handle) (b : OpenFiles OpenTarget) : Prop where
  stamp : B a.stamp .policy
  policy : a.policy = p
  reader : B a.reader .reader
  writer : B a.writer .writer
  markers : Markers B p a.markers
  model : b = ⟨.policy, p, .reader, .writer, markersFor p⟩

private theorem acquire (steps : OpenSteps dir p r R B) :
    Sim R (acquireWith nativeOpen dir) (acquireWith (openEffects p r) dir)
      (fun h target => target = .lock ∧ B h .lock) := by
  unfold acquireWith
  apply steps.bindFreshOpen .lock
  intro h w s fresh held frame
  apply (steps.lock h w s fresh held frame).thenSim
  intro a b same
  subst b
  split
  · exact Sim.pure ⟨rfl, held⟩
  · exact Sim.throw

private theorem files (steps : OpenSteps dir p r R B) :
    Sim R (openFilesWith nativeOpen dir) (openFilesWith (openEffects p r) dir) (Files B p) := by
  unfold openFilesWith
  apply steps.bindFreshOpen .policy
  intro stamp w s fresh st frame
  apply (steps.policyRead stamp w s fresh st frame).thenSim
  intro text expected eq
  obtain ⟨rfl, eq⟩ := eq
  subst text
  cases p <;> dsimp only [stampText]
  all_goals
    apply steps.bindFreshOpen .reader
    intro reader w s fresh hr frame
    apply (steps.unbuffered reader _ w s fresh hr frame).thenSim
    intro _ _ _
    apply steps.bindFreshOpen .writer
    intro writer w s fresh hw frame
    apply (steps.unbuffered writer _ w s fresh hw frame).thenSim
    intro _ _ _
  case logOnly => exact Sim.pure ⟨st, rfl, hr, hw, trivial, rfl⟩
  case boundary =>
    apply steps.bindFreshOpen .marker0
    intro zero w s fresh hz frame
    apply (steps.unbuffered zero _ w s fresh hz frame).thenSim
    intro _ _ _
    apply steps.bindFreshOpen .marker1
    intro one w s fresh ho frame
    apply (steps.unbuffered one _ w s fresh ho frame).thenSim
    intro _ _ _
    exact Sim.pure ⟨st, rfl, hr, hw, ⟨hz, ho⟩, rfl⟩

/-- The fixed report schedule describes only the calls issued to the
held reader and marker descriptions. Intervening per-file writebacks can be
selected independently at each primitive in the existing persistence model. -/
structure WorkerSteps (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop)
    (r : OpenReports) : Prop where
  data : ∀ h (base : OpenImage), B h .reader → Sim (fun w i => R w {base with image := i})
    (nativeRecovery.readFromStart h) ((scheduledOps (ops r.worker) r.writebacks).readData) Eq
  truncate : ∀ h n (base : OpenImage), B h .reader → Sim (fun w i => R w {base with image := i})
    (nativeRecovery.truncateAt h n) ((scheduledOps (ops r.worker) r.writebacks).truncate n) Eq
  syncData : ∀ h (base : OpenImage), B h .reader → Sim (fun w i => R w {base with image := i})
    (nativeRecovery.sync h) ((scheduledOps (ops r.worker) r.writebacks).syncData) Eq
  marker : ∀ h slot (base : OpenImage), slot < 2 → B h (if slot = 0 then .marker0 else .marker1) →
    Sim (fun w i => R w {base with image := i})
      (nativeRecovery.readFromStart h) ((scheduledOps (ops r.worker) r.writebacks).readMarker slot) Eq
  syncMarker : ∀ h slot (base : OpenImage), slot < 2 → B h (if slot = 0 then .marker0 else .marker1) →
    Sim (fun w i => R w {base with image := i})
      (nativeRecovery.sync h) ((scheduledOps (ops r.worker) r.writebacks).syncMarker slot) Eq

/-- Only issued primitive obligations appear in the log-only branch. -/
private theorem logWorker (steps : WorkerSteps R B r) (reader writer : IO.FS.Handle)
    (held : B reader .reader) (base : OpenImage) :
    Sim (fun w i => R w {base with image := i}) (recoverNative .logOnly reader writer none)
      (recoverScheduled r.worker r.writebacks .logOnly) Eq := by
  rw [recoverScheduled_eq]
  unfold recoverNative recoverWith WalRecoverySlice.reopen
  have leftPure {α β : Type} (x : α) (f : α → F β) : (pure x >>= f) = f x := rfl
  have rightPure {α β : Type} (x : α) (f : α → M β) : (pure x >>= f) = f x := rfl
  simp only [leftPure, rightPure]
  dsimp
  repeat' first
    | exact Sim.pure rfl
    | exact Sim.throw
    | exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ h => h.elim)
    | apply (steps.data reader base held).bind; intro a b eq; subst b
    | apply (steps.truncate reader _ base held).bind; intro a b eq; cases a; cases b
    | apply (steps.syncData reader base held).bind; intro a b eq; cases a; cases b
    | simp only [leftPure, rightPure]
    | split
    | dsimp only

theorem worker (steps : WorkerSteps R B r) (files : Files B p a b) :
    Sim R (recoverNative a.policy a.reader a.writer a.markers)
      (workerEffect r b.policy b.reader b.writer b.markers) Eq := by
  rcases files with ⟨_, pol, reader, _, markers, rfl⟩
  rw [pol]
  intro w base pre
  have run : Sim (fun w i => R w {base with image := i}) (recoverNative p a.reader a.writer a.markers)
      (recoverScheduled r.worker r.writebacks p) Eq := by
    cases p with
    | logOnly =>
      cases m : a.markers with
      | none => exact logWorker steps _ _ reader _
      | some pair => simp [Markers, m] at markers
    | boundary =>
      cases m : a.markers with
      | none => simp [Markers, m] at markers
      | some pair =>
        obtain ⟨zero, one⟩ := pair
        have h : B zero .marker0 ∧ B one .marker1 := by simpa [Markers, m] using markers
        rw [recoverScheduled_eq]
        unfold recoverNative recoverWith
        apply reopen
        constructor
        · exact steps.data _ _ reader
        · intro slot fit
          by_cases z : slot = 0
          · subst slot; exact steps.marker zero 0 base fit h.1
          · have eq : slot = 1 := by omega
            subst slot; exact steps.marker one 1 base fit h.2
        · intro n; exact steps.truncate _ n _ reader
        · exact steps.syncData _ _ reader
        · intro slot fit
          by_cases z : slot = 0
          · subst slot; exact steps.syncMarker zero 0 base fit h.1
          · have eq : slot = 1 := by omega
            subst slot; exact steps.syncMarker one 1 base fit h.2
  have obs := run w base.image pre
  have lift : (workerEffect r p .reader .writer (markersFor p)).run base =
      match (recoverScheduled r.worker r.writebacks p).run base.image with
      | .ok response image => EStateM.Result.ok response {base with image}
      | .error e image => .error e {base with image} := by simp [workerEffect]; rfl
  rw [lift]
  cases actual : (recoverNative p a.reader a.writer a.markers).run w <;>
    cases model : (recoverScheduled r.worker r.writebacks p).run base.image <;>
    simp only [actual, model] at obs ⊢
  case ok.ok x _ y _ => cases x <;> cases y <;> exact obs
  case error.ok _ _ y _ => cases y <;> exact obs
  all_goals exact obs

/-- Logical shape of the exact record constructed before ref allocation. -/
structure OpenedTogether (B : IO.FS.Handle → OpenTarget → Prop) (p : Policy)
    (a : ActualOpened) (b : ModelOpened) : Prop where
  lock : B a.lock .lock
  reader : B a.reader .reader
  writer : B a.writer .writer
  markers : Markers B p a.markers
  policy : a.policy = p
  batches : a.recovered = b.recovered
  phase : a.phase = .active a.lock (appendFiles a.writer a.reader a.markers)
    a.recovered.cursor a.recovered.batches

private theorem install (steps : OpenSteps dir p r R B) (recovery : WorkerSteps R B r)
    (lock : B h .lock) :
    Sim R (installWith nativeOpen recoverNative appendFiles dir h)
      (installWith (openEffects p r) (workerEffect r) appendFiles dir .lock) (OpenedTogether B p) := by
  unfold installWith
  apply (files steps).bind
  intro a b pair
  apply (worker recovery pair).bind
  intro decoded modelDecoded eq
  subst modelDecoded
  obtain ⟨stamp, policy, reader, writer, markers, rfl⟩ := pair
  unfold settleWith
  have set : Sim R (settleWith nativeOpen dir a.stamp)
      (settleWith (openEffects p r) dir .policy) Eq := by
    unfold settleWith
    apply (steps.sync _ _ (.inl rfl) stamp).bind
    intro _ _ _
    apply (steps.openFile .directory).bind
    intro directory role hr
    obtain ⟨rfl, held⟩ := hr
    exact steps.sync _ _ (.inr rfl) held
  apply set.bind
  intro _ _ _
  exact Sim.pure ⟨lock, reader, writer, markers, policy, rfl, rfl⟩

/-- A pointwise primitive observation with separate continuations for
returned values and errors. Each refers to both reached states. -/
def At (a : F α) (b : OpenM β) (w : W) (s : OpenImage)
    (ok : α → β → W → OpenImage → Prop) (fail : W → OpenImage → Prop) : Prop :=
  match a.run w, b.run s with
  | .ok (.ok x) t, .ok (.ok y) u => ok x y t u
  | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => fail t u
  | _, _ => False

private theorem At.bind {a : F α} {b : OpenM β} {f : α → F γ} {g : β → OpenM δ}
    (first : At a b w s mid fail)
    (next : ∀ x y t u, mid x y t u → At (f x) (g y) t u ok fail) :
    At (a >>= f) (b >>= g) w s ok fail := by
  unfold At at *
  rw [ExceptT.run_bind, ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at first ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | contradiction | exact first | exact next _ _ _ _ first
  case error.ok x t y u => cases y <;> first | contradiction | exact first
  all_goals exact first

private theorem Sim.atPost {a : F α} {b : OpenM β} (h : Sim R a b rel)
    (entry : R w s) : At a b w s (fun x y t u => R t u ∧ rel x y) R := by
  have post := h w s entry
  unfold At
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at post ⊢
  case ok.ok x t y u => cases x <;> cases y <;> exact post
  case error.ok x t y u => cases y <;> exact post
  all_goals exact post

private def CaughtPost (ok : α → β → W → OpenImage → Prop) (fail : W → OpenImage → Prop) :
    Except IO.Error α → Except String β → W → OpenImage → Prop
  | .ok x, .ok y, t, u => ok x y t u
  | .error _, .error _, t, u => fail t u
  | _, _, _, _ => False

private theorem catchCall {a : F α} {b : OpenM β} (same : At a b w s ok fail) :
    At (liftM ((checked a).toBaseIO)) (SingleFile.attempt b) w s (CaughtPost ok fail) unused := by
  unfold At at *
  have caught : (liftM ((checked a).toBaseIO) : F _).run w =
      match a.run w with
      | .error e t => .ok (.ok (.error e)) t
      | .ok (.error e) t => .ok (.ok (.error (IO.userError e))) t
      | .ok (.ok x) t => .ok (.ok (.ok x)) t := by
    change (BaseIO.toEIO (do return Except.ok (← (checked a).toBaseIO)) : IO _) w = _
    cases ran : a.run w with
    | error => simp [checked, EIO.toBaseIO, BaseIO.toEIO, Bind.bind, instMonadBaseIO._aux_13,
        instMonadEIO._aux_13, ST.bind, EST.bind, ran]; exact ⟨rfl, rfl⟩
    | ok result t =>
      cases result <;> simp [checked, EIO.toBaseIO, BaseIO.toEIO, Bind.bind, instMonadBaseIO._aux_13,
        instMonadEIO._aux_13, ST.bind, EST.bind, ran] <;> exact ⟨rfl, rfl⟩
  have attempted : (SingleFile.attempt b).run s =
      match b.run s with
      | .ok v t => .ok (.ok v) t
      | .error e t => .error e t := rfl
  rw [caught, attempted]
  cases na : a.run w <;> cases mb : b.run s <;> simp only [na, mb] at same
  case ok.ok x t y u => cases x <;> cases y <;> exact same
  case error.ok x t y u => cases y <;> exact same
  all_goals exact same

structure Runtime (R : W → OpenImage → Prop) where
  cell : W → Ref → Phase IO.FS.Handle (AppendFiles IO.FS.Handle) → Prop
  mutex : W → Std.BaseMutex → Prop
  newRef : ∀ phase w s, R w s →
    let r := (IO.mkRef phase : BaseIO Ref) w
    R r.state s ∧ cell r.state r.val phase
  newMutex : ∀ w s ref phase, R w s → cell w ref phase →
    let r := Std.BaseMutex.new w
    R r.state s ∧ cell r.state ref phase ∧ mutex r.state r.val

/-- Identifies the allocated ref and mutex in the actual returned handle
and the phase constructed from the same primitive recovery execution. -/
def Owns (runtime : Runtime R) (B : IO.FS.Handle → OpenTarget → Prop)
    (p : Policy) (w : W) (h : Handle) (ready : ModelOpened) : Prop :=
  ∃ a : ActualOpened, OpenedTogether B p a ready ∧ ∃ ref mutex,
    h.Assembled a.policy ref mutex ∧ runtime.cell w ref a.phase ∧ runtime.mutex w mutex

/-- The exact lock description and world returned by the first issued primitive. -/
def LockFileAt (dir : FilePath) (w : W) (h : IO.FS.Handle) (t : W) : Prop :=
  (nativeOpen.openTarget dir .lock).run w = .ok (.ok h) t

/-- A granted lock on this invocation's freshly opened description. -/
def LockedAt (dir : FilePath) (w : W) (h : IO.FS.Handle) (t : W) : Prop :=
  ∃ opened, LockFileAt dir w h opened ∧ (nativeOpen.tryLock h).run opened = .ok (.ok true) t

private def installActual (dir : FilePath) (h : IO.FS.Handle) : F Handle :=
  installWith nativeOpen recoverNative appendFiles dir h >>= fun a => liftM (installReady a)

/-- Provenance of the owned description and the failed, unwinding install;
only the unlock syscall remains before rethrow. -/
def Unwinding (dir : FilePath) (w : W) (h : IO.FS.Handle) (t : W) : Prop :=
  ∃ locked, LockedAt dir w h locked ∧ ∃ e, (checked (installActual dir h)).toBaseIO locked = ⟨.error e, t⟩

/-- Outside-worker writebacks are charged to the primitives actually
reached. The very first open consumes the initial image and its prefix.
Only terminal leaf outcomes produce the suffix. -/
structure Boundaries (dir : FilePath) (p : Policy) (r : OpenReports)
    (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop) (rt : Runtime R)
    (w : W) (initial : OpenImage) (physical : W → OpenImage → Prop) : Prop where
  first : At (nativeOpen.openTarget dir .lock) ((openEffects p r).openTarget dir .lock)
    w (settleImage r.beforeWorker initial)
    (fun h role t u => role = .lock ∧ B h .lock ∧ R t u)
    (fun t u => physical t (settleImage r.afterWorker u))
  tryLock : ∀ h t u, LockFileAt dir w h t → B h .lock → R t u →
    At (nativeOpen.tryLock h) ((openEffects p r).tryLock .lock) t u
      (fun granted model t' u' => granted = model ∧
        if granted then R t' u' else physical t' (settleImage r.afterWorker u'))
      (fun t' u' => physical t' (settleImage r.afterWorker u'))
  drop : ∀ h t u, Unwinding dir w h t → B h .lock → R t u →
    At (nativeOpen.unlock h) ((openEffects p r).unlock .lock) t u
      (fun _ _ t' u' => physical t' (settleImage r.afterWorker u'))
      (fun t' u' => physical t' (settleImage r.afterWorker u'))
  allocated : ∀ t u ref phase, R t u → rt.cell t ref phase →
    physical (Std.BaseMutex.new t).state (settleImage r.afterWorker u)

private theorem allocate (rt : Runtime R) (pair : OpenedTogether B p a b) (frame : R t u)
    (boundary : Boundaries dir p r R B rt w initial phys) :
    At (liftM (installReady a)) (pure b) t u
      (fun h ready t' u' => phys t' (settleImage r.afterWorker u') ∧ Owns rt B p t' h ready) R := by
  obtain ⟨h, ran, assembled⟩ := installReady_run a t
  have cell := rt.newRef a.phase t u frame
  obtain ⟨frame, saved, held⟩ := rt.newMutex _ u _ _ cell.1 cell.2
  have lifted : (liftM (installReady a) : F _).run t =
      .ok (.ok h) (Std.BaseMutex.new ((IO.mkRef a.phase : BaseIO Ref) t).state).state := by
    change (match installReady a t with
      | .ok value t => EST.Out.ok (Except.ok value : Except String Handle) t
      | .error e t => EST.Out.error e t) = _
    rw [ran]
  unfold At
  rw [lifted]
  exact ⟨boundary.allocated _ u _ _ cell.1 cell.2, a, pair, _, _, assembled, saved, held⟩

private theorem At.trace {a : F α} {b : OpenM β} (h : At a b w s ok fail) :
    At a b w s (fun x y t u => ok x y t u ∧ a.run w = .ok (.ok x) t) fail := by
  unfold At at *
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | exact h | exact ⟨h, rfl⟩
  case error.ok x t y u => cases y <;> exact h
  all_goals exact h

private theorem openBody (steps : OpenSteps dir p r R B) (recovery : WorkerSteps R B r)
    (rt : Runtime R) (edge : Boundaries dir p r R B rt w initial phys) :
    At (openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
      (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
      (fun ready => installReady ready) dir)
      (openExistingWith (openEffects p r) SingleFile.attempt throw (workerEffect r) appendFiles pure dir)
      w (settleImage r.beforeWorker initial)
      (fun h ready t u => phys t (settleImage r.afterWorker u) ∧ Owns rt B p t h ready)
      (fun t u => phys t (settleImage r.afterWorker u)) := by
  unfold openExistingWith
  apply At.bind (mid := fun h role t u => role = .lock ∧ B h .lock ∧ R t u ∧ LockedAt dir w h t)
  · unfold acquireWith
    apply edge.first.trace.bind
    rintro h _ opened u ⟨⟨rfl, held, frame⟩, fresh⟩
    apply (edge.tryLock h opened u fresh held frame).trace.bind
    rintro granted _ t u ⟨⟨rfl, frame⟩, issued⟩
    cases granted
    · exact frame
    · exact ⟨rfl, held, frame, opened, fresh, issued⟩
  rintro h _ locked u ⟨rfl, held, frame, lockRun⟩
  have installed := ((install steps recovery held).atPost frame).bind
    (f := fun a => liftM (installReady a)) (g := pure)
    (fun _ _ _ _ info => allocate rt info.2 info.1 edge)
  apply (catchCall installed).trace.bind
  intro x y t u caught
  obtain ⟨pair, trace⟩ := caught
  cases x <;> cases y
  case ok.ok => exact pair
  case error.error err _ =>
    have unwinding : Unwinding dir w h t := by
      refine ⟨locked, lockRun, err, ?_⟩
      change (liftM ((checked (installActual dir h)).toBaseIO) : F _).run locked = _ at trace
      change (BaseIO.toEIO (do return Except.ok (← (checked (installActual dir h)).toBaseIO)) : IO _) locked = _ at trace
      cases call : (checked (installActual dir h)).toBaseIO locked with
      | mk value after =>
        simp [BaseIO.toEIO, Bind.bind, instMonadBaseIO._aux_13, ST.bind, call] at trace
        change Except.ok value = Except.ok (Except.error err) ∧ after = t at trace
        rw [Except.ok.inj trace.1, trace.2]
    apply (catchCall (edge.drop _ _ _ unwinding held pair)).bind
    intro a b t u result
    cases a <;> cases b <;> first | exact result | exact False.elim result
  all_goals exact False.elim pair

theorem openExisting {physical : W → OpenImage → Prop} (steps : OpenSteps dir p r R B)
    (recovery : WorkerSteps R B r) (rt : Runtime R) (w : W) (initial : OpenImage)
    (edge : Boundaries dir p r R B rt w initial physical) :
    match SingleFile.openExisting dir w, openExistingModel dir p r initial with
    | .ok h t, .ok (.ok ready) u => physical t u ∧ Owns rt B p t h ready
    | .error _ t, .ok (.error _) u => physical t u
    | _, _ => False := by
  let a : F Handle := openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
    (fun ready => installReady ready) dir
  let b : OpenM ModelOpened := openExistingWith (openEffects p r) SingleFile.attempt throw
    (workerEffect r) appendFiles pure dir
  let s := settleImage r.beforeWorker initial
  have same : At a b w s _ _ := openBody steps recovery rt edge
  unfold At at same
  have checkedRun : SingleFile.openExisting dir w = match a.run w with
    | .error e t => .error e t
    | .ok (.ok x) t => .ok x t
    | .ok (.error e) t => .error (IO.userError e) t := by
    change (checked a w) = _
    unfold checked
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
    cases a.run w with
    | error => rfl
    | ok v t => cases v <;> rfl
  have modelRun : openExistingModel dir p r initial = settleResult r.afterWorker
      (match b.run s with
      | .ok v u => .ok v u
      | .error e u => .error e {u with held := false}) := rfl
  rw [checkedRun, modelRun]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at same
  case ok.ok x t y u => cases x <;> cases y <;> exact same
  case error.ok x t y u => cases y <;> exact same
  all_goals exact same

/-- Local laws for a read of a registered phase under the actual mutex.
All three instructions carry the physical frame to their successor. -/
structure ScanSteps (R : W → OpenImage → Prop) (rt : Runtime R) : Prop where
  lock : ∀ t u cell phase mutex, R t u → rt.mutex t mutex → rt.cell t cell phase →
    let reached := (mutex.lock t).state
    R reached u ∧ rt.mutex reached mutex ∧ rt.cell reached cell phase
  read : ∀ t u cell phase mutex, R t u → rt.mutex t mutex → rt.cell t cell phase →
    let got := (cell.get : BaseIO _) t
    got.val = phase ∧ R got.state u ∧ rt.mutex got.state mutex ∧ rt.cell got.state cell phase
  unlock : ∀ t u cell phase mutex, R t u → rt.mutex t mutex → rt.cell t cell phase →
    let reached := (mutex.unlock t).state
    R reached u ∧ rt.mutex reached mutex ∧ rt.cell reached cell phase

theorem scan (steps : ScanSteps R rt) (owned : Owns rt B p w h ready) (image : R w u) :
    ∃ t, SingleFile.scan h w = .ok ready.recovered.batches t ∧
      R t u ∧ Owns rt B p t h ready := by
  obtain ⟨a, pair, cell, mutex, bound, ref, held⟩ := owned
  obtain ⟨frame, held, ref⟩ := steps.lock _ _ _ _ _ image held ref
  obtain ⟨got, frame, held, ref⟩ := steps.read _ _ _ _ _ frame held ref
  have eq := scan_active_run bound w (got.trans pair.phase)
  obtain ⟨frame, held, ref⟩ := steps.unlock _ _ _ _ _ frame held ref
  exact ⟨_, pair.batches ▸ eq, frame, a, pair, cell, mutex, bound, ref, held⟩

end WalRecoverySlice.SingleFile.ConcreteRecovery
