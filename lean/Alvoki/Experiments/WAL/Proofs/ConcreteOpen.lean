import Alvoki.Experiments.WAL.Proofs.ConcreteRecovery

namespace WalRecoverySlice.SingleFile.ConcreteRecovery
open Persistence System

abbrev Ref := IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle))
abbrev ModelOpened := Opened OpenTarget (AppendFiles OpenTarget)
abbrev ActualOpened := Opened IO.FS.Handle (AppendFiles IO.FS.Handle)

/-- The local namespace/descriptor assumptions required during single-file
acquisition. A relation B ties each acquired description to an OpenTarget. -/
structure OpenSteps (dir : FilePath) (policy : Policy) (r : OpenReports)
    (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop) : Prop where
  openFile : ∀ target, Sim R (nativeOpen.openTarget dir target)
    ((openEffects policy r).openTarget dir target) (fun h model => model = target ∧ B h target)
  unbuffered : ∀ h target, B h target → Sim R (nativeOpen.unbuffered h)
    ((openEffects policy r).unbuffered target) Eq
  policyRead : ∀ h, B h .policy → Sim R (nativeOpen.readPolicy (dir / "policy") h)
    ((openEffects policy r).readPolicy (dir / "policy") .policy)
    (fun x y => x = y ∧ y = stampText policy)
  lock : ∀ h, B h .lock → Sim R (nativeOpen.tryLock h) ((openEffects policy r).tryLock .lock) Eq
  unlock : ∀ h, B h .lock → Sim R (nativeOpen.unlock h) ((openEffects policy r).unlock .lock) Eq
  sync : ∀ h target, B h target → Sim R (nativeOpen.sync h) ((openEffects policy r).sync target) Eq

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
  apply (steps.openFile .lock).bind
  intro h target hx
  obtain ⟨rfl, held⟩ := hx
  apply (steps.lock h held).bind
  intro a b same
  subst b
  split
  · exact Sim.pure ⟨rfl, held⟩
  · exact Sim.throw

private theorem files (steps : OpenSteps dir p r R B) :
    Sim R (openFilesWith nativeOpen dir) (openFilesWith (openEffects p r) dir) (Files B p) := by
  unfold openFilesWith
  apply (steps.openFile .policy).bind
  intro stamp target ht
  obtain ⟨rfl, st⟩ := ht
  apply (steps.policyRead stamp st).bind
  intro text expected eq
  obtain ⟨rfl, eq⟩ := eq
  subst text
  cases p <;> dsimp only [stampText]
  all_goals
    apply (steps.openFile .reader).bind
    intro reader modelReader hr
    obtain ⟨rfl, hr⟩ := hr
    apply (steps.unbuffered reader _ hr).bind
    intro _ _ _
    apply (steps.openFile .writer).bind
    intro writer modelWriter hw
    obtain ⟨rfl, hw⟩ := hw
    apply (steps.unbuffered writer _ hw).bind
    intro _ _ _
  case logOnly => exact Sim.pure ⟨st, rfl, hr, hw, trivial, rfl⟩
  case boundary =>
    apply (steps.openFile .marker0).bind
    intro zero modelZero hz
    obtain ⟨rfl, hz⟩ := hz
    apply (steps.unbuffered zero _ hz).bind
    intro _ _ _
    apply (steps.openFile .marker1).bind
    intro one modelOne ho
    obtain ⟨rfl, ho⟩ := ho
    apply (steps.unbuffered one _ ho).bind
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
    apply (steps.sync _ _ stamp).bind
    intro _ _ _
    apply (steps.openFile .directory).bind
    intro directory role hr
    obtain ⟨rfl, held⟩ := hr
    exact steps.sync _ _ held
  apply set.bind
  intro _ _ _
  exact Sim.pure ⟨lock, reader, writer, markers, policy, rfl, rfl⟩

/-- A terminal result may refer to the contents of a mutable cell in the
world in which that result was actually returned. -/
def SimAt (R : W → OpenImage → Prop) (a : F α) (b : OpenM β)
    (rel : W → α → β → Prop) : Prop :=
  ∀ w s, R w s →
    match a.run w, b.run s with
    | .ok (.ok x) t, .ok (.ok y) u => R t u ∧ rel t x y
    | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => R t u
    | _, _ => False

private theorem Sim.toAt {a : F α} {b : OpenM β} (h : Sim R a b rel) :
    SimAt R a b (fun _ => rel) := by
  intro w s prior
  specialize h w s prior
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases x <;> cases y <;> exact h
  case error.ok x t y u => cases y <;> exact h
  all_goals exact h

private theorem SimAt.bind {a : F α} {b : OpenM β} {f : α → F γ} {g : β → OpenM δ}
    (first : SimAt R a b rel)
    (next : ∀ w s x y, R w s → rel w x y →
      match (f x).run w, (g y).run s with
      | .ok (.ok x) t, .ok (.ok y) u => R t u ∧ out t x y
      | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => R t u
      | _, _ => False) : SimAt R (a >>= f) (b >>= g) out := by
  intro w s prior
  have h := first w s prior
  rw [ExceptT.run_bind, ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | contradiction | exact h | exact next _ _ _ _ h.1 h.2
  case error.ok x t y u => cases y <;> first | contradiction | exact h
  all_goals first | contradiction | exact h

private def CatchRel (rel : α → β → Prop) : Except IO.Error α → Except String β → Prop
  | .ok a, .ok b => rel a b
  | .error _, .error _ => True
  | _, _ => False

private theorem catchCall {a : F α} {b : OpenM β} (together : SimAt R a b rel) :
    SimAt R (liftM ((checked a).toBaseIO)) (SingleFile.attempt b) (fun w => CatchRel (rel w)) := by
  intro w s pre
  have same := together w s pre
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
  case ok.ok x t y u =>
    cases x <;> cases y <;> first | contradiction | exact same | exact ⟨same, trivial⟩
  case error.ok x t y u =>
    cases y <;> first | contradiction | exact ⟨same, trivial⟩
  all_goals contradiction

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

private theorem allocate (runtime : Runtime R) (pair : OpenedTogether B p a b) :
    SimAt R (liftM (installReady a)) (pure b) (Owns runtime B p) := by
  intro w s pre
  obtain ⟨h, ran, assembled⟩ := installReady_run a w
  have cell := runtime.newRef a.phase w s pre
  obtain ⟨frame, saved, held⟩ := runtime.newMutex _ s _ _ cell.1 cell.2
  have lifted : (liftM (installReady a) : F _).run w =
      .ok (.ok h) (Std.BaseMutex.new ((IO.mkRef a.phase : BaseIO Ref) w).state).state := by
    change (match installReady a w with
      | .ok value t => EST.Out.ok (Except.ok value : Except String Handle) t
      | .error e t => EST.Out.error e t) = _
    rw [ran]
  rw [lifted]
  exact ⟨frame, a, pair, _, _, assembled, saved, held⟩


private theorem openBody (steps : OpenSteps dir p r R B) (recovery : WorkerSteps R B r)
    (runtime : Runtime R) :
    SimAt R (openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
      (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
      (fun ready => installReady ready) dir)
      (openExistingWith (openEffects p r) SingleFile.attempt throw (workerEffect r) appendFiles pure dir)
      (Owns runtime B p) := by
  unfold openExistingWith
  apply SimAt.bind (acquire steps).toAt
  intro w s lock role frame hr
  obtain ⟨rfl, held⟩ := hr
  have installed : SimAt R _ _ (Owns runtime B p) :=
    SimAt.bind (f := fun a => liftM (installReady a)) (g := pure) (install steps recovery held).toAt
      (fun w s _ _ h pair => allocate runtime pair w s h)
  apply SimAt.bind (catchCall installed) _ w s frame
  intro w s x y h pair
  cases x <;> cases y
  case ok.ok => exact ⟨h, pair⟩
  case error.error =>
    apply SimAt.bind (catchCall (steps.unlock _ held).toAt) _ w s h
    intro w s _ _ frame _
    exact frame
  all_goals exact False.elim pair


/-- Equal return channels and exact reached disk/ownership under the
two outside-worker writeback lists and primitive schedule of this attempt. -/
theorem openExisting {physical : W → OpenImage → Prop} (steps : OpenSteps dir p r R B) (recovery : WorkerSteps R B r)
    (runtime : Runtime R) (w : W) (initial : OpenImage)
    (entry : R w (settleImage r.beforeWorker initial))
    (exitFrame : ∀ t u, R t u → physical t (settleImage r.afterWorker u)) :
    match SingleFile.openExisting dir w, openExistingModel dir p r initial with
    | .ok h t, .ok (.ok ready) u => physical t u ∧ Owns runtime B p t h ready
    | .error _ t, .ok (.error _) u => physical t u
    | _, _ => False := by
  let a : F Handle := openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
    (fun ready => installReady ready) dir
  let b : OpenM ModelOpened := openExistingWith (openEffects p r) SingleFile.attempt throw
    (workerEffect r) appendFiles pure dir
  let s := settleImage r.beforeWorker initial
  have same := openBody steps recovery runtime w s entry
  change SimAt.match_1 (fun _ _ => Prop) (a.run w) (b.run s) (fun x t y u => R t u ∧ Owns runtime B p t x y) (fun _ t _ u => R t u) (fun _ t _ u => R t u) (fun _ _ => False) at same
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
  case ok.ok x t y u =>
    cases x <;> cases y <;> first | contradiction | exact exitFrame _ _ same | exact ⟨exitFrame _ _ same.1, same.2⟩
  case error.ok x t y u => cases y <;> first | contradiction | exact exitFrame _ _ same
  all_goals contradiction

end WalRecoverySlice.SingleFile.ConcreteRecovery
