import Alvoki.Experiments.WAL.Proofs.ConcreteRecovery

namespace WalRecoverySlice.SingleFile.ConcreteRecovery
open Persistence System

private abbrev Ref := IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle))
private abbrev ModelOpened := Opened OpenTarget (AppendFiles OpenTarget)
private abbrev ActualOpened := Opened IO.FS.Handle (AppendFiles IO.FS.Handle)

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

end WalRecoverySlice.SingleFile.ConcreteRecovery
