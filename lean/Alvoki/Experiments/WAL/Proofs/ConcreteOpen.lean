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

/-- The exact lock description and world returned by the first issued primitive. -/
def LockFileAt (dir : FilePath) (w : W) (h : IO.FS.Handle) (t : W) : Prop :=
  (nativeOpen.openTarget dir .lock).run w = .ok (.ok h) t

/-- A granted lock on this invocation's freshly opened description. -/
def LockedAt (dir : FilePath) (w : W) (h : IO.FS.Handle) (t : W) : Prop :=
  ∃ opened, LockFileAt dir w h opened ∧ (nativeOpen.tryLock h).run opened = .ok (.ok true) t

/-- The policy handle passed to the first namespace barrier is the one
in the actual file set whose decoder returned at this world. -/
def WorkerDone (dir : FilePath) (origin : W) (stamp : IO.FS.Handle) (finish : W) : Prop :=
  ∃ lock locked, LockedAt dir origin lock locked ∧ ∃ files began,
    (openFilesWith nativeOpen dir).run locked = .ok (.ok files) began ∧ files.stamp = stamp ∧
    ∃ decoded, (recoverNative files.policy files.reader files.writer files.markers).run began =
      .ok (.ok decoded) finish

inductive BufferNext : Policy → OpenTarget → OpenTarget → Prop where
  | writer : BufferNext p .reader .writer
  | marker0 : BufferNext .boundary .writer .marker0
  | marker1 : BufferNext .boundary .marker0 .marker1

def BufferTarget : OpenTarget → Bool
  | .reader | .writer | .marker0 | .marker1 => true
  | _ => false

/-- Each open is attached to the previous successful operation in this
particular invocation. A returned primitive error supplies no next stage. -/
inductive FileStage (dir : FilePath) (p : Policy) (origin : W) : OpenTarget → W → Prop where
  | policy : LockedAt dir origin lock t → FileStage dir p origin .policy t
  | reader : FileStage dir p origin .policy w →
      (nativeOpen.openTarget dir .policy).run w = .ok (.ok h) u →
      (nativeOpen.readPolicy (dir / "policy") h).run u = .ok (.ok (stampText p)) t →
      FileStage dir p origin .reader t
  | buffered : FileStage dir p origin target w → BufferNext p target next →
      (nativeOpen.openTarget dir target).run w = .ok (.ok h) u →
      (nativeOpen.unbuffered h).run u = .ok (.ok ()) t → FileStage dir p origin next t
  | directory : WorkerDone dir origin stamp w →
      (nativeOpen.sync stamp).run w = .ok (.ok ()) t → FileStage dir p origin .directory t

def Fresh (dir : FilePath) (p : Policy) (origin : W) (target : OpenTarget)
    (h : IO.FS.Handle) (t : W) : Prop :=
  ∃ w, FileStage dir p origin target w ∧ (nativeOpen.openTarget dir target).run w = .ok (.ok h) t

private theorem Fresh.reader (fresh : Fresh dir p origin .policy stamp t)
    (read : (nativeOpen.readPolicy (dir / "policy") stamp).run t = .ok (.ok (stampText p)) v) :
    FileStage dir p origin .reader v := by
  obtain ⟨_, stage, opened⟩ := fresh
  exact .reader stage opened read

private theorem Fresh.buffered (fresh : Fresh dir p origin target h t) (step : BufferNext p target next)
    (run : (nativeOpen.unbuffered h).run t = .ok (.ok ()) v) : FileStage dir p origin next v := by
  obtain ⟨_, stage, opened⟩ := fresh
  exact .buffered stage step opened run

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
    (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop) (origin : W) : Prop where
  openFile : ∀ target w s, FileStage dir policy origin target w → R w s →
    SimResult R (nativeOpen.openTarget dir target) ((openEffects policy r).openTarget dir target)
      (fun h model => model = target ∧ B h target) w s
  unbuffered : ∀ h target w s, BufferTarget target = true → Fresh dir policy origin target h w → B h target → R w s →
    SimResult R (nativeOpen.unbuffered h) ((openEffects policy r).unbuffered target) Eq w s
  policyRead : ∀ h w s, Fresh dir policy origin .policy h w → B h .policy → R w s →
    SimResult R (nativeOpen.readPolicy (dir / "policy") h)
      ((openEffects policy r).readPolicy (dir / "policy") .policy)
      (fun x y => x = y ∧ y = stampText policy) w s
  syncPolicy : ∀ h w s, WorkerDone dir origin h w → B h .policy → R w s →
    SimResult R (nativeOpen.sync h) ((openEffects policy r).sync .policy) Eq w s
  syncDirectory : ∀ h w s, Fresh dir policy origin .directory h w → B h .directory → R w s →
    SimResult R (nativeOpen.sync h) ((openEffects policy r).sync .directory) Eq w s

theorem OpenSteps.bindFreshOpen (steps : OpenSteps dir p r R B origin)
    (stage : FileStage dir p origin target w) (frame : R w s)
    {f : IO.FS.Handle → F α} {g : OpenTarget → OpenM β}
    (next : ∀ h t u, Fresh dir p origin target h t → B h target → R t u →
      SimResult R (f h) (g target) out t u) :
    SimResult R (nativeOpen.openTarget dir target >>= f) ((openEffects p r).openTarget dir target >>= g) out w s := by
  apply (steps.openFile target w s stage frame).bind
  rintro h _ t u actual _ post ⟨rfl, bound⟩
  exact next _ _ _ ⟨w, stage, actual⟩ bound post

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

/-- A successful barrier followed by a reported failure on the same live
description rules out a reusable no-fault sync law. Only the barrier reached
in this attempt is interpreted against its selected report. -/
theorem stampSync_notReusable (p : Policy) (h : IO.FS.Handle)
    (entry : R w s)
    (first : (nativeOpen.sync h).run w = .ok (.ok ()) t)
    (later : (nativeOpen.sync h).run t = .error e u) :
    ¬ Sim R (nativeOpen.sync h) ((openEffects p {}).sync .policy) Eq := by
  intro reused
  have model (v : OpenImage) : ((openEffects p {}).sync .policy).run v =
      .ok (.ok ()) {v with policyDurable := true} := rfl
  have step := reused w s entry
  rw [first, model] at step
  have next := reused t _ step.1
  rw [later, model] at next
  exact next

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

private theorem files (steps : OpenSteps dir p r R B origin)
    (locked : LockedAt dir origin lock start) (initial : R start model) :
    SimResult R (openFilesWith nativeOpen dir) (openFilesWith (openEffects p r) dir) (Files B p) start model := by
  unfold openFilesWith
  apply steps.bindFreshOpen (.policy locked) initial
  intro stamp w s fresh st frame
  apply (steps.policyRead stamp w s fresh st frame).bind
  rintro text _ _ _ read _ frame ⟨rfl, rfl⟩
  have reached := fresh.reader read
  cases p <;> dsimp only [stampText]
  all_goals
    apply steps.bindFreshOpen reached frame
    intro reader w s fresh hr frame
    apply (steps.unbuffered reader .reader w s rfl fresh hr frame).bind
    rintro _ _ _ _ buffered _ frame rfl
    apply steps.bindFreshOpen (fresh.buffered .writer buffered) frame
    intro writer w s fresh hw frame
    apply (steps.unbuffered writer .writer w s rfl fresh hw frame).bind
    rintro _ _ _ _ writerReady _ frame rfl
  case logOnly => exact ⟨frame, st, rfl, hr, hw, trivial, rfl⟩
  case boundary =>
    apply steps.bindFreshOpen (fresh.buffered .marker0 writerReady) frame
    intro zero w s fresh hz frame
    apply (steps.unbuffered zero .marker0 w s rfl fresh hz frame).bind
    rintro _ _ _ _ synced _ frame rfl
    apply steps.bindFreshOpen (fresh.buffered .marker1 synced) frame
    intro one w s fresh ho frame
    apply (steps.unbuffered one .marker1 w s rfl fresh ho frame).bind
    rintro _ _ _ _ _ _ frame rfl
    exact ⟨frame, st, rfl, hr, hw, ⟨hz, ho⟩, rfl⟩

/-- Each contract observes one instruction in this particular worker's
issued prefix, starting from its actual acquired descriptions. -/
structure WorkerSteps (dir : FilePath) (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop)
    (r : OpenReports) (origin : W) : Prop where
  issued : ∀ {a b p lock start began base}, Files B p a b → LockedAt dir origin lock start →
    (openFilesWith nativeOpen dir).run start = .ok (.ok a) began → R began base →
    RecoveryOps (fun w i => R w {base with image := i}) (recoveryOps nativeRecovery a.reader a.markers)
      (scheduledOps (ops r.worker) r.writebacks) p began base.image

private theorem live_settle (files : List WalFile) (i : Image) :
    (settleFiles files i).data.live = i.data.live := by
  induction files generalizing i with
  | nil => rfl
  | cons f fs ih =>
    change (settleFiles fs (f.settle i)).data.live = _
    rw [ih]
    cases f <;> rfl

private theorem scheduledReadModel (effects : Effects) (schedule : WritebackSchedule) :
    ReadModel (scheduledOps (ops effects) schedule) where
  read i bytes u ok := by
    let j := settleFiles schedule.dataRead i
    change EStateM.Result.ok (if effects.readDataError then Except.error "data read error" else Except.ok j.data.live) j =
      EStateM.Result.ok (Except.ok bytes) u at ok
    cases err : effects.readDataError <;> simp [err] at ok
    rw [← ok.2, ok.1]
  marker slot i value u ok := by
    let j := settleFiles (schedule.markerSync slot) i
    change (effects.markerSync slot).syncResult j (j.marker slot) (j.withMarker slot) = _ at ok
    rcases a : effects.markerSync slot with abort | abort
    · cases abort <;> simp [a, Primitive.syncResult, Abort.result] at ok
    · cases abort with
      | some e => cases e <;> simp [a, Primitive.syncResult, Abort.result] at ok
      | none =>
        simp [a, Primitive.syncResult] at ok
        rw [← ok]
        unfold Image.withMarker
        split <;> exact live_settle _ _
theorem worker (steps : WorkerSteps dir R B r origin) (files : Files B p a b)
    (locked : LockedAt dir origin lock start) (opened : (openFilesWith nativeOpen dir).run start = .ok (.ok a) w)
    (pre : R w base) : SimResult R (recoverNative a.policy a.reader a.writer a.markers)
      (workerEffect r b.policy b.reader b.writer b.markers) Eq w base := by
  have schedule := steps.issued files locked opened pre
  obtain ⟨_, pol, _, _, _, rfl⟩ := files
  rw [pol]
  have obs := reopen schedule (scheduledReadModel _ _) pre
  rw [← recoverScheduled_eq] at obs
  change At (recoverNative p a.reader a.writer a.markers) (recoverScheduled r.worker r.writebacks p)
    w base.image _ _ at obs
  unfold SimResult
  unfold At at obs
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

private theorem install (steps : OpenSteps dir p r R B origin) (recovery : WorkerSteps dir R B r origin)
    (lock : B h .lock) (locked : LockedAt dir origin h start) (initial : R start model) :
    SimResult R (installWith nativeOpen recoverNative appendFiles dir h)
      (installWith (openEffects p r) (workerEffect r) appendFiles dir .lock) (fun a b => OpenedTogether B p a b ∧ a.lock = h) start model := by
  unfold installWith
  apply (files steps locked initial).bind
  intro a b began base opened _ frame pair
  have decoded : SimResult R (recoverNative a.policy a.reader a.writer a.markers)
      (workerEffect r b.policy b.reader b.writer b.markers) Eq began base := worker recovery pair locked opened frame
  apply decoded.bind
  rintro decoded _ t u ran _ frame rfl
  have done : WorkerDone dir origin a.stamp t := ⟨h, start, locked, a, began, opened, rfl, decoded, ran⟩
  obtain ⟨stamp, policy, reader, writer, markers, rfl⟩ := pair
  have set : SimResult R (settleWith nativeOpen dir a.stamp)
      (settleWith (openEffects p r) dir .policy) Eq t u := by
    unfold settleWith
    apply (steps.syncPolicy a.stamp t u done stamp frame).bind
    rintro _ _ _ _ sync _ frame rfl
    apply steps.bindFreshOpen (.directory done sync) frame
    intro directory w s fresh held frame
    exact steps.syncDirectory directory w s fresh held frame
  apply set.bind
  rintro _ _ _ _ _ _ frame rfl
  exact ⟨frame, ⟨lock, reader, writer, markers, policy, rfl, rfl⟩, rfl⟩

private theorem SimResult.atPost {a : F α} {b : OpenM β} (h : SimResult R a b rel w s) : At a b w s (fun x y t u => R t u ∧ rel x y) R := by
  have post := h
  unfold SimResult at post
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
    (p : Policy) (dir : FilePath) (origin w : W) (h : Handle) (ready : ModelOpened) : Prop :=
  ∃ a : ActualOpened, OpenedTogether B p a ready ∧ ∃ ref mutex locked,
    h.Assembled a.policy ref mutex ∧ runtime.cell w ref a.phase ∧ runtime.mutex w mutex ∧
      LockedAt dir origin a.lock locked

private def installActual (dir : FilePath) (h : IO.FS.Handle) : F Handle :=
  installWith nativeOpen recoverNative appendFiles dir h >>= fun a => liftM (Internal.installReady a)

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
  /-- On return from this failed installation, the last local lock
  description goes out of scope, including when unlock reports an error. -/
  drop : ∀ h t u, Unwinding dir w h t → B h .lock → R t u →
    At (nativeOpen.unlock h) ((openEffects p r).unlock .lock) t u
      (fun _ _ t' u' => physical t' (settleImage r.afterWorker u'))
      (fun t' u' => physical t' (settleImage r.afterWorker u'))
  allocated : ∀ t u ref phase, R t u → rt.cell t ref phase →
    physical (Std.BaseMutex.new t).state (settleImage r.afterWorker u)

private theorem allocate (rt : Runtime R) (pair : OpenedTogether B p a b)
    (granted : LockedAt dir w a.lock locked) (frame : R t u)
    (boundary : Boundaries dir p r R B rt w initial phys) :
    At (liftM (Internal.installReady a)) (pure b) t u
      (fun h ready t' u' => phys t' (settleImage r.afterWorker u') ∧ Owns rt B p dir w t' h ready) R := by
  obtain ⟨h, ran, assembled⟩ := installReady_run a t
  have cell := rt.newRef a.phase t u frame
  obtain ⟨frame, saved, held⟩ := rt.newMutex _ u _ _ cell.1 cell.2
  have lifted : (liftM (Internal.installReady a) : F _).run t =
      .ok (.ok h) (Std.BaseMutex.new ((IO.mkRef a.phase : BaseIO Ref) t).state).state := by
    change (match Internal.installReady a t with
      | .ok value t => EST.Out.ok (Except.ok value : Except String Handle) t
      | .error e t => EST.Out.error e t) = _
    rw [ran]
  unfold At
  rw [lifted]
  exact ⟨boundary.allocated _ u _ _ cell.1 cell.2, a, pair, _, _, locked, assembled, saved, held, granted⟩

private theorem At.trace {a : F α} {b : OpenM β} (h : At a b w s ok fail) :
    At a b w s (fun x y t u => ok x y t u ∧ a.run w = .ok (.ok x) t) fail := by
  unfold At at *
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | exact h | exact ⟨h, rfl⟩
  case error.ok x t y u => cases y <;> exact h
  all_goals exact h

private theorem openBody (steps : OpenSteps dir p r R B w) (recovery : WorkerSteps dir R B r w)
    (rt : Runtime R) (edge : Boundaries dir p r R B rt w initial phys) :
    At (openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
      (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
      (fun ready => Internal.installReady ready) dir)
      (openExistingWith (openEffects p r) SingleFile.attempt throw (workerEffect r) appendFiles pure dir)
      w (settleImage r.beforeWorker initial)
      (fun h ready t u => phys t (settleImage r.afterWorker u) ∧ Owns rt B p dir w t h ready)
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
  have installed := ((install steps recovery held lockRun frame).atPost).bind
    (f := fun a => liftM (Internal.installReady a)) (g := pure)
    (fun _ _ _ _ info => allocate rt info.2.1 (info.2.2.symm ▸ lockRun) info.1 edge)
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

theorem openExisting {physical : W → OpenImage → Prop} (steps : OpenSteps dir p r R B w)
    (recovery : WorkerSteps dir R B r w) (rt : Runtime R) (initial : OpenImage)
    (edge : Boundaries dir p r R B rt w initial physical) :
    match SingleFile.openExisting dir w, openExistingModel dir p r initial with
    | .ok h t, .ok (.ok ready) u => physical t u ∧ Owns rt B p dir w t h ready
    | .error _ t, .ok (.error _) u => physical t u
    | _, _ => False := by
  let a : F Handle := openExistingWith nativeOpen (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO Handle)) recoverNative appendFiles
    (fun ready => Internal.installReady ready) dir
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

theorem scan (steps : ScanSteps R rt) (owned : Owns rt B p dir origin w h ready) (image : R w u) :
    ∃ t, SingleFile.scan h w = .ok ready.recovered.batches t ∧
      R t u ∧ Owns rt B p dir origin t h ready := by
  obtain ⟨a, pair, cell, mutex, locked, bound, ref, held, granted⟩ := owned
  obtain ⟨frame, held, ref⟩ := steps.lock _ _ _ _ _ image held ref
  obtain ⟨got, frame, held, ref⟩ := steps.read _ _ _ _ _ frame held ref
  have eq := scan_active_run bound w (got.trans pair.phase)
  obtain ⟨frame, held, ref⟩ := steps.unlock _ _ _ _ _ frame held ref
  exact ⟨_, pair.batches ▸ eq, frame, a, pair, cell, mutex, locked, bound, ref, held, granted⟩

end WalRecoverySlice.SingleFile.ConcreteRecovery
