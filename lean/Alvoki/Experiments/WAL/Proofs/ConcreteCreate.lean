import Alvoki.Experiments.WAL.Proofs.ConcreteOpen

namespace WalRecoverySlice.SingleFile.ConcreteCreate
open System Persistence ConcreteRecovery

/-- Connect a native returned IO result with the returned branch of the
abstract interpreter. The model's unreturned process interruptions remain
part of the component crash guarantee. -/
def Paired (a : IO α) (b : OpenM β) (w : W) (s : OpenImage)
    (ok : α → β → W → OpenImage → Prop) (fail : IO.Error → String → W → OpenImage → Prop) : Prop :=
  match a w, b.run s with
  | .ok x t, .ok (.ok y) u => ok x y t u
  | .error e t, .ok (.error d) u => fail e d t u
  | _, _ => False

theorem Paired.bind {a : IO α} {b : OpenM β} {f : α → IO γ} {g : β → OpenM δ}
    (one : Paired a b w s mid fail)
    (next : ∀ x y t u, a w = .ok x t → mid x y t u → Paired (f x) (g y) t u ok fail) :
    Paired (a >>= f) (b >>= g) w s ok fail := by
  unfold Paired at *
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a w <;> cases hb : b.run s <;> simp only [ha, hb] at one ⊢
  case ok.ok x t y u => cases y <;> first | contradiction | exact next _ _ _ _ ha one
  case error.ok x t y u => cases y <;> first | contradiction | exact one
  all_goals exact one

theorem Paired.catch {a : IO α} {b : OpenM β} {f : IO.Error → IO α} {g : String → OpenM β}
    (one : Paired a b w s ok err)
    (handler : ∀ e d t u, a w = .error e t → err e d t u → Paired (f e) (g d) t u ok fail) :
    Paired (tryCatchThe IO.Error a f) (tryCatchThe String b g) w s ok fail := by
  unfold Paired at *
  have cv : (tryCatchThe String b g).run s = match b.run s with
    | .ok (.ok x) t => .ok (.ok x) t
    | .ok (.error d) t => (g d).run t
    | .error e t => .error e t := by
    change EStateM.bind b.run _ s = _
    cases run : b.run s with
    | ok value t => cases value <;> simp [EStateM.bind, run] <;> rfl
    | error => simp [EStateM.bind, run]
  have nv : tryCatchThe IO.Error a f w = match a w with
    | .ok x t => .ok x t
    | .error e t => f e t := by
      change EST.tryCatch a f w = _
      unfold EST.tryCatch
      cases a w <;> rfl
  rw [cv, nv]
  cases ha : a w <;> cases hb : b.run s <;> simp only [ha, hb] at one
  case ok.ok x t y u => cases y <;> first | contradiction | exact one
  case error.ok x t y u => cases y <;> first | contradiction | exact handler _ _ _ _ ha one
  all_goals exact one

def Returns (a : IO α) (w : W) (ok : α → W → Prop) (fail : W → Prop) : Prop :=
  match a w with | .ok x t => ok x t | .error _ t => fail t

theorem Returns.bind {a : IO α} {f : α → IO β} (h : Returns a w mid fail)
    (next : ∀ x t, a w = .ok x t → mid x t → Returns (f x) t ok fail) :
    Returns (a >>= f) w ok fail := by
  unfold Returns at *
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases run : a w <;> rw [run] at h
  case ok => exact next _ _ run h
  case error => exact h

def listing (dir : FilePath) : IO (Array String) := do
  return (← Internal.readDirChecked dir).map (·.fileName)

def prepare (dir : FilePath) (p : Policy) : IO Unit :=
  prepareCreateWith IO.userError listing Internal.writeAndSync dir p

/-- The installation starts after this same lock owner successfully
initialized the private directory. -/
def Prepared (dir : FilePath) (p : Policy) (origin : W) (lock : IO.FS.Handle) (w : W) : Prop :=
  ∃ t, LockedAt dir origin lock t ∧ prepare dir p t = .ok () w

inductive WriteStage (dir : FilePath) (p : Policy) (origin : W) : FilePath → ByteArray → W → Prop where
  | stamp : LockedAt dir origin lock t → listing dir t = .ok names u → names.any (· != "lock") = false →
    WriteStage dir p origin (dir / "policy") (stampText p).toUTF8 u
  | segment : WriteStage dir p origin (dir / "policy") (stampText p).toUTF8 t →
    Internal.writeAndSync (dir / "policy") (stampText p).toUTF8 t = .ok () u →
    WriteStage dir p origin (dir / "segment") ByteArray.empty u
  | zero : p = .boundary → WriteStage dir p origin (dir / "segment") ByteArray.empty t →
    Internal.writeAndSync (dir / "segment") ByteArray.empty t = .ok () u →
    WriteStage dir p origin (dir / "commit.0") ⟨(encodeMarker 0 0).toArray⟩ u
  | one : WriteStage dir p origin (dir / "commit.0") ⟨(encodeMarker 0 0).toArray⟩ t →
    Internal.writeAndSync (dir / "commit.0") ⟨(encodeMarker 0 0).toArray⟩ t = .ok () u →
    WriteStage dir p origin (dir / "commit.1") ByteArray.empty u

def Wrote (R : W → OpenImage → Prop) (report : OpenResult Unit) (t : W) : Prop :=
  ∃ u, report = .ok (.ok ()) u ∧ R t u

def Failed (R : W → OpenImage → Prop) (report : OpenResult Unit) (t : W) : Prop :=
  ∃ d u, report = .ok (.error d) u ∧ R t u

/-- Each receipt is for the preceding successful call on this newly created
description. The selected-disk frame on failure can ignore partial private bytes. -/
structure WriteSteps (R : W → OpenImage → Prop) (path : FilePath) (bytes : ByteArray) (w : W)
    (report : OpenResult Unit) where
  pending : W → Prop
  opened : Returns (IO.FS.Handle.mk path .writeNew) w (fun _ t => pending t) (Failed R report)
  buffer : ∀ h t, IO.FS.Handle.mk path .writeNew w = .ok h t → pending t →
    Returns (Internal.disableBuffering h) t (fun _ next => pending next) (Failed R report)
  write : ∀ h t u, IO.FS.Handle.mk path .writeNew w = .ok h t →
    Internal.disableBuffering h t = .ok () u → pending u →
    Returns (h.write bytes) u (fun _ next => pending next) (Failed R report)
  flush : ∀ h t u v, IO.FS.Handle.mk path .writeNew w = .ok h t →
    Internal.disableBuffering h t = .ok () u → h.write bytes u = .ok () v → pending v →
    Returns h.flush v (fun _ next => pending next) (Failed R report)
  sync : ∀ h t u v z, IO.FS.Handle.mk path .writeNew w = .ok h t →
    Internal.disableBuffering h t = .ok () u → h.write bytes u = .ok () v → h.flush v = .ok () z →
    pending z → Returns (Internal.syncHandle h) z (fun _ next => Wrote R report next) (Failed R report)

private theorem writeRun (steps : WriteSteps R path bytes w report) :
    Returns (Internal.writeAndSync path bytes) w (fun _ t => Wrote R report t) (Failed R report) := by
  unfold Internal.writeAndSync Internal.openStream
  apply Returns.bind (mid := fun h u => ∃ t, IO.FS.Handle.mk path .writeNew w = .ok h t ∧
    Internal.disableBuffering h t = .ok () u ∧ steps.pending u)
  · apply steps.opened.bind
    intro h t op pending
    apply (steps.buffer h t op pending).bind
    rintro ⟨⟩ u buf pending
    exact ⟨t, op, buf, pending⟩
  rintro h u _ ⟨t, op, buf, pending⟩
  apply (steps.write h t u op buf pending).bind
  rintro ⟨⟩ v written pending
  apply (steps.flush h t u v op buf written pending).bind
  rintro ⟨⟩ z flushed pending
  exact steps.sync h t u v z op buf written flushed pending

def listModel (dir : FilePath) (r : CreateReports) (path : FilePath) : OpenM (Array String) :=
  if path == dir then unchanged r.listingFault r.names else throw "wrong directory"

structure Steps (R : W → OpenImage → Prop) (B : IO.FS.Handle → OpenTarget → Prop)
    (dir : FilePath) (p : Policy) (r : CreateReports) (origin : W) where
  first : SimResult R (nativeOpen.openTarget dir .lock) ((openEffects p r.opening).openTarget dir .lock)
    (fun h role => role = .lock ∧ B h .lock) origin (emptyCreateImage p)
  lock : ∀ h w s, LockFileAt dir origin h w → B h .lock → R w s →
    SimResult R (nativeOpen.tryLock h) ((openEffects p r.opening).tryLock .lock) Eq w s
  list : ∀ h t s, LockedAt dir origin h t → R t s →
    Paired (Internal.readDirChecked dir) (listModel dir r dir) t s
      (fun entries names u after => entries.map (·.fileName) = names ∧ R u after) (fun _ _ u after => R u after)
  write : ∀ path bytes w s, WriteStage dir p origin path bytes w → R w s →
    WriteSteps R path bytes w ((createWrite dir p r path bytes).run s)
  opening : OpenSteps dir p r.opening R B origin (Prepared dir p origin)
  recovery : WorkerSteps dir R B r.opening origin (Prepared dir p origin)
  runtime : Runtime R
  unlock : ∀ h locked w s, LockedAt dir origin h locked →
    (∃ e, (prepare dir p >>= fun _ => Internal.install dir h) locked = .error e w) →
    R w s → Paired h.unlock ((openEffects p r.opening).unlock .lock) w s
      (fun _ _ t u => R t u) (fun _ _ t u => R t u)

private theorem pairedWrite (steps : Steps R B dir p r origin)
    (stage : WriteStage dir p origin path bytes w) (frame : R w s) :
    Paired (Internal.writeAndSync path bytes) (createWrite dir p r path bytes) w s
      (fun _ _ t u => R t u) (fun _ _ t u => R t u) := by
  have got := writeRun (steps.write path bytes w s stage frame)
  unfold Returns at got
  unfold Paired
  cases run : Internal.writeAndSync path bytes w with
  | ok x t =>
    rw [run] at got
    obtain ⟨u, model, held⟩ := got
    rw [model]
    exact held
  | error e t =>
    rw [run] at got
    obtain ⟨d, u, model, held⟩ := got
    rw [model]
    exact held

private theorem pairedList (steps : Steps R B dir p r origin) (grant : LockedAt dir origin h w) (frame : R w s) :
    Paired (listing dir) (listModel dir r dir) w s (fun x y t u => x = y ∧ R t u) (fun _ _ t u => R t u) := by
  have got := steps.list h w s grant frame
  unfold listing
  unfold Paired at *
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases a : Internal.readDirChecked dir w <;> cases b : (listModel dir r dir).run s <;>
    simp only [a, b] at got
  case ok.ok _ _ y _ => cases y <;> exact got
  case error.ok _ _ y _ => cases y <;> exact got
  all_goals exact got

private theorem preparation (steps : Steps R B dir p r origin)
    (grant : LockedAt dir origin h w) (frame : R w s) :
    Paired (prepare dir p) (prepareCreateWith _root_.id (listModel dir r) (createWrite dir p r) dir p)
      w s (fun _ _ t u => R t u) (fun _ _ t u => R t u) := by
  unfold prepare prepareCreateWith
  apply (pairedList steps grant frame).bind
  rintro names _ t u listed ⟨rfl, frame⟩
  split
  · exact frame
  rename_i empty
  have onlyLock : names.any (· != "lock") = false := by simpa using empty
  have first := WriteStage.stamp (p := p) grant listed onlyLock
  unfold initializeFilesWith
  cases p
  all_goals
    apply (pairedWrite steps first frame).bind
    rintro ⟨⟩ ⟨⟩ t u wrote frame
    have segment := first.segment wrote
    apply (pairedWrite steps segment frame).bind
    rintro ⟨⟩ ⟨⟩ t u wrote frame
  case logOnly => exact frame
  case boundary =>
    have zero := segment.zero rfl wrote
    apply (pairedWrite steps zero frame).bind
    rintro ⟨⟩ ⟨⟩ t u wrote frame
    exact pairedWrite steps (zero.one wrote) frame

private theorem checkedPair {a : F α} {b : OpenM β} (h : At a b w s ok fail) :
    Paired (checked a) b w s ok (fun _ _ t u => fail t u) := by
  unfold At at h
  unfold Paired checked
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases actual : a.run w <;> cases model : b.run s <;> simp only [actual, model] at h
  case ok.ok x _ y _ => cases x <;> cases y <;> exact h
  case error.ok _ _ y _ => cases y <;> exact h
  all_goals exact h

private theorem acquisition (steps : Steps R B dir p r origin) :
    Paired (Internal.acquire dir) (acquireWith (openEffects p r.opening) dir) origin (emptyCreateImage p)
      (fun h role t u => role = .lock ∧ B h .lock ∧ LockedAt dir origin h t ∧ R t u)
      (fun _ _ t u => R t u) := by
  apply checkedPair
  unfold acquireWith
  apply At.bind (mid := fun h role t u => role = .lock ∧ B h .lock ∧ LockFileAt dir origin h t ∧ R t u)
  · have leaf := steps.first
    unfold At SimResult at *
    cases a : (nativeOpen.openTarget dir .lock).run origin <;>
      cases b : ((openEffects p r.opening).openTarget dir .lock).run (emptyCreateImage p) <;>
      simp only [a, b] at leaf
    case ok.ok x t y u =>
      cases x <;> cases y <;> first | exact leaf | exact ⟨leaf.2.1, leaf.2.2, a, leaf.1⟩
    case error.ok _ _ y _ => cases y <;> exact leaf
    all_goals exact leaf
  rintro h _ w s ⟨rfl, bound, fresh, frame⟩
  apply At.bind (mid := fun x y t u => x = y ∧ (nativeOpen.tryLock h).run w = .ok (.ok x) t ∧ R t u)
  · have leaf := steps.lock h w s fresh bound frame
    unfold At SimResult at *
    cases a : (nativeOpen.tryLock h).run w <;> cases b : ((openEffects p r.opening).tryLock .lock).run s <;>
      simp only [a, b] at leaf
    case ok.ok x _ y _ =>
      cases x <;> cases y <;> first | exact leaf | exact ⟨leaf.2, rfl, leaf.1⟩
    case error.ok _ _ y _ => cases y <;> exact leaf
    all_goals exact leaf
  rintro x _ t u ⟨rfl, ran, frame⟩
  cases x
  · exact frame
  · exact ⟨rfl, bound, ⟨w, fresh, ran⟩, frame⟩

private theorem installed (steps : Steps R B dir p r origin) (bound : B fd .lock)
    (grant : LockedAt dir origin fd locked) (prepared : prepare dir p locked = .ok () w) (frame : R w s) :
    Paired (Internal.install dir fd) (installWith (openEffects p r.opening) (workerEffect r.opening) appendFiles dir .lock)
      w s (fun h ready t u => R t u ∧ Owns steps.runtime B p dir origin t h ready)
      (fun _ _ t u => R t u) := by
  have source := installFrom steps.opening steps.recovery bound ⟨locked, grant, prepared⟩ frame
  have checked : Paired (checked (installWith nativeOpen recoverNative appendFiles dir fd))
      (installWith (openEffects p r.opening) (workerEffect r.opening) appendFiles dir .lock) w s
      (fun a b t u => R t u ∧ OpenedTogether B p a b ∧ a.lock = fd) (fun _ _ t u => R t u) := by
    apply checkedPair
    unfold At
    unfold SimResult at source
    cases a : (installWith nativeOpen recoverNative appendFiles dir fd).run w <;>
      cases b : (installWith (openEffects p r.opening) (workerEffect r.opening) appendFiles dir .lock).run s <;>
      simp only [a, b] at source
    case ok.ok x _ y _ => cases x <;> cases y <;> exact source
    case error.ok _ _ y _ => cases y <;> exact source
    all_goals exact source
  unfold Internal.install
  have right {α} (m : OpenM α) : (m >>= pure) = m := by
    funext x
    change EStateM.bind m.run _ x = m.run x
    cases ran : m.run x with
    | error => simp [EStateM.bind, ran]
    | ok v t => cases v <;> simp [EStateM.bind, ran, ExceptT.bindCont] <;> rfl
  rw [← right (installWith (openEffects p r.opening) (workerEffect r.opening) appendFiles dir .lock)]
  apply checked.bind
  rintro a b t u _ ⟨frame, pair, rfl⟩
  obtain ⟨h, ran, assembled⟩ := installReady_run a t
  have cell := steps.runtime.newRef a.phase t u frame
  obtain ⟨finished, saved, held⟩ := steps.runtime.newMutex _ u _ _ cell.1 cell.2
  unfold Paired
  rw [ran]
  exact ⟨finished, a, pair, _, _, locked, assembled, saved, held, grant⟩

/-- Public creation, with no authority to publish partial files. The same
actual newly granted descriptor becomes the lock retained by the successful
handle. Both possible reports from the failure-path unlock keep the frame. -/
theorem create (steps : Steps R B dir p r origin) :
    match SingleFile.create dir p origin, createModel dir p r with
    | .ok h t, .ok (.ok ready) u => R t u ∧ Owns steps.runtime B p dir origin t h ready
    | .error _ t, .ok (.error _) u => R t u
    | _, _ => False := by
  let model := createWith (error := String) _root_.id (acquireWith (openEffects p r.opening) dir)
    (openEffects p r.opening).unlock (listModel dir r) (createWrite dir p r)
    (installWith (openEffects p r.opening) (workerEffect r.opening) appendFiles) dir p
  have paired : Paired (SingleFile.create dir p) model origin (emptyCreateImage p)
    (fun h ready t u => R t u ∧ Owns steps.runtime B p dir origin t h ready)
    (fun _ _ t u => R t u) := by
    unfold model SingleFile.create createWith
    apply (acquisition steps).bind
    rintro h _ t s _ ⟨rfl, bound, grant, frame⟩
    apply Paired.catch (err := fun _ _ w u => R w u)
    · apply (preparation steps grant frame).bind
      rintro ⟨⟩ ⟨⟩ w u prepared frame
      exact installed steps bound grant prepared frame
    · intro e d w u failed frame
      apply Paired.bind (mid := fun _ _ t u => R t u)
      · apply (steps.unlock h t w u grant ⟨e, failed⟩ frame).catch
        intro _ _ t u _ frame
        exact frame
      · intro _ _ t u _ frame
        exact frame
  have modeled : createModel dir p r = model.run (emptyCreateImage p) := rfl
  rw [modeled]
  unfold Paired at paired
  cases a : SingleFile.create dir p origin <;> cases b : model.run (emptyCreateImage p) <;>
    simp only [a, b] at paired
  case ok.ok _ _ y _ => cases y <;> exact paired
  case error.ok _ _ y _ => cases y <;> exact paired
  all_goals exact paired

end WalRecoverySlice.SingleFile.ConcreteCreate
