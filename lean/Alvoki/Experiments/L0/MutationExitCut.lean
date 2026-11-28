import Alvoki.Experiments.L0.InterruptedMutation
import Alvoki.Experiments.L0.NativeMutation

namespace ExperimentalL0.MutationExitCut
open System Lifecycle NativeScope
open NativeRead (Footprint tableNamespace)
open NativeMutationScope (Retry Reopens)
open WalRecoverySlice.SingleFile (Handle)
open WalRecoverySlice.Segmented.Native (Store PhaseMemory)

/-- Ordered primitive calls after the WAL returned. Unlock is converted to
BaseIO so both reported outcomes lead to the same remaining finalizers. -/
inductive Tail where
  | done
  | call {α : Type} (op : BaseIO α) (next : α → Tail)

def Tail.run : Tail → BaseIO Unit
  | .done => pure ()
  | .call op next => do (next (← op)).run

noncomputable def child (h : Handle) (next : Tail) : Tail :=
  let cell := h.bindings.choose
  let mutex := h.bindings.choose_spec.choose
  let leave := Tail.call mutex.unlock (fun _ => next)
  let release := fun (fd : IO.FS.Handle) =>
    Tail.call (cell.set .closed) (fun _ => .call fd.unlock.toBaseIO (fun _ => leave))
  .call mutex.lock fun _ => .call cell.get fun
    | .closed => leave
    | .active fd _ _ _ | .poisoned fd => release fd

noncomputable def walClose (h : Wal) (next : Tail) : Tail :=
  let cell := h.parts.choose
  let mutex := h.parts.choose_spec.choose
  let leave := Tail.call mutex.unlock (fun _ => next)
  let release := fun (s : Store) =>
    let unlock := Tail.call s.lock.unlock.toBaseIO (fun _ => leave)
    Tail.call (s.active.swap none) fun
      | none => unlock
      | some (_, ch) => child ch unlock
  .call mutex.lock fun _ => .call (cell.swap .closed) fun
    | .closed => leave
    | .ready s _ | .poisoned s => release s

noncomputable def close (ref : Ref) (next : Tail) : Tail :=
  .call (ref.swap .offline) fun old =>
    match old.wal with
    | none => next
    | some wal => walClose wal next

/-- The outer close always runs. A reported WAL error additionally closes
the current phase in the mutation's own error handler. -/
noncomputable def suffix (ref : Ref) (lock : IO.FS.Handle) (next : Session) (accepted : Bool) : Tail :=
  let outer := close ref (.call lock.unlock.toBaseIO (fun _ => .done))
  if accepted then .call ref.get fun phase =>
    match phase.publish next with
    | some published => .call (ref.swap published) (fun _ => outer)
    | none => close ref outer
  else close ref outer

private theorem call_run (op : BaseIO α) (next : α → Tail) (w : W) :
    (Tail.call op next).run w = (next (op w).val).run (op w).state := by rw [Tail.run]; rfl

private theorem child_run (h : Handle) (k : Tail) (w : W) :
    (child h k).run w = k.run ((WalRecoverySlice.SingleFile.close h).toBaseIO w).state := by
  let cell := h.bindings.choose
  let mutex := h.bindings.choose_spec.choose
  have binds : h.Binds cell mutex := h.bindings.choose_spec.choose_spec
  rw [EIO.toBaseIO, WalRecoverySlice.SingleFile.close_run binds]
  unfold child
  simp only [call_run]
  cases ph : ((h.bindings.choose.get : BaseIO _) (h.bindings.choose_spec.choose.lock w).state).val with
  | closed => simp only [cell, mutex, call_run]
  | active fd files pos bs | poisoned fd =>
    simp only [cell, mutex, call_run]
    cases op : fd.unlock ((cell.set .closed : BaseIO Unit) ((cell.get : BaseIO _) (mutex.lock w).state).state).state <;>
      simp only [cell, mutex] at op <;> simp only [EIO.toBaseIO, op]

private def guarded (m : Std.BaseMutex) (a : IO Unit) : IO Unit := do
  m.lock
  try a finally m.unlock

private theorem guarded_run (m : Std.BaseMutex) (a : IO Unit) (w : W) :
    ((guarded m a).toBaseIO w).state = (m.unlock (a.toBaseIO (m.lock w).state).state).state := by
  unfold guarded
  have lift (f : BaseIO Unit) (w : W) : (liftM f : IO Unit) w = .ok (f w).val (f w).state := rfl
  simp only [EIO.toBaseIO, Bind.bind, instMonadEIO._aux_13, EST.bind, tryFinally,
    tryFinally', MonadFinally.tryFinally', instMonadFinallyEIO._aux_1, Functor.map, instMonadEIO._aux_1, lift]
  cases a (m.lock w).state <;> rfl

private theorem release_state (s : Store) (w : W) :
    (s.release.toBaseIO w).state =
      let taken := (s.active.swap none : BaseIO _) w
      let v := match taken.val with
        | none => taken.state
        | some (_, h) => ((WalRecoverySlice.SingleFile.close h).toBaseIO taken.state).state
      (s.lock.unlock.toBaseIO v).state := by
  open WalRecoverySlice.Segmented.Native in
    simp only [Store.release, releaseWith, cleanupOnError, Store.closeChild, closeChildWith,
      Bind.bind, instMonadEIO._aux_13, EST.bind, tryCatchThe, MonadExceptOf.tryCatch,
      instMonadExceptOfEIO._aux_3, EST.tryCatch, EIO.toBaseIO]
  let taken := (s.active.swap none : BaseIO _) w
  have get : (s.active.swap none : IO _) w = .ok taken.val taken.state := rfl
  rw [get]
  simp only [← show taken = (s.active.swap none : BaseIO _) w from rfl]
  cases b : taken.val with
  | none => cases rep : s.lock.unlock taken.state <;> simp [Pure.pure, instMonadEIO._aux_5, EST.pure, rep]
  | some pair =>
    obtain ⟨id,h⟩ := pair
    cases child : WalRecoverySlice.SingleFile.close h taken.state <;>
      simp [child, Pure.pure, instMonadEIO._aux_5, EST.pure] <;>
      rename_i v <;> cases rep : s.lock.unlock v <;>
      simp [throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw]

private theorem wal_run (h : Wal) (k : Tail) (w : W) :
    (walClose h k).run w = k.run ((WalRecoverySlice.Segmented.Native.close h).toBaseIO w).state := by
  let cell := h.parts.choose
  let mutex := h.parts.choose_spec.choose
  have eq (cell) (mutex) (parts : h.Parts cell mutex) :
      WalRecoverySlice.Segmented.Native.close h = guarded mutex
        (WalRecoverySlice.Segmented.Native.closeWith cell.swap Store.release) := by
    obtain ⟨rfl,rfl⟩ := parts
    rfl
  rw [eq cell mutex h.parts.choose_spec.choose_spec, guarded_run]
  let locked := (mutex.lock w).state
  let got := (cell.swap .closed : BaseIO _) locked
  have taken : (cell.swap .closed : IO _) locked = .ok got.val got.state := rfl
  unfold walClose
  simp only [EIO.toBaseIO, WalRecoverySlice.Segmented.Native.closeWith, Bind.bind, instMonadEIO._aux_13, EST.bind,
    ← show locked = (mutex.lock w).state from rfl, taken, call_run]
  generalize origin : ((cell.swap .closed : BaseIO _) (mutex.lock w).state).val = phase
  cases phase with
  | closed => simp [got, locked, cell, mutex] at *; simp [Pure.pure, instMonadEIO._aux_5, EST.pure, call_run]
  | ready s session | poisoned s =>
    simp only [got, locked, cell, mutex] at origin ⊢
    have release := release_state s got.state
    simp only [EIO.toBaseIO, got, locked, cell, mutex] at release
    simp only [call_run, release]
    split <;> simp_all only [child_run, call_run, EIO.toBaseIO]

private theorem close_state (r : Ref) (k : Tail) (w : W) :
    (close r k).run w = k.run (((Native.phaseCell r).close WalRecoverySlice.Segmented.Native.close).toBaseIO w).state := by
  unfold close
  rw [call_run, EIO.toBaseIO, close_run]
  cases b : ((r.swap .offline : BaseIO _) w).val.wal with
  | none => rfl
  | some wal => exact wal_run wal k _

private theorem finish_state (a : IO α) (b : IO Unit) (w : W) :
    ((finish (ε := IO.Error) a b).toBaseIO w).state = (b.toBaseIO (a.toBaseIO w).state).state := by
  rw [EIO.toBaseIO, finish_io]
  dsimp only
  cases (a.toBaseIO w).val <;> cases (b.toBaseIO (a.toBaseIO w).state).val <;> rfl

private theorem outer_state (r : Ref) (lock : IO.FS.Handle) (w : W) :
    ((close r (.call lock.unlock.toBaseIO (fun _ => .done))).run w).state =
      ((finish (ε := IO.Error) ((Native.phaseCell r).close WalRecoverySlice.Segmented.Native.close)
        lock.unlock).toBaseIO w).state := by
  rw [finish_state, close_state, call_run, Tail.run]
  rfl

private theorem publish_state (r : Ref) (lock : IO.FS.Handle) (next : Session) (w : W) :
    ((suffix r lock next true).run w).state =
      ((finish (ε := IO.Error) ((Native.phaseCell r).close WalRecoverySlice.Segmented.Native.close) lock.unlock).toBaseIO
        (WalRecoverySlice.Segmented.Native.returnedWorld (NativeWrite.afterWrite r (.ok next w)))).state := by
  simp only [suffix, ↓reduceIte, call_run, NativeWrite.afterWrite]
  simp only [Cell.publish, Native.phaseCell, Bind.bind, instMonadEIO._aux_13, EST.bind, read_io]
  cases choice : ((r.get : BaseIO _) w).val.publish next with
  | none =>
    simp only [throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw,
      WalRecoverySlice.Segmented.Native.returnedWorld, close_state, Tail.run, finish_state]
    rfl
  | some stage =>
    simp only [Pure.pure, instMonadEIO._aux_5, call_run,
      WalRecoverySlice.Segmented.Native.returnedWorld]
    apply outer_state

/-- Every updating callback uses this suffix after the store action has returned.
The error arm ignores the proposed next session and runs both finalizers. -/
noncomputable def afterStore (ref : Ref) (lock : IO.FS.Handle) (fallback : Session) :
    EST.Out IO.Error IO.RealWorld Session → Tail
  | .ok next _ => suffix ref lock next true
  | .error _ _ => suffix ref lock fallback false

theorem afterWrite_state {body : IO Unit} (result : EST.Out IO.Error IO.RealWorld Session)
    (ran : body callback = NativeWrite.afterWrite ref result) (lock : IO.FS.Handle) (fallback : Session) :
    ((afterStore ref lock fallback result).run
      (WalRecoverySlice.Segmented.Native.returnedWorld result)).state =
    WalRecoverySlice.Segmented.Native.returnedWorld (finish (ε := IO.Error) body
      (finish (ε := IO.Error) ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close)
        lock.unlock) callback) := by
  have state {α : Type} (a : IO α) (w : W) :
      WalRecoverySlice.Segmented.Native.returnedWorld (a w) = (a.toBaseIO w).state := by
    cases eq : a w <;> simp [EIO.toBaseIO, eq, WalRecoverySlice.Segmented.Native.returnedWorld]
  rw [state (finish _ _), finish_state, ← state body callback, ran]
  cases result with
  | ok next t => exact publish_state ref lock next t
  | error e t =>
    simp only [afterStore, suffix, Bool.false_eq_true, ↓reduceIte, NativeWrite.afterWrite,
      WalRecoverySlice.Segmented.Native.returnedWorld, close_state]
    rw [finish_state, call_run, Tail.run]
    rfl

/-- The last world on the primitive path is the world where withOpen would
deliver its reply. Intermediate calls are ordered by their actual results. -/
theorem suffix_state (p : InterruptedMutation.Prefix path root start)
    (invoked : Native.withOpen path (fun h => Native.mutation h change) start =
      finish (ε := IO.Error) (Native.mutation handle change)
        (finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close)
          p.lock.unlock) p.callback)
    (ran : Native.mutation handle change p.callback = NativeWrite.afterWrite p.ref
      (match WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue with
      | .ok _ t => .ok {p.session with mem := insert p.session.mem change} t
      | .error e t => .error e t)) :
    let output := WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue
    let accepted := match output with | .ok .. => true | .error .. => false
    let tail := suffix p.ref p.lock {p.session with mem := insert p.session.mem change} accepted
    (tail.run (WalRecoverySlice.Segmented.Native.returnedWorld output)).state =
      (WalRecoverySlice.Segmented.Native.returnedWorld (Native.withOpen path (fun h => Native.mutation h change) start)) := by
  intro output accepted tail
  have path := afterWrite_state _ ran p.lock {p.session with mem := insert p.session.mem change}
  rw [invoked]
  cases reached : WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue <;>
    simpa only [tail, accepted, output, reached, afterStore, WalRecoverySlice.Segmented.Native.returnedWorld]
      using path

/-- A primitive preserves the manifest and committed table observations,
while permitting any whole-file WAL writebacks. -/
structure Frame (physical : W → Footprint inode) (root : FilePath) (tables : Catalog) (s t : W) : Prop where
  disk : WalRecoverySlice.Segmented.Writebacks (physical s).disk (physical t).disk
  manifest : (physical t).manifest.active = (physical s).manifest.active
  survivors : (physical t).manifest.survivors = (physical s).manifest.survivors
  catalog : (tableNamespace physical root).Keeps s t tables

/-- Executing a prefix of the actual finalizer leaves this continuation.
Membership refers only to the primitive operand and its returned value. -/
inductive Tail.Prefix : Tail → W → Tail → W → Prop where
  | here : Prefix path w path w
  | step : Prefix (next (op w).val) (op w).state rest t → Prefix (.call op next) w rest t

/-- Every primitive return boundary, including a reported error, is
represented even if that return is the final call in the scope. -/
theorem Tail.Prefix.finish (path : Tail) (w : W) : Prefix path w .done (path.run w).state := by
  induction path generalizing w with
  | done => exact .here
  | call op next ih => exact .step (ih (op w).val _)

abbrev LeafStop := {α : Type} → BaseIO α → W → W → Prop

/-- Ordinary boundaries include pure guard rejections and the completed
scope. An in-flight observation retains the exact operand but needs no
return from the interrupted call. -/
inductive Cut (stop : LeafStop) (path : Tail) (start : W) (cut : W) : Prop where
  | boundary : Tail.Prefix path start rest cut → Cut stop path start cut
  | during : Tail.Prefix path start (.call op next) w → stop op w cut → Cut stop path start cut

private theorem Frame.refl (physical : W → Footprint inode) (root : FilePath) (tables : Catalog) (w : W) :
    Frame physical root tables w w := ⟨.nil, rfl, rfl, fun _ _ _ _ _ left right => ⟨left, right⟩⟩

private theorem Frame.trans (first : Frame physical root tables s t)
    (next : Frame physical root tables t u) : Frame physical root tables s u :=
  ⟨first.disk.trans next.disk, next.manifest.trans first.manifest,
    next.survivors.trans first.survivors, first.catalog.trans next.catalog⟩

/-- Local frame laws apply only to an operand actually issued by this
invocation of the suffix, including the unlock after a failed child close. -/
structure Frames (edge : W → W → Prop) (stop : LeafStop) (path : Tail) (start : W) : Prop where
  returned : ∀ {α} {op : BaseIO α} {next w}, Tail.Prefix path start (.call op next) w → edge w (op w).state
  stopped : ∀ {α} {op : BaseIO α} {next w cut}, Tail.Prefix path start (.call op next) w →
    stop op w cut → edge w cut

private theorem Tail.Prefix.frame (cut : Tail.Prefix path s rest t)
    (frames : Frames (Frame physical root tables) stop path s) : Frame physical root tables s t := by
  induction cut with
  | here => exact Frame.refl ..
  | step _ ih =>
    exact (frames.returned .here).trans (ih ⟨fun path => frames.returned (.step path),
      fun path => frames.stopped (.step path)⟩)

theorem Cut.frame (position : Cut stop path s t)
    (frames : Frames (Frame physical root tables) stop path s) : Frame physical root tables s t := by
  cases position with
  | boundary route => exact route.frame frames
  | during route interrupted => exact (route.frame frames).trans (frames.stopped route interrupted)

theorem Frame.files (keep : Frame physical root image.tables w cut)
    (manifest : (physical w).manifest.Stable (L0Manifest.encode image.version))
    (catalog : (tableNamespace physical root).Represents w image.tables)
    (disk : WalRecoverySlice.Segmented.Recoverable image.view req (physical w).disk)
    (restart : NativeAppendCut.Restarted physical root image.tables cut (physical cut).disk mode after) :
    NativeReadScope.RestartFiles req physical root image after :=
  restart.filesAt ⟨keep.manifest.trans manifest.1, keep.survivors.trans manifest.2⟩ (catalog.frame keep.catalog) (keep.disk.recoverable disk)

def accepted : EST.Out IO.Error IO.RealWorld Nat → Bool
  | .ok .. => true
  | .error .. => false

def selected (image : Selected) (change : Change) (ok : Bool) :=
  if ok then image.append (encode change) else image

def pending (change : Change) (ok : Bool) : Option WalRecoverySlice.Segmented.Contract.Request :=
  if ok then none else some (.append (encode change))

abbrev Prefix := InterruptedMutation.Prefix

def output (p : Prefix path root start) (change : Change) :=
  WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue

noncomputable def remaining (p : Prefix path root start) (change : Change) :=
  suffix p.ref p.lock {p.session with mem := insert p.session.mem change} (accepted (output p change))

open NativeMutationScope (uncertainEvents)
open WalRecoverySlice.Segmented.Native (returnedWorld)

structure Recovery (physical : W → Footprint inode) (heap : PhaseMemory) (path root : FilePath)
    (image : Selected) (life : NativeRead.Lifetime) (req : Option WalRecoverySlice.Segmented.Contract.Request)
    (events : List Event) (after : W) : Prop where
  retry : Retry physical root events image req after
  reads : Reopens physical heap path root image life req → ∀ first second rootLife,
    PendingReadScope.TwoReads req physical path root image life events after first second rootLife

private theorem recovery (outcome : Retry physical root events image req after) :
    Recovery physical heap path root image life req events after :=
  ⟨outcome, outcome.readTwice⟩

/-- The returned WAL action already fixes the history on acknowledgement
loss. On a reported error both WAL survivors remain admitted. -/
theorem afterReturn {physical : W → Footprint inode} (p : Prefix path root start)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ l r, WithOpenReads.Runtime physical root l r image life heap)
    (trace : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, NativeRead.SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (fits : image.view.tail + 1 < UInt64.size) (io : NativeMutationScope.AppendPrimitives runtime change)
    (linux : System.Platform.isWindows = false)
    (atCut : Cut stop (remaining p change) (returnedWorld (output p change)) cut)
    (frames : Frames (Frame physical root image.tables) stop (remaining p change) (returnedWorld (output p change)))
    (restart : NativeAppendCut.Restarted physical root image.tables cut (physical cut).disk mode after) :
    ((remaining p change).run (returnedWorld (output p change))).state =
      returnedWorld (Native.withOpen path (fun h => Native.mutation h change) start) ∧
    Recovery physical heap path root (selected image change (accepted (output p change))) life
      (pending change (accepted (output p change))) (uncertainEvents before change) after := by
  obtain ⟨run, history, entered, h, binding, scope, invoked⟩ :=
    p.issued entry files heap (runtime p.lock p.ref) trace change scans fits
  refine ⟨?_, ?_⟩
  · exact suffix_state p scope invoked
  apply recovery
  have post := NativeMutationScope.appendAt runtime io entered fits linux
  have keep := atCut.frame frames
  change Frame physical root image.tables (returnedWorld (WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue)) cut at keep
  unfold output
  unfold Alvoki.NativePost.IOReturns at post
  cases ran : WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue with
  | error e t =>
    rw [ran] at post keep
    exact Retry.uncertain run (keep.files post.1.manifest post.1.catalog post.2.1 restart)
  | ok pos t =>
    rw [ran] at post keep
    obtain ⟨_, held, reg, mem, active, view, _⟩ := post
    obtain ⟨_, _, _, _, _, ready⟩ := active
    have disk := ready.installed.offline (request := none) (.inl view)
    exact (Retry.written run (Frame.files (image := image.append (encode change)) keep held.manifest held.catalog disk restart)).2

/-- A full absolute-position guard returns an error before the native WAL
append is issued. The same error finalizers retain the old, settled image. -/
theorem rejected {physical : W → Footprint inode} (p : Prefix path root start)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap)
    (trace : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, NativeRead.SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (full : ¬ image.view.tail + 1 < UInt64.size)
    (atCut : Cut stop (suffix p.ref p.lock p.session false) (NativeWrite.guardWorld p.ref p.wal p.callback) cut)
    (frames : Frames (Frame physical root image.tables) stop (suffix p.ref p.lock p.session false)
      (NativeWrite.guardWorld p.ref p.wal p.callback))
    (restart : NativeAppendCut.Restarted physical root image.tables cut (physical cut).disk mode after) :
    ((suffix p.ref p.lock p.session false).run (NativeWrite.guardWorld p.ref p.wal p.callback)).state =
      returnedWorld (Native.withOpen path (fun h => Native.mutation h change) start) ∧
    Recovery physical heap path root image life none (uncertainEvents before change) after := by
  obtain ⟨run, history, online⟩ := p.online entry files heap ops trace
  obtain ⟨h, bound, scope⟩ := p.withOpen (fun h => Native.mutation h change)
  have rejected := NativeWrite.dispatchAt online bound heap ops.cleanup.cached ops.phase (scans history) change
  simp only [full, ↓reduceIte] at rejected
  obtain ⟨held, invoked⟩ := rejected
  obtain ⟨_, _, _, installed, view⟩ := held.child
  have saved := (atCut.frame frames).files held.manifest held.catalog (installed.installed.offline (request := none) (.inl view)) restart
  refine ⟨?_, recovery (Retry.rejected run saved)⟩
  rw [scope]
  let body := Native.mutation h change
  let finalizer := finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close) p.lock.unlock
  have world : returnedWorld (finish (ε := IO.Error) body finalizer p.callback) =
      (finalizer.toBaseIO (body.toBaseIO p.callback).state).state := by
    rw [← finish_state]
    cases ran : finish (ε := IO.Error) body finalizer p.callback <;> simp [returnedWorld, EIO.toBaseIO, ran]
  rw [world]
  dsimp only [finalizer]
  rw [finish_state]
  simp only [suffix, Bool.false_eq_true, ↓reduceIte, close_state, Tail.run,
    body, EIO.toBaseIO, invoked, NativeWrite.afterWrite]
  rfl

end ExperimentalL0.MutationExitCut
