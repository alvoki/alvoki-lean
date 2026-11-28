import Alvoki.Experiments.L0.Native

namespace ExperimentalL0.NativeScope
open System Lifecycle
abbrev W := Void IO.RealWorld
abbrev Wal := WalRecoverySlice.Segmented.Native.Handle
abbrev Ref := IO.Ref (Phase Wal)

/-- A continuation for each reported result of the actual IO action. -/
def Post (action : IO α) (start : W) (ok : α → W → Prop) (err : IO.Error → W → Prop) : Prop :=
  match action start with
  | .ok x t => ok x t
  | .error e t => err e t

theorem Post.weaken {failure : IO.Error → W → Prop} (h : Post action w before failure)
    (success : ∀ x t, before x t → ok x t)
    (error : ∀ e t, failure e t → err e t) : Post action w ok err := by
  unfold Post at *
  split at h
  · exact success _ _ h
  · exact error _ _ h

theorem Post.bind (action : IO α) (next : α → IO β)
    (first : Post action w (fun x t => Post (next x) t ok err) err) :
    Post (action >>= next) w ok err := by
  unfold Post at *
  cases ran : action w <;>
    simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using first

theorem Post.andThen {action : IO α} {next : α → IO β}
    (first : Post action w ready err)
    (following : ∀ x t, ready x t → Post (next x) t ok err) :
    Post (action >>= next) w ok err := by
  apply Post.bind
  unfold Post at first ⊢
  cases ran : action w with
  | error e t => simpa only [ran] using first
  | ok x t =>
    rw [ran] at first
    exact following x t first

/-- A cleanup failure may replace success. When the body fails, the
original error is the one reported, at the world left by cleanup. -/
theorem Post.finish (body : IO α) (cleanup : IO Unit)
    (bodyPost : Post body w
      (fun x t => Post cleanup t (fun _ u => ok x u) err)
      (fun e t => Post cleanup t (fun _ u => err e u) (fun _ u => err e u))) :
    Post (Lifecycle.finish (ε := IO.Error) body cleanup) w ok err := by
  unfold Post at *
  rw [finish_io]
  cases ran : body w with
  | ok x t | error e t =>
    cases released : cleanup t <;> simpa only [EIO.toBaseIO, ran, released] using bodyPost

theorem swap_io (ref : Ref) (next : Phase Wal) (w : W) :
    (ref.swap next : IO (Phase Wal)) w =
      .ok ((ref.swap next : BaseIO (Phase Wal)) w).val ((ref.swap next : BaseIO (Phase Wal)) w).state := by
  change (match ST.Prim.Ref.swap ref next w with | ⟨val, t⟩ => EST.Out.ok val t) = _
  generalize h : ST.Prim.Ref.swap ref next w = r
  cases r with
  | mk val t =>
    change EST.Out.ok val t = .ok (ST.Prim.Ref.swap ref next w).val (ST.Prim.Ref.swap ref next w).state
    rw [h]

theorem read_io (ref : Ref) (w : W) :
    (ref.get : IO (Phase Wal)) w =
      .ok ((ref.get : BaseIO (Phase Wal)) w).val ((ref.get : BaseIO (Phase Wal)) w).state := by
  change (match ST.Prim.Ref.get ref w with | ⟨val, t⟩ => EST.Out.ok val t) = _
  generalize h : ST.Prim.Ref.get ref w = r
  cases r with
  | mk val t =>
    change EST.Out.ok val t = .ok (ST.Prim.Ref.get ref w).val (ST.Prim.Ref.get ref w).state
    rw [h]

theorem close_run (ref : Ref) (w : W) :
    let taken := (ref.swap .offline : BaseIO (Phase Wal)) w
    (Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close w =
      match taken.val.wal with
      | none => .ok () taken.state
      | some child => WalRecoverySlice.Segmented.Native.close child taken.state := by
    intro taken
    simp only [Cell.close, Native.phaseCell, Bind.bind, instMonadEIO._aux_13, EST.bind, swap_io]
    cases choice : taken.val.wal <;> simp [taken] at choice ⊢ <;> rfl

/-- The postcondition required at the start of cleanup. The swap consumes
the exact phase cell before looking up its child. Unlock starts at the world
left by that child's close, even if the close reports an error. -/
def Release (ref : Ref) (lock : IO.FS.Handle) (w : W)
    (ok : W → Prop) (err : IO.Error → W → Prop) : Prop :=
  let taken := (ref.swap .offline : BaseIO (Phase Wal)) w
  let unlock := fun t => Post lock.unlock t (fun _ u => ok u) err
  match taken.val.wal with
  | none => unlock taken.state
  | some child => Post (WalRecoverySlice.Segmented.Native.close child) taken.state
      (fun _ t => unlock t)
      (fun e t => Post lock.unlock t (fun _ u => err e u) (fun _ u => err e u))

theorem release (h : Release ref lock w ok err) :
    Post (Lifecycle.finish (ε := IO.Error)
      ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close) lock.unlock)
      w (fun _ u => ok u) err := by
  apply Post.finish
  let taken := (ref.swap .offline : BaseIO (Phase Wal)) w
  unfold Post
  rw [close_run]
  change (match taken.val.wal with | none => _ | some _ => _) at h
  cases choice : taken.val.wal with
  | none =>
    rw [choice] at h
    exact h
  | some child =>
    simp only [choice] at h
    exact h

/-- Reached success and failure obligations for the read callback. -/
def Callback (ref : Ref) (lock : IO.FS.Handle) (use : IO α) (w : W)
    (ok : α → W → Prop) (err : IO.Error → W → Prop) : Prop :=
  Post use w
    (fun x t => Release ref lock t (ok x) err)
    (fun e t => Release ref lock t (err e) (fun _ u => err e u))

/-- Publication reads the same reference that recovery used. Its successful
swap installs an online session on that reference before invoking the callback. -/
def Publish (ref : Ref) (lock : IO.FS.Handle) (use : IO α) (session : Session)
    (w : W) (ok : α → W → Prop) (err : IO.Error → W → Prop) : Prop :=
  let read := (ref.get : BaseIO (Phase Wal)) w
  match read.val.publish session with
  | none =>
    let e := IO.userError "L0 cannot publish a session"
    Release ref lock read.state (err e) (fun _ u => err e u)
  | some next => Callback ref lock use ((ref.swap next : BaseIO (Phase Wal)) read.state).state ok err

theorem withSession_rule (root : FilePath) (ref : Ref) (lock : IO.FS.Handle) (use : IO α)
    (recovery : Post (Native.recoverAt root ref) w
      (fun session t => Publish ref lock use session t ok err)
      (fun e t => Release ref lock t (err e) (fun _ u => err e u))) :
    Post ((Native.phaseCell ref).withSession (IO.userError "L0 cannot publish a session")
        (Native.recoverAt root ref) use WalRecoverySlice.Segmented.Native.close lock.unlock)
      w ok err := by
  unfold Cell.withSession
  apply Post.finish
  apply Post.bind
  unfold Post at recovery ⊢
  cases ran : Native.recoverAt root ref w with
  | error e t =>
    rw [ran] at recovery
    exact release recovery
  | ok session t =>
    rw [ran] at recovery
    let read := (ref.get : BaseIO (Phase Wal)) t
    have pub : (Native.phaseCell ref).publish (IO.userError "L0 cannot publish a session") session t =
        match read.val.publish session with
        | none => .error (IO.userError "L0 cannot publish a session") read.state
        | some next => .ok () ((ref.swap next : BaseIO (Phase Wal)) read.state).state := by
      simp only [Cell.publish, Native.phaseCell, Bind.bind, instMonadEIO._aux_13, EST.bind, read_io]
      cases choice : read.val.publish session <;> simp [read, EST.bind, swap_io] at choice ⊢ <;> rfl
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, pub]
    change Publish ref lock use session t ok err at recovery
    unfold Publish at recovery
    dsimp only at recovery
    cases choice : read.val.publish session with
    | none =>
      dsimp only [read] at choice
      rw [choice] at recovery
      exact release recovery
    | some next =>
      dsimp only [read] at choice
      rw [choice] at recovery
      let entered := ((ref.swap next : BaseIO (Phase Wal)) read.state).state
      change Callback ref lock use entered ok err at recovery
      unfold Callback Post at recovery
      cases called : use entered with
      | error e u | ok x u =>
        rw [called] at recovery
        change (match use entered with | .ok _ _ => _ | .error _ _ => _)
        rw [called]
        exact release recovery

/-- Path resolution and metadata preserve the caller's namespace facts;
the native checks decide which paths can proceed to opening the lock. An
owner using these facts across acquisition must protect against name races. -/
theorem validatedRoot_rule (path : FilePath)
    (resolved : Post (IO.FS.realPath path) start ready failed)
    (stat : ∀ root w, ready root w → ∀ (p : FilePath),
      Post p.symlinkMetadata w (fun _ t => ready root t) (fun _ t => ready root t))
    (reject : ∀ root w, ready root w → ∀ e, failed e w) :
    Post (Native.validatedRoot path) start ready failed := by
  have dir : ∀ root name w, ready root w →
      Post (Native.checkComponentDirectory root name) w (fun _ t => ready root t) failed := by
    intro root name w good
    have frame := stat root w good (root / name)
    unfold Post Native.checkComponentDirectory at *
    cases ran : (root / name).symlinkMetadata w with
    | error e t =>
      rw [ran] at frame
      simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using reject root t frame e
    | ok md t =>
      rw [ran] at frame
      by_cases regular : (md.type == IO.FS.FileType.dir) = true
      · simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, regular, Pure.pure,
          instMonadEIO._aux_5, EST.pure] using frame
      · simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, regular, Bool.false_eq_true,
          ite_false]
        exact reject root t frame _
  have existsPost : ∀ root (p : FilePath) w, ready root w →
      Post (Native.pathExists p) w (fun _ t => ready root t) failed := by
    intro root p w good
    have frame := stat root w good p
    unfold Post Native.pathExists at *
    cases ran : p.symlinkMetadata w with
    | ok md t =>
      rw [ran] at frame
      simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, MonadExceptOf.tryCatch,
        instMonadExceptOfEIO._aux_3, EST.tryCatch, Pure.pure, instMonadEIO._aux_5, EST.pure] using frame
    | error e t =>
      rw [ran] at frame
      cases e <;> simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, MonadExceptOf.tryCatch,
        instMonadExceptOfEIO._aux_3, EST.tryCatch] <;>
        first | exact frame | exact reject root t frame _
  unfold Native.validatedRoot
  apply Post.andThen resolved
  intro root t good
  apply Post.andThen (dir root "wal" t good)
  intro _ u good
  apply Post.andThen (dir root "manifest" u good)
  intro _ v good
  apply Post.andThen (dir root "tables" v good)
  intro _ w good
  apply Post.bind
  let p := root / "l0.lock"
  have lockCheck : Post (Native.checkLockName p) w (fun _ t => ready root t) failed := by
    unfold Native.checkLockName
    apply Post.andThen (existsPost root p w good)
    intro yes t good
    cases yes with
    | false => exact good
    | true =>
      have frame := stat root t good p
      unfold Post at *
      cases ran : p.symlinkMetadata t with
      | error e u =>
        rw [ran] at frame
        simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using reject root u frame e
      | ok md u =>
        rw [ran] at frame
        by_cases regular : (md.type == IO.FS.FileType.file && md.numLinks == 1) = true
        · simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, regular, Pure.pure,
            instMonadEIO._aux_5, EST.pure] using frame
        · simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, regular]
          exact
            reject root u frame (IO.userError "expected a singly linked regular L0 lock file")
  exact lockCheck

/-- Acquire the root from its validated path, then allocate the actual phase
cell, recover and enter the callback. The caller supplies an invariant on the
instant of successful lock acquisition and consumes it on the fresh reference.
A path, open or lock error has no callback premise. -/
theorem withOpen_rule (path : FilePath) (use : Native.Handle → IO α)
    (held : FilePath → IO.FS.Handle → W → Prop)
    (acquire : Post (Native.validatedRoot path) start (fun root t =>
      Post (IO.FS.Handle.mk (root / "l0.lock") .append) t (fun lock u =>
        Post (lock.tryLock true) u (fun yes v =>
          if yes then held root lock v else err (IO.userError "L0 already open") v) err) err) err)
    (scope : ∀ root lock v, held root lock v →
      let fresh := IO.mkRef (.opening : Phase Wal) v
      ∀ handle, handle.AtRoot root fresh.val →
        Post (Native.recoverAt root fresh.val) fresh.state
          (fun session t => Publish fresh.val lock (use handle) session t ok err)
          (fun e t => Release fresh.val lock t (err e) (fun _ u => err e u))) :
    Post (Native.withOpen path use) start ok err := by
  have reached := Native.withOpen_reached path use start
  unfold Post at acquire ⊢
  cases resolved : Native.validatedRoot path start with
  | error e t =>
    rw [resolved] at reached acquire
    rwa [reached]
  | ok root t =>
    rw [resolved] at reached acquire
    cases opened : IO.FS.Handle.mk (root / "l0.lock") .append t with
    | error e u =>
      simp only [opened] at reached acquire
      rwa [reached]
    | ok lock u =>
      simp only [opened] at reached acquire
      cases locked : lock.tryLock true u with
      | error e v =>
        simp only [locked] at reached acquire
        rwa [reached]
      | ok yes v =>
        cases yes with
        | false =>
          simp only [locked] at reached acquire
          rwa [reached]
        | true =>
          simp only [locked] at reached acquire
          obtain ⟨handle, binding, execution⟩ := reached
          rw [execution]
          exact withSession_rule root _ lock (use handle) (scope root lock v acquire handle binding)

/-- When recovery fails before invoking the callback, the primary error
is independent of the callback and both cleanup outcomes. The reached world
records the actual close (only for an attached child) and subsequent unlock. -/
theorem withOpen_recoveryError (path root : FilePath) (use : Native.Handle → IO α)
    (resolved : Native.validatedRoot path start = .ok root t)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append t = .ok lock u)
    (held : lock.tryLock true u = .ok true v)
    (failed : let fresh := IO.mkRef (.opening : Phase Wal) v
      Native.recoverAt root fresh.val fresh.state = .error e reached) :
    let fresh := IO.mkRef (.opening : Phase Wal) v
    let taken := (fresh.val.swap .offline : BaseIO (Phase Wal)) reached
    let afterChild := match taken.val.wal with
      | none => taken.state
      | some child => ((WalRecoverySlice.Segmented.Native.close child).toBaseIO taken.state).state
    Native.withOpen path use start = .error e (lock.unlock.toBaseIO afterChild).state := by
  let fresh := IO.mkRef (.opening : Phase Wal) v
  let ref := fresh.val
  let taken := (ref.swap .offline : BaseIO (Phase Wal)) reached
  have unlocked (w) : Post lock.unlock w
      (fun _ t => t = (lock.unlock.toBaseIO w).state)
      (fun _ t => t = (lock.unlock.toBaseIO w).state) := by
    unfold Post
    cases run : lock.unlock w <;> simp [EIO.toBaseIO, run]
  have execution := Native.withOpen_reached path use start
  simp only [resolved, opened, held] at execution
  obtain ⟨handle, _, ran⟩ := execution
  rw [ran]
  let afterChild := match taken.val.wal with
    | none => taken.state
    | some child => ((WalRecoverySlice.Segmented.Native.close child).toBaseIO taken.state).state
  have cleanup : Release ref lock reached (fun w => w = (lock.unlock.toBaseIO afterChild).state)
      (fun _ w => w = (lock.unlock.toBaseIO afterChild).state) := by
    unfold Release
    cases owned : taken.val.wal with
    | none =>
      simpa [taken, afterChild, owned] using unlocked taken.state
    | some child =>
      change (match taken.val.wal with | none => _ | some _ => _)
      rw [owned]
      unfold Post
      cases closed : WalRecoverySlice.Segmented.Native.close child taken.state with
      | ok x end_ | error err end_ =>
        dsimp only [taken] at closed
        simpa [Post, afterChild, owned, taken, EIO.toBaseIO, closed] using unlocked end_
  let final := (lock.unlock.toBaseIO afterChild).state
  change Native.recoverAt root ref fresh.state = .error e reached at failed
  let body := (Native.phaseCell ref).withSession (IO.userError "L0 cannot publish a session")
      (Native.recoverAt root ref) (use handle) WalRecoverySlice.Segmented.Native.close lock.unlock
  have post : Post body fresh.state (fun _ _ => False) (fun err t => err = e ∧ t = final) := by
    apply withSession_rule
    rw [Post, failed]
    simpa only [eq_self, true_and] using cleanup
  change body fresh.state = .error e final
  cases result : body fresh.state with
  | ok x t => rw [Post, result] at post; exact post.elim
  | error err t =>
    rw [Post, result] at post
    obtain ⟨rfl, rfl⟩ := post
    rfl

end ExperimentalL0.NativeScope
