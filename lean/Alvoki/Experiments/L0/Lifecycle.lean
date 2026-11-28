import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0.Lifecycle

/-- The wrapper holds one phase cell. An exposed session owns the WAL
in the same cell, and intermediate phases keep it private for cleanup. -/
inductive Phase (W : Type) where
  | offline
  | opening
  | recovering (handle : W)
  | updating (handle : W)
  | online (handle : W) (session : Session)

variable {W : Type}

def Phase.wal : Phase W → Option W
  | .recovering handle | .updating handle | .online handle _ => some handle
  | .offline | .opening => none

def Phase.session : Phase W → Option Session
  | .online _ session => some session
  | _ => none

/-- Reserve the only phase in which the recovery callback can open a WAL.
The returned constructor records the new handle before the callback scans it. -/
def Phase.attachWal : Phase W → Option (W → Phase W)
  | .opening => some .recovering
  | _ => none

/-- Hide the previous session for the entire duration of a mutation. -/
def Phase.beginUpdate : Phase W → Option (Phase W × Session)
  | .online handle session => some (.updating handle, session)
  | _ => none

/-- Publish only after recovery or the mutating operation completed. -/
def Phase.publish (phase : Phase W) (session : Session) : Option (Phase W) :=
  match phase with
  | .recovering handle | .updating handle => some (.online handle session)
  | _ => none

/-- Publish into the same handle custody. In particular a closed handle
cannot be brought online by either an operation or a recovery continuation. -/
theorem Phase.publish_owns_wal {before after : Phase W} {session : Session}
    (step : before.publish session = some after) :
    after.session = some session ∧ after.wal = before.wal ∧ before.session = none := by
  cases before <;> simp [publish] at step <;> subst after <;> exact ⟨rfl, rfl, rfl⟩

theorem Phase.beginUpdate_hides_session {before after : Phase W} {session : Session}
    (step : before.beginUpdate = some (after, session)) :
    before.session = some session ∧ after.session = none ∧ after.wal = before.wal := by
  cases before <;> simp [beginUpdate] at step
  obtain ⟨rfl, rfl⟩ := step
  exact ⟨rfl, rfl, rfl⟩

theorem Phase.attachWal_keeps_session_private {before : Phase W} {attach : W → Phase W}
    (step : before.attachWal = some attach) (handle : W) :
    before.wal = none ∧ (attach handle).wal = some handle ∧
      (attach handle).session = none := by
  cases before <;> simp [attachWal] at step
  subst attach
  exact ⟨rfl, rfl, rfl⟩

theorem Phase.online_owns_wal {phase : Phase W} {session : Session}
    (online : phase.session = some session) : ∃ handle, phase.wal = some handle := by
  cases phase <;> simp_all [Phase.session, Phase.wal]

/-- This is the value installed by cleanup before any fallible close callback. -/
theorem Phase.offline_closed (session : Session) :
    (Phase.offline : Phase W).wal = none ∧ (Phase.offline : Phase W).session = none ∧
      (Phase.offline : Phase W).attachWal = none ∧
      (Phase.offline : Phase W).beginUpdate = none ∧
      (Phase.offline : Phase W).publish session = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- The executable wrapper interprets the phase cell with an IO.Ref. -/
structure Cell (m : Type → Type u) (W : Type) where
  read : m (Phase W)
  swap : Phase W → m (Phase W)

/-- Keep custody of the returned handle before scanning. A failed scan
therefore leaves the attached handle available to the scope cleanup. -/
def Cell.reopenWal [Monad m] [MonadExceptOf ε m] (cell : Cell m W)
    (invalid : ε) (openWal : m W) (scan : W → m α) : m α := do
  let some attach := (← cell.read).attachWal | throw invalid
  let handle ← openWal
  let _ ← cell.swap (attach handle)
  scan handle

/-- Component callbacks are given only the handle they need. Only the
shared adapter below receives the phase cell and attaches a recovery handle. -/
structure Callbacks (m : Type → Type) (W : Type) where
  append : W → WalRecoverySlice.Segmented.Contract.Batch → m Unit
  scan : W → m WalRecoverySlice.Segmented.Contract.View
  openWal : m W
  manifest : DurableBlob.Backend m L0Manifest.Version
  tables : Tables m

def Cell.borrowWal [Monad m] [MonadExceptOf ε m] (cell : Cell m W)
    (invalid : ε) (use : W → m α) : m α := do
  let some handle := (← cell.read).wal | throw invalid
  use handle

/-- This is the component record consumed by the L0 schedule on Linux. -/
def Cell.components [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (callbacks : Callbacks m W) : Components m where
  append := fun batch => cell.borrowWal invalid (fun handle => callbacks.append handle batch)
  scan := cell.borrowWal invalid callbacks.scan
  reopenWal := cell.reopenWal invalid callbacks.openWal callbacks.scan
  manifest := callbacks.manifest
  tables := callbacks.tables

def Cell.publish [Monad m] [MonadExceptOf ε m] (cell : Cell m W)
    (invalid : ε) (session : Session) : m Unit := do
  let some next := (← cell.read).publish session | throw invalid
  let _ ← cell.swap next

def Cell.close [Monad m] (cell : Cell m W) (closeWal : W → m Unit) : m Unit := do
  let previous ← cell.swap .offline
  if let some handle := previous.wal then closeWal handle

private def attempt [Monad m] [MonadExceptOf ε m] (action : m α) : m (Except ε α) :=
  MonadExceptOf.tryCatch (ε := ε) (action >>= fun value => pure (.ok value))
    (fun error => pure (.error error))

/-- Execute cleanup on either outcome and preserve the primary error. -/
def finish [Monad m] [MonadExceptOf ε m] (action : m α) (cleanup : m Unit) : m α := do
  let result ← attempt (ε := ε) action
  let cleaned ← attempt (ε := ε) cleanup
  match result, cleaned with
  | .error error, _ | .ok _, .error error => throw error
  | .ok value, .ok () => pure value

/-- Native cleanup starts at the world left by the body even on error.
If both operations fail, keep the earlier error at the later world. -/
theorem finish_io (action : IO α) (cleanup : IO Unit) (start : Void IO.RealWorld) :
    finish (ε := IO.Error) action cleanup start =
      let body := action.toBaseIO start
      let released := cleanup.toBaseIO body.state
      match body.val, released.val with
      | .error e, _ | .ok _, .error e => .error e released.state
      | .ok x, .ok _ => .ok x released.state := by
  cases ran : action start with
  | ok x t | error e t =>
    cases released : cleanup t <;>
      simp [finish, attempt, Bind.bind, instMonadEIO._aux_13, EST.bind, EIO.toBaseIO,
        MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
        Pure.pure, instMonadEIO._aux_5, EST.pure, ran, released] <;> rfl

/-- Kernel-checked by the interpretation below. The native wrapper runs
this schedule inside the already-acquired root-lock scope. -/
def Cell.withSession [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (recover : m Session) (use : m α) (closeWal : W → m Unit) (unlock : m Unit) : m α :=
  finish (ε := ε) (do
    let session ← recover
    cell.publish invalid session
    use) (finish (ε := ε) (cell.close closeWal) unlock)

/-- Reads need an online session and do not hide or republish it. -/
def Cell.useSession [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (use : Session → m α) : m α := do
  let some session := (← cell.read).session | throw invalid
  use session

/-- The phase check and the storage lookup run in the same interpreter. -/
def Cell.get [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (ops : Components m) (key : UInt64) : m (Option UInt64) :=
  cell.useSession invalid (fun live => ExperimentalL0.get ops live key)

def Cell.update [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (operation : Session → m Session) (closeWal : W → m Unit) : m Unit := do
  let some (next, session) := (← cell.read).beginUpdate | throw invalid
  let _ ← cell.swap next
  let result ← attempt (ε := ε) (do cell.publish invalid (← operation session))
  match result with
  | .ok () => pure ()
  | .error error =>
    let _ ← attempt (ε := ε) (cell.close closeWal)
    throw error

/-- The online branch begins on the world produced by the phase swap.
On failure, close consumes the failed world's phase and preserves its
primary error even when releasing the WAL reports another error. -/
theorem Cell.update_online_io (cell : Cell IO W) (invalid : IO.Error)
    (operation : Session → IO Session) (closeWal : W → IO Unit)
    (read : cell.read start = .ok (.online wal session) entered)
    (swap : cell.swap (.updating wal) entered = .ok previous hidden) :
    cell.update invalid operation closeWal start =
      let completed := (operation session >>= cell.publish invalid).toBaseIO hidden
      match completed.val with
      | .ok _ => .ok () completed.state
      | .error e => .error e ((cell.close closeWal).toBaseIO completed.state).state := by
  cases ran : operation session hidden with
  | error e t =>
    cases closed : cell.close closeWal t <;>
      simp [Cell.update, Phase.beginUpdate, read, swap, ran, closed, attempt, Bind.bind,
        instMonadEIO._aux_13, EST.bind, EIO.toBaseIO, MonadExceptOf.tryCatch,
        instMonadExceptOfEIO._aux_3, EST.tryCatch, Pure.pure, instMonadEIO._aux_5, EST.pure] <;> rfl
  | ok next t =>
    cases published : cell.publish invalid next t with
    | ok => simp [Cell.update, Phase.beginUpdate, read, swap, ran, published, attempt,
        Bind.bind, instMonadEIO._aux_13, EST.bind, EIO.toBaseIO, MonadExceptOf.tryCatch,
        instMonadExceptOfEIO._aux_3, EST.tryCatch, Pure.pure, instMonadEIO._aux_5, EST.pure]
    | error e u =>
      cases closed : cell.close closeWal u <;>
        simp [Cell.update, Phase.beginUpdate, read, swap, ran, published, closed, attempt,
          Bind.bind, instMonadEIO._aux_13, EST.bind, EIO.toBaseIO, MonadExceptOf.tryCatch,
          instMonadExceptOfEIO._aux_3, EST.tryCatch, Pure.pure, instMonadEIO._aux_5, EST.pure] <;> rfl

namespace Proof

variable {S : Type}

def stateCell : Cell (EStateM ε (Phase W × S)) W where
  read := fun state => .ok state.1 state
  swap := fun next before => .ok before.1 (next, before.2)

/-- Interpret a storage callback without granting access to phase custody. -/
def liftStorage (storage : EStateM ε S α) : EStateM ε (Phase W × S) α := fun before =>
  match storage before.2 with
  | .ok result after => .ok result (before.1, after)
  | .error error after => .error error (before.1, after)

def liftCallbacks (callbacks : Callbacks (EStateM ε S) W) :
    Callbacks (EStateM ε (Phase W × S)) W where
  append := fun handle batch => liftStorage (callbacks.append handle batch)
  scan := fun handle => liftStorage (callbacks.scan handle)
  openWal := liftStorage callbacks.openWal
  manifest := {
    reopen := liftStorage callbacks.manifest.reopen
    publish := fun version => liftStorage (callbacks.manifest.publish version)
  }
  tables := {
    create := fun rows => liftStorage (callbacks.tables.create rows)
    check := fun id => liftStorage (callbacks.tables.check id)
    lookup := fun id key => liftStorage (callbacks.tables.lookup id key)
  }

/-- The phase at a success or failure boundary of the executable schedule. -/
def reached : EStateM.Result ε (Phase W × S) α → Phase W × S
  | .ok _ phase | .error _ phase => phase

/-- Preserve the custody cell even when storage operations fail. -/
def KeepsPhase (action : EStateM ε (Phase W × S) α) : Prop :=
  ∀ before, (reached (action before)).1 = before.1

private theorem keepsPhase_bind {action : EStateM ε (Phase W × S) α}
    {next : α → EStateM ε (Phase W × S) β}
    (kept : KeepsPhase action) (rest : ∀ val, KeepsPhase (next val)) :
    KeepsPhase (action >>= next) := by
  intro before
  have frame := kept before
  cases ran : action before with
  | error error after => simpa [Bind.bind, EStateM.bind, ran, reached] using frame
  | ok value after =>
    have more := rest value after
    simp [ran, reached] at frame
    simpa [Bind.bind, EStateM.bind, ran] using more.trans frame

private theorem keepsPhase_lift (action : EStateM ε S α) :
    @KeepsPhase W S ε α (liftStorage action) := by
  intro before
  cases ran : action before.2 <;> simp [liftStorage, ran, reached]

private theorem keepsPhase_borrow (invalid : ε) (action : W → EStateM ε S α) :
    KeepsPhase (stateCell.borrowWal invalid (fun handle => liftStorage (action handle))) := by
  intro before
  cases held : before.1.wal with
  | none => simp [Cell.borrowWal, stateCell, Bind.bind, EStateM.bind, held]; rfl
  | some handle =>
    simpa [Cell.borrowWal, stateCell, Bind.bind, EStateM.bind, held] using
      (keepsPhase_lift (action handle) before)

private theorem keepsPhase_pure (value : α) : @KeepsPhase W S ε α (pure value) :=
  fun _ => rfl

private theorem keepsPhase_throw (error : ε) : @KeepsPhase W S ε α (throw error) :=
  fun _ => rfl

abbrev callbacksWithPhase (callbacks : Callbacks (EStateM String S) W) (invalid : String) :=
  stateCell.components invalid (liftCallbacks callbacks)

/-- The shared write schedule uses the existing borrowed WAL and never
publishes or detaches a session; the outer mutation guard owns that. -/
theorem write_keepsPhase (callbacks : Callbacks (EStateM String S) W) (invalid : String)
    (session : Session) (change : Change) :
    KeepsPhase (write (callbacksWithPhase callbacks invalid) session change) := by
  unfold write
  apply keepsPhase_bind (keepsPhase_borrow invalid callbacks.scan)
  intro view
  split
  · apply keepsPhase_bind (keepsPhase_borrow invalid (fun h => callbacks.append h (encode change)))
    exact fun _ => keepsPhase_pure _
  · exact keepsPhase_throw _

theorem flush_keepsPhase (callbacks : Callbacks (EStateM String S) W) (invalid : String)
    (session : Session) :
    KeepsPhase (flush (callbacksWithPhase callbacks invalid) session) := by
  unfold flush
  split
  · exact keepsPhase_pure _
  · apply keepsPhase_bind (keepsPhase_borrow invalid callbacks.scan)
    intro view
    by_cases fits : view.tail < UInt64.size
    · simp only [ite_eq_left fits]
      apply keepsPhase_bind (keepsPhase_lift (callbacks.tables.create session.mem.toList))
      intro id
      apply keepsPhase_bind (keepsPhase_lift (callbacks.manifest.publish
        ⟨id :: session.version.tables, view.tail.toUInt64⟩))
      exact fun _ => keepsPhase_pure _
    · simp only [ite_eq_right fits]
      intro before
      rfl

private theorem lookupTables_keepsPhase (callbacks : Callbacks (EStateM String S) W)
    (invalid : String) (key : UInt64) (ids : List UInt64) :
    KeepsPhase (lookupTables (callbacksWithPhase callbacks invalid).tables key ids) := by
  induction ids with
  | nil => exact keepsPhase_pure _
  | cons id ids ih =>
    unfold lookupTables
    apply keepsPhase_bind (keepsPhase_lift (callbacks.tables.lookup id key))
    intro found
    cases found with
    | none => exact ih
    | some value => exact keepsPhase_pure _

theorem get_keepsPhase (callbacks : Callbacks (EStateM String S) W) (invalid : String)
    (session : Session) (key : UInt64) :
    KeepsPhase (get (callbacksWithPhase callbacks invalid) session key) := by
  unfold get
  split
  · exact keepsPhase_pure _
  · apply keepsPhase_bind (lookupTables_keepsPhase callbacks invalid key session.version.tables)
    exact fun _ => keepsPhase_pure _

private theorem checkTables_keepsPhase (callbacks : Callbacks (EStateM String S) W)
    (invalid : String) (ids : List UInt64) :
    KeepsPhase (checkTables (callbacksWithPhase callbacks invalid).tables ids) := by
  induction ids with
  | nil => exact keepsPhase_pure _
  | cons id ids ih =>
    unfold checkTables
    exact keepsPhase_bind (keepsPhase_lift (callbacks.tables.check id)) (fun _ => ih)

private theorem attempt_state (action : EStateM ε (Phase W × S) α) (phase : Phase W × S) :
    attempt action phase = match action phase with
      | .ok value after => .ok (.ok value) after
      | .error error after => .ok (.error error) after := by
  cases h : action phase <;>
    simp [attempt, h, MonadExceptOf.tryCatch, EStateM.tryCatch, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure] <;> rfl

private theorem finish_state (action : EStateM ε (Phase W × S) α) (cleanup) (phase : Phase W × S) :
    finish (ε := ε) action cleanup phase =
      match action phase with
      | .ok value after => match cleanup after with
        | .ok _ closed => .ok value closed
        | .error error closed => .error error closed
      | .error error after => .error error (reached (cleanup after)) := by
  cases h : action phase with
  | ok value after =>
    cases done : cleanup after <;>
      simp [finish, Bind.bind, EStateM.bind, attempt_state, h, done, Pure.pure, EStateM.pure] <;> rfl
  | error error after =>
    cases done : cleanup after <;>
      simp [finish, Bind.bind, EStateM.bind, attempt_state, h, done, reached] <;> rfl

theorem reopen_attaches_before_scan (openWal : EStateM ε (Phase W × S) W)
    (scan : W → EStateM ε (Phase W × S) α) (invalid : ε) (handle : W)
    (before : S) (after : Phase W × S)
    (opened : openWal (.opening, before) = .ok handle after) :
    Cell.reopenWal stateCell invalid openWal scan (.opening, before) =
      scan handle (.recovering handle, after.2) := by
  simp [Cell.reopenWal, stateCell, Phase.attachWal, Bind.bind, EStateM.bind, opened]

theorem reopen_open_failure (openWal : EStateM ε (Phase W × S) W)
    (scan : W → EStateM ε (Phase W × S) α) (invalid error : ε) (before : S)
    (after : Phase W × S)
    (failed : openWal (.opening, before) = .error error after) :
    Cell.reopenWal stateCell invalid openWal scan (.opening, before) = .error error after := by
  simp [Cell.reopenWal, stateCell, Phase.attachWal, Bind.bind, EStateM.bind, failed]

/-- A successful recovery keeps the handle attached by the one WAL open
through the watermark checks and every table-open callback. -/
theorem recover_attached (callbacks : Callbacks (EStateM String S) W) (invalid : String)
    (before : S) (session : Session) (after : Phase W × S)
    (ran : recover (callbacksWithPhase callbacks invalid) (.opening, before) = .ok session after) :
    ∃ handle, after.1 = .recovering handle := by
  let ops := callbacksWithPhase callbacks invalid
  change recover ops (.opening, before) = .ok session after at ran
  cases openedManifest : callbacks.manifest.reopen before with
  | error error reached =>
    have read : ops.manifest.reopen (.opening, before) = .error error (.opening, reached) := by
      simp [ops, Cell.components, liftCallbacks, liftStorage, openedManifest]
    simp [recover, Bind.bind, EStateM.bind, read] at ran
  | ok version reachedManifest =>
    have read : ops.manifest.reopen (.opening, before) = .ok version (.opening, reachedManifest) := by
      simp [ops, Cell.components, liftCallbacks, liftStorage, openedManifest]
    cases openedWal : callbacks.openWal reachedManifest with
    | error error reachedOpen =>
      have openStep : (liftCallbacks callbacks).openWal (.opening, reachedManifest) =
          .error error (.opening, reachedOpen) := by
        simp [liftCallbacks, liftStorage, openedWal]
      have same := reopen_open_failure _ (liftCallbacks callbacks).scan invalid error
        reachedManifest (.opening, reachedOpen) openStep
      change ops.reopenWal (.opening, reachedManifest) = _ at same
      simp [recover, Bind.bind, EStateM.bind, read, same] at ran
    | ok handle stored =>
      have openStep : (liftCallbacks callbacks).openWal (.opening, reachedManifest) =
          .ok handle (.opening, stored) := by
        simp [liftCallbacks, liftStorage, openedWal]
      have same := reopen_attaches_before_scan _ (liftCallbacks callbacks).scan invalid handle
        reachedManifest (.opening, stored) openStep
      change ops.reopenWal (.opening, reachedManifest) = _ at same
      cases scanned : callbacks.scan handle stored with
      | error error reachedScan =>
        have wal : ops.reopenWal (.opening, reachedManifest) =
            .error error (.recovering handle, reachedScan) := by
          simpa [liftCallbacks, liftStorage, scanned] using same
        simp [recover, Bind.bind, EStateM.bind, read, wal] at ran
      | ok view reachedScan =>
        have wal : ops.reopenWal (.opening, reachedManifest) =
            .ok view (.recovering handle, reachedScan) := by
          simpa [liftCallbacks, liftStorage, scanned] using same
        by_cases bounds : view.base ≤ version.flushedThrough.toNat ∧
            version.flushedThrough.toNat ≤ view.tail
        · cases decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode with
          | none =>
            simp [recover, Bind.bind, EStateM.bind, read, wal, bounds, decoded] at ran
            change EStateM.Result.error "invalid L0 mutation batch"
              (Phase.recovering handle, reachedScan) = _ at ran
            contradiction
          | some changes =>
            have frame := checkTables_keepsPhase callbacks invalid version.tables (.recovering handle, reachedScan)
            change (reached (checkTables ops.tables version.tables (.recovering handle, reachedScan))).1 = _ at frame
            cases checked : checkTables ops.tables version.tables (.recovering handle, reachedScan) with
            | error error result =>
              simp [recover, Bind.bind, EStateM.bind, read, wal, bounds, decoded, checked] at ran
            | ok _ result =>
              simp [recover, Bind.bind, EStateM.bind, read, wal, bounds, decoded, checked,
                Pure.pure, EStateM.pure] at ran
              obtain ⟨_, rfl⟩ := ran
              exact ⟨handle, by simpa [checked, reached] using frame⟩
        · simp [recover, Bind.bind, EStateM.bind, read, wal, bounds] at ran
          change EStateM.Result.error "manifest watermark outside the WAL view"
            (Phase.recovering handle, reachedScan) = _ at ran
          contradiction

private theorem close_state (closeWal : W → EStateM ε (Phase W × S) Unit)
    (before : Phase W × S) :
    Cell.close stateCell closeWal before =
      match before.1.wal with
      | some handle => closeWal handle (.offline, before.2)
      | none => .ok () (.offline, before.2) := by
  rcases before with ⟨phase, storage⟩
  cases phase <;> rfl

private theorem cleanup_closes (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (before : Phase W × S) :
    reached (finish (ε := ε) (Cell.close stateCell closeWal) unlock before) =
      (.offline, before.2) := by
  have closed : reached (Cell.close stateCell closeWal before) = (.offline, before.2) := by
    rw [close_state]
    cases before.1.wal with
    | none => rfl
    | some handle => exact closeFrame handle before.2
  rw [finish_state]
  cases h : Cell.close stateCell closeWal before with
  | ok _ after =>
    rw [h] at closed
    cases closed
    cases ran : unlock (.offline, before.2) <;>
      simpa [ran, reached] using unlockFrame before.2
  | error error after =>
    rw [h] at closed
    cases closed
    exact unlockFrame before.2

/-- Both a normal callback and a failing recovery leave the phase cell
offline. Close and unlock can fail and leave the reached storage unchanged. -/
theorem withSession_closes
    (recover : EStateM ε (Phase W × S) Session) (use : EStateM ε (Phase W × S) α)
    (invalid : ε) (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (before : Phase W × S) :
    (reached (Cell.withSession stateCell invalid recover use closeWal unlock before)).1 =
      .offline := by
  unfold Cell.withSession
  rw [finish_state]
  split
  · rename_i after _
    have closed := congrArg Prod.fst (cleanup_closes closeWal unlock closeFrame unlockFrame after)
    cases ran : finish (ε := ε) (Cell.close stateCell closeWal) unlock after <;>
      simpa [ran, reached] using closed
  · exact congrArg Prod.fst (cleanup_closes closeWal unlock closeFrame unlockFrame _)

/-- A failed recovery never enters the callback and preserves its error and
reached storage even when either cleanup callback also fails. -/
theorem failed_recovery_closes (recover : EStateM ε (Phase W × S) Session)
    (use : EStateM ε (Phase W × S) α) (invalid error : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock) (before : S)
    (after : Phase W × S)
    (failed : recover (.opening, before) = .error error after)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    Cell.withSession stateCell invalid recover use closeWal unlock (.opening, before) =
      .error error (.offline, after.2) := by
  unfold Cell.withSession
  rw [finish_state]
  simp [Bind.bind, EStateM.bind, failed, cleanup_closes closeWal unlock closeFrame unlockFrame]

/-- First expose the recovered session with the WAL held by recovery,
then run the client callback starting from the reached storage. -/
theorem successful_recovery_publishes (recover : EStateM ε (Phase W × S) Session)
    (use : EStateM ε (Phase W × S) α) (invalid : ε) (closeWal : W → EStateM ε (Phase W × S) Unit)
    (unlock) (wal : W) (session : Session) (before after : S)
    (ran : recover (.opening, before) = .ok session (.recovering wal, after)) :
    Cell.withSession stateCell invalid recover use closeWal unlock (.opening, before) =
      finish (ε := ε) use (finish (ε := ε) (Cell.close stateCell closeWal) unlock)
        (.online wal session, after) := by
  unfold Cell.withSession
  rw [finish_state, finish_state]
  simp [Bind.bind, EStateM.bind, ran, Cell.publish, stateCell, Phase.publish, Pure.pure, EStateM.pure]

/-- Once the callback has run, outer cleanup detaches the session from its
reached storage on either result. The outer return can still report an error. -/
theorem successful_recovery_cleanup (recover : EStateM ε (Phase W × S) Session)
    (use : EStateM ε (Phase W × S) α) (invalid : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock) (wal : W)
    (session : Session) (before after : S)
    (ran : recover (.opening, before) = .ok session (.recovering wal, after))
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    reached (Cell.withSession stateCell invalid recover use closeWal unlock (.opening, before)) =
      (.offline, (reached (use (.online wal session, after))).2) := by
  rw [successful_recovery_publishes recover use invalid closeWal unlock wal session before after ran]
  rw [finish_state]
  cases used : use (.online wal session, after) with
  | error error next =>
    exact cleanup_closes closeWal unlock closeFrame unlockFrame next
  | ok value next =>
    have closed := cleanup_closes closeWal unlock closeFrame unlockFrame next
    cases cleaned : finish (ε := ε) (Cell.close stateCell closeWal) unlock next <;>
      simpa [cleaned, reached] using closed

theorem useSession_online (use : Session → EStateM ε (Phase W × S) α) (invalid : ε)
    (wal : W) (session : Session) (storage : S) :
    Cell.useSession stateCell invalid use (.online wal session, storage) =
      use session (.online wal session, storage) := rfl

theorem useSession_offline (use : Session → EStateM ε (Phase W × S) α) (invalid : ε)
    (storage : S) :
    Cell.useSession stateCell invalid use (.offline, storage) =
      .error invalid (.offline, storage) := rfl

theorem update_success (operation : Session → EStateM ε (Phase W × S) Session) (invalid : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (wal : W) (old next : Session)
    (before after : S)
    (ran : operation old (.updating wal, before) = .ok next (.updating wal, after)) :
    Cell.update stateCell invalid operation closeWal (.online wal old, before) =
      .ok () (.online wal next, after) := by
  simp [Cell.update, stateCell, Phase.beginUpdate, Bind.bind, EStateM.bind, attempt_state,
    ran, Cell.publish, Phase.publish, Pure.pure, EStateM.pure]

private theorem read_state (state : Phase W × S) :
    (stateCell (ε := ε)).read state = .ok state.1 state := rfl

private theorem swap_state (state : Phase W × S) (next : Phase W) :
    (stateCell (ε := ε)).swap next state = .ok state.1 (next, state.2) := rfl

theorem update_error (operation : Session → EStateM ε (Phase W × S) Session) (invalid error : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (wal : W) (old : Session) (before : S)
    (after : Phase W × S)
    (ran : operation old (.updating wal, before) = .error error after)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Cell.update stateCell invalid operation closeWal (.online wal old, before) =
      .error error (.offline, after.2) := by
  simp only [Cell.update, read_state, swap_state, Phase.beginUpdate, Bind.bind, EStateM.bind,
    attempt_state, ran, close_state]
  cases h : after.1.wal with
  | none => rfl
  | some handle =>
    have closed := closeFrame handle after.2
    cases ranClose : closeWal handle (.offline, after.2) <;>
      simp [ranClose, reached] at closed ⊢ <;> subst_vars <;> rfl

end Proof
end ExperimentalL0.Lifecycle
