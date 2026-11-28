import Alvoki.Experiments.L0.TableSchedule
import Alvoki.Experiments.L0.TableRows
import Alvoki.Experiments.L0.TableAllocation
import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.DurableBlob.Native
import Alvoki.Experiments.WAL.Segmented.Native

namespace ExperimentalL0.Native
open System Lifecycle
private abbrev Wal := WalRecoverySlice.Segmented.Native.Handle
private abbrev FileM := ExceptT String IO

@[extern "alvoki_fsync"]
private opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

def pathExists (path : FilePath) : IO Bool :=
  MonadExceptOf.tryCatch (ε := IO.Error) (path.symlinkMetadata >>= fun _ => pure true)
    (fun e => match e with
      | .noFileOrDirectory .. => pure false
      | other => throw other)

private def buildSynced (path : FilePath) (id : UInt64) (rows : Rows) : IO Unit := do
  let remaining ← IO.mkRef rows
  let _ ← ImmutableSSTable.Unified.buildFileSynced path (tableLayout id)
    (nextTableRow remaining.get remaining.set)

private def createTable (dir : FilePath) (rows : Rows) : FileM UInt64 :=
  createTableUnder dir (fun path => liftM (pathExists path))
    (fun path id entries => liftM (buildSynced path id entries))
    (fun parent => liftM (IO.FS.withFile parent .read syncHandle)) rows

def checked (operation : FileM α) : IO α := do
  match ← operation.run with
  | .ok result => return result
  | .error error => throw (IO.userError error)

private def tables (dir : FilePath) : Tables FileM where
  create := createTable dir
  check id := nativeTableAt dir id (fun _ => pure ())
  lookup id key := nativeTableAt dir id (·.lookup key)

def phaseCell (phase : IO.Ref (Phase Wal)) : Cell IO Wal where
  read := phase.get
  swap := phase.swap

def componentCell (phase : IO.Ref (Phase Wal)) : Cell FileM Wal where
  read := liftM (phase.get : IO (Phase Wal))
  swap := fun next => liftM (phase.swap next : IO (Phase Wal))

def storageCallbacks (root : FilePath) : Callbacks FileM Wal :=
  let blob := DurableBlob.native (root / "manifest")
  {
    append handle batch := liftM do
      let _ ← WalRecoverySlice.Segmented.Native.append handle batch
    scan handle := liftM (WalRecoverySlice.Segmented.Native.scan handle)
    openWal := liftM (WalRecoverySlice.Segmented.Native.openExisting (root / "wal"))
    manifest := L0Manifest.backend id {
      publish := fun bytes => liftM (blob.publish bytes)
      reopen := liftM blob.reopen
    }
    tables := tables (root / "tables")
  }

def callbackComponents (root : FilePath) (phase : IO.Ref (Phase Wal)) : Components FileM :=
  (componentCell phase).components "L0 cannot use the WAL in this phase" (storageCallbacks root)

structure Handle where private mk ::
  private ops : Components FileM
  private phase : IO.Ref (Phase Wal)

private def assembled (root : FilePath) (phase : IO.Ref (Phase Wal)) : Handle :=
  ⟨callbackComponents root phase, phase⟩

/-- The private handle actually passed to the callback in withOpen. -/
def Handle.AtRoot (handle : Handle) (root : FilePath) (phase : IO.Ref (Phase Wal)) : Prop :=
  handle = assembled root phase

/-- The recovery action run by the native scope on its fresh phase cell. -/
def recoverAt (root : FilePath) (phase : IO.Ref (Phase Wal)) : IO Session :=
  checked (recover (callbackComponents root phase))

def checkComponentDirectory (root : FilePath) (name : String) : IO Unit := do
  unless (← (root / name).symlinkMetadata).type == .dir do
    throw (IO.userError s!"expected directory {name}")

def checkLockName (path : FilePath) : IO Unit := do
  if ← pathExists path then
    let md ← path.symlinkMetadata
    unless md.type == .file && md.numLinks == 1 do
      throw (IO.userError "expected a singly linked regular L0 lock file")

/-- Resolve and validate the namespace before acquiring its root lock. -/
def validatedRoot (path : FilePath) : IO FilePath := do
  let root ← IO.FS.realPath path
  checkComponentDirectory root "wal"
  checkComponentDirectory root "manifest"
  checkComponentDirectory root "tables"
  checkLockName (root / "l0.lock")
  return root

/-- Exclusive root ownership is held for the entire callback. The caller
supplies an initialized root containing distinct, durably named wal,
manifest, and tables directories. All operations must be sequential.
An escaped handle is offline after the callback ends. -/
def withOpen (path : FilePath) (use : Handle → IO α) : IO α := do
  let root ← validatedRoot path
  let lockPath := root / "l0.lock"
  IO.FS.withFile lockPath .append fun lock => do
    unless ← lock.tryLock do throw (IO.userError "L0 already open")
    let phase ← IO.mkRef (.opening : Phase Wal)
    let handle := assembled root phase
    (phaseCell phase).withSession (IO.userError "L0 cannot publish a session")
      (checked (recover handle.ops)) (use handle)
      WalRecoverySlice.Segmented.Native.close lock.unlock

/-- Acquisition failures precede recovery and the callback. Success exposes
the exact root lock and freshly allocated cell supplied to the shared scope.
The assembled handle stays private except for its propositional identity. -/
theorem withOpen_reached (path : FilePath) (use : Handle → IO α) (start : Void IO.RealWorld) :
    match validatedRoot path start with
    | .error e t => withOpen path use start = .error e t
    | .ok root t =>
      match IO.FS.Handle.mk (root / "l0.lock") .append t with
      | .error e u => withOpen path use start = .error e u
      | .ok lock u =>
        match lock.tryLock true u with
        | .error e v => withOpen path use start = .error e v
        | .ok false v => withOpen path use start = .error (IO.userError "L0 already open") v
        | .ok true v =>
          let fresh := IO.mkRef (.opening : Phase Wal) v
          ∃ handle, handle.AtRoot root fresh.val ∧
            withOpen path use start =
              (phaseCell fresh.val).withSession (IO.userError "L0 cannot publish a session")
                (recoverAt root fresh.val) (use handle)
                WalRecoverySlice.Segmented.Native.close lock.unlock fresh.state := by
  cases resolved : validatedRoot path start with
  | error => simp [withOpen, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved]
  | ok root t =>
    cases opened : IO.FS.Handle.mk (root / "l0.lock") .append t with
    | error => simp [withOpen, IO.FS.withFile, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved, opened]
    | ok lock u =>
      cases acquired : lock.tryLock true u with
      | error =>
        simp [withOpen, IO.FS.withFile, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved, opened, acquired]
      | ok yes v =>
        cases yes
        · simp [withOpen, IO.FS.withFile, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved, opened, acquired]
          rfl
        · simp only [opened, acquired]
          refine ⟨_, rfl, ?_⟩
          simp [withOpen, IO.FS.withFile, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved, opened, acquired]
          rfl

private def update (handle : Handle) (operation : Session → FileM Session) : IO Unit := do
  (phaseCell handle.phase).update (IO.userError "L0 requires reopen")
    (fun session => checked (operation session)) WalRecoverySlice.Segmented.Native.close

def put (handle : Handle) (key value : UInt64) : IO Unit :=
  update handle (fun session => write handle.ops session (key, .put value))

def delete (handle : Handle) (key : UInt64) : IO Unit :=
  update handle (fun session => write handle.ops session (key, .delete))

def flush (handle : Handle) : IO Unit :=
  update handle (ExperimentalL0.flush handle.ops)

def get (handle : Handle) (key : UInt64) : IO (Option UInt64) :=
  checked ((componentCell handle.phase).get "L0 requires reopen" handle.ops key)

/-- Execute public get on the exact world reached by reading its phase
reference. A closed phase never enters the storage lookup. -/
theorem get_afterPhaseRead (handle : Handle) (key : UInt64)
    (phaseRead : (handle.phase.get : IO (Phase Wal)) start = .ok phase entered) :
    get handle key start =
      match phase.session with
      | none => .error (IO.userError "L0 requires reopen") entered
      | some session => checked (ExperimentalL0.get handle.ops session key) entered := by
  let resume (phase : Phase Wal) : FileM (Option UInt64) :=
    match phase.session with
    | some session => ExperimentalL0.get handle.ops session key
    | _ => throw "L0 requires reopen"
  change checked ((liftM (handle.phase.get : IO (Phase Wal)) : FileM (Phase Wal)) >>= resume) start = _
  unfold checked
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  have lifted : (liftM (handle.phase.get : IO (Phase Wal)) : FileM (Phase Wal)).run start =
      .ok (.ok phase) entered := by
    change (match (handle.phase.get : IO (Phase Wal)) start with
      | .ok p world => EST.Out.ok (Except.ok p : Except String (Phase Wal)) world
      | .error error world => EST.Out.error error world) = _
    rw [phaseRead]
  rw [lifted]
  cases phase <;> rfl

/-- A proof consumer may choose arbitrary implementations of the operations
which get cannot reach. Only the lookup field must agree. -/
theorem get_atRoot (binding : Handle.AtRoot handle root ref)
    (phaseRead : (ref.get : IO (Phase Wal)) start = .ok (.online wal session) entered)
    (ops : Components FileM)
    (lookup : ops.tables.lookup = fun id key => nativeTableAt (root / "tables") id (·.lookup key)) :
    get handle key start = (do
      match ← (ExperimentalL0.get ops session key).run with
      | .ok value => pure value
      | .error error => throw (IO.userError error) : IO _) entered := by
  cases binding
  rw [get_afterPhaseRead _ _ phaseRead]
  change checked (ExperimentalL0.get (callbackComponents root ref) session key) entered = _
  have same (ids) : lookupTables (callbackComponents root ref).tables key ids =
      lookupTables ops.tables key ids := by
    induction ids with
    | nil => rfl
    | cons id ids ih =>
      simp only [lookupTables, ← ih]
      rw [lookup]
      rfl
  unfold ExperimentalL0.get
  rw [same]
  change checked (ExperimentalL0.get ops session key) entered = _
  unfold checked
  cases ran : (ExperimentalL0.get ops session key).run entered with
  | error => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ExperimentalL0.get] at ran ⊢; rw [ran]
  | ok r t =>
    cases r <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ExperimentalL0.get] at ran ⊢ <;> rw [ran]

end ExperimentalL0.Native
