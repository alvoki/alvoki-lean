import Alvoki.Experiments.WAL.Recovery
import Std.Sync.Mutex

/-! Experimental one-segment native handle. The caller owns the directory and
must not replace its files while a handle is open. -/
namespace WalRecoverySlice.SingleFile
open System

@[extern "alvoki_fsync"]
opaque Internal.syncHandle (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_wal_unbuffered"]
opaque Internal.disableBuffering (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_read_dir_checked"]
opaque Internal.readDirChecked (path : @& FilePath) : IO (Array IO.FS.DirEntry)

def Internal.openStream (file : FilePath) (mode : IO.FS.Mode) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk file mode
  Internal.disableBuffering h
  return h

private abbrev FileM := ExceptT String IO
private def encodeBytes (xs : Bytes) : ByteArray := ⟨xs.toArray⟩

def Internal.writeAndSync (file : FilePath) (bytes : ByteArray) : IO Unit := do
  let h ← Internal.openStream file .writeNew
  h.write bytes
  h.flush
  Internal.syncHandle h

@[extern "alvoki_wal_truncate_at"]
private opaque truncateAt (h : @& IO.FS.Handle) (count : @& Nat) : IO Unit

/-- Recovery uses a read/write description for reading, truncating and syncing
the segment. The separate append stream owns the append barriers. -/
structure RecoveryIO (m : Type → Type) (handle : Type) where
  readFromStart : handle → m Bytes
  truncateAt : handle → Nat → m Unit
  sync : handle → m Unit

def markerHandle [Monad m] [MonadExceptOf String m]
    (markers : Option (handle × handle)) (slot : Nat) : m handle := do
  let some (a, b) := markers | throw "marker unavailable"
  return if slot == 0 then a else b

@[inline] def recoveryOps [Monad m] [MonadExceptOf String m]
    (io : RecoveryIO m handle) (data : handle) (markers : Option (handle × handle)) : Ops m where
  readData := io.readFromStart data
  readMarker slot := do io.readFromStart (← markerHandle markers slot)
  syncMarker slot := do io.sync (← markerHandle markers slot)
  truncate := io.truncateAt data
  syncData := io.sync data
  append _ := throw "append during recovery"
  writeMarker _ _ := throw "marker write during recovery"

@[inline] def recoverWith [Monad m] [MonadExceptOf String m]
    (io : RecoveryIO m handle) (data : handle) (markers : Option (handle × handle))
    (policy : Policy) : m Decoded :=
  reopen (recoveryOps io data markers) policy

/-- The 1024-byte loop used by Lean's handle reader, with an unfoldable
equation so an interrupted second or later read has its own operand. -/
def Internal.readChunks (h : IO.FS.Handle) (acc : ByteArray) : IO ByteArray := do
  let bytes ← h.read 1024
  if bytes.isEmpty then return acc
  readChunks h (acc ++ bytes)
partial_fixpoint

private def readFromStart (h : IO.FS.Handle) : IO Bytes := do
  h.rewind
  return (← Internal.readChunks h .empty).data.toList

def nativeRecovery : RecoveryIO FileM IO.FS.Handle where
  readFromStart h := readFromStart h
  truncateAt h n := truncateAt h n
  sync h := Internal.syncHandle h

structure AppendFiles (handle : Type) where
  writer : handle
  markers : Option (handle × handle)

def appendFiles (writer _reader : handle) (markers : Option (handle × handle)) : AppendFiles handle :=
  ⟨writer, markers⟩

structure AppendIO (m : Type → Type) (handle : Type) where
  appendFlushed : handle → Bytes → m Unit
  writeFromStart : handle → Bytes → m Unit
  sync : handle → m Unit

@[inline] def appendOps [Monad m] [MonadExceptOf String m]
    (io : AppendIO m handle) (files : AppendFiles handle) : Ops m where
  append := io.appendFlushed files.writer
  syncData := io.sync files.writer
  writeMarker slot bytes := do io.writeFromStart (← markerHandle files.markers slot) bytes
  syncMarker slot := do io.sync (← markerHandle files.markers slot)
  readData := throw "read during append"
  readMarker _ := throw "read during append"
  truncate _ := throw "truncate during append"

@[inline] abbrev writeFlushedWith [Monad m] (write flush : m Unit) : m Unit := do
  write
  flush

@[inline] abbrev writeFromStartWith [Monad m] (rewind writeFlushed : m Unit) : m Unit := do
  rewind
  writeFlushed

private def writeFlushed (h : IO.FS.Handle) (bytes : Bytes) : IO Unit :=
  writeFlushedWith (h.write (encodeBytes bytes)) h.flush

def Internal.nativeAppend : AppendIO FileM IO.FS.Handle where
  appendFlushed h bytes := writeFlushed h bytes
  writeFromStart h bytes := writeFromStartWith (liftM h.rewind) (liftM (writeFlushed h bytes))
  sync h := Internal.syncHandle h

/-- Erase the typed append adapter at a reached writer or marker. These
equations expose the actual rewind, write, flush, and fsync calls. -/
theorem Internal.append_data_run (files : AppendFiles IO.FS.Handle) (b : Bytes) :
    ((appendOps nativeAppend files).append b).run =
      (do files.writer.write ⟨b.toArray⟩; files.writer.flush; return .ok ()) := by
  funext w
  change ((fun x => (Except.ok x : Except String Unit)) <$> writeFlushed files.writer b : IO _) w = _
  simp only [writeFlushed,writeFlushedWith, Functor.map, instMonadEIO._aux_1, Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases run : files.writer.write ⟨b.toArray⟩ w <;> simp only [encodeBytes,run]
  rename_i t
  cases files.writer.flush t <;> rfl

theorem Internal.append_marker_run (files : AppendFiles IO.FS.Handle) (hs : files.markers = some (a,b))
    (slot : Nat) (bytes : Bytes) :
    let h := if slot == 0 then a else b
    ((appendOps nativeAppend files).writeMarker slot bytes).run =
      (do h.rewind; h.write ⟨bytes.toArray⟩; h.flush; return .ok ()) := by
  intro h
  have picked : markerHandle files.markers slot = (pure h : FileM _) := by simp [markerHandle,hs,h]
  change ((markerHandle files.markers slot >>= fun file => do
    file.rewind; writeFlushed file bytes) : FileM Unit).run = _
  have bindPure {α β} (v : α) (k : α → FileM β) : (pure v >>= k) = k v := rfl
  rw [picked,bindPure,ExceptT.run_bind]
  have liftRun (act : IO Unit) : (liftM act : FileM Unit).run = (do return Except.ok (← act) : IO (Except String Unit)) := rfl
  simp only [liftRun]
  funext w
  simp only [writeFlushed,writeFlushedWith,encodeBytes,Bind.bind,instMonadEIO._aux_13,EST.bind,Pure.pure,instMonadEIO._aux_5,EST.pure]
  cases h.rewind w <;> simp only [EST.bind]
  rename_i t
  cases h.write ⟨bytes.toArray⟩ t <;> simp only
  rename_i u
  cases h.flush u <;> rfl

theorem Internal.append_sync_marker_run (files : AppendFiles IO.FS.Handle) (hs : files.markers = some (a,b))
    (slot : Nat) :
    ((appendOps nativeAppend files).syncMarker slot).run =
      (do syncHandle (if slot == 0 then a else b); return .ok ()) := by
  simp only [appendOps,nativeAppend,markerHandle,hs,ExceptT.run_bind]
  funext w
  change ((fun x => (Except.ok x : Except String Unit)) <$> syncHandle _ : IO _) w = _
  cases syncHandle (if slot == 0 then a else b) w <;> rfl

def checked (action : FileM α) : IO α := do
  match ← action.run with
  | .ok value => return value
  | .error error => throw <| IO.userError error

inductive Phase (handle payload : Type) where
  | active (lock : handle) (stored : payload) (cursor : Cursor) (entries : List Bytes)
  | poisoned (lock : handle)
  | closed

/-- An alias of a handle shares its phase and mutex; closing any alias closes all. -/
structure Handle where private mk ::
  private policy : Policy
  private state : IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle))
  private mutex : Std.BaseMutex

private def withMutex (h : Handle) (action : IO α) : IO α := do
  h.mutex.lock
  try action finally h.mutex.unlock

inductive OpenTarget where
  | lock | policy | reader | writer | marker0 | marker1 | directory
  deriving DecidableEq

def OpenTarget.location (dir : FilePath) : OpenTarget → FilePath × IO.FS.Mode
  | .lock => (dir / "lock", .append)
  | .policy => (dir / "policy", .read)
  | .reader => (dir / "segment", .readWrite)
  | .writer => (dir / "segment", .append)
  | .marker0 => (dir / "commit.0", .readWrite)
  | .marker1 => (dir / "commit.1", .readWrite)
  | .directory => (dir, .read)

/-- Acquisition and barriers shared by the native adapter and the proof model. -/
structure OpenIO (m : Type → Type) (handle : Type) where
  openFile : OpenTarget → FilePath → IO.FS.Mode → m handle
  unbuffered : handle → m Unit
  readPolicy : FilePath → handle → m String
  tryLock : handle → m Bool
  unlock : handle → m Unit
  sync : handle → m Unit

@[inline] def OpenIO.openTarget (io : OpenIO m handle) (dir : FilePath) (target : OpenTarget) : m handle :=
  let (path, mode) := target.location dir
  io.openFile target path mode

structure Opened (handle : Type) (payload : Type := Unit) where
  lock : handle
  policy : Policy
  reader : handle
  writer : handle
  markers : Option (handle × handle)
  recovered : Decoded
  phase : Phase handle payload

@[inline] def acquireWith [Monad m] [MonadExceptOf String m]
    (io : OpenIO m handle) (dir : FilePath) : m handle := do
  let lock ← io.openTarget dir .lock
  let granted ← io.tryLock lock
  if granted then pure lock else throw "WAL already open"

structure OpenFiles (handle : Type) where
  stamp : handle
  policy : Policy
  reader : handle
  writer : handle
  markers : Option (handle × handle)

@[inline] def openFilesWith [Monad m] [MonadExceptOf String m] (io : OpenIO m handle)
    (dir : FilePath) : m (OpenFiles handle) := do
  let stamp ← io.openTarget dir .policy
  let policy ← match ← io.readPolicy (dir / "policy") stamp with
    | "v3 log" => pure Policy.logOnly
    | "v3 boundary" => pure Policy.boundary
    | _ => throw "unrecognized WAL policy"
  let reader ← io.openTarget dir .reader
  io.unbuffered reader
  let writer ← io.openTarget dir .writer
  io.unbuffered writer
  let markers ← if policy == .boundary then do
    let a ← io.openTarget dir .marker0
    io.unbuffered a
    let b ← io.openTarget dir .marker1
    io.unbuffered b
    pure (some (a, b))
    else pure none
  return ⟨stamp, policy, reader, writer, markers⟩

@[inline] def settleWith [Monad m] (io : OpenIO m handle) (dir : FilePath)
    (stamp : handle) : m Unit := do
  io.sync stamp
  io.sync (← io.openTarget dir .directory)

@[inline] def installWith [Monad m] [MonadExceptOf String m] (io : OpenIO m handle)
    (recover : Policy → handle → handle → Option (handle × handle) → m Decoded)
    (stored : handle → handle → Option (handle × handle) → payload)
    (dir : FilePath) (lock : handle) : m (Opened handle payload) := do
  let files ← openFilesWith io dir
  let recovered ← recover files.policy files.reader files.writer files.markers
  -- Settle policy bytes and the visible file names before installing a handle.
  settleWith io dir files.stamp
  let phase := Phase.active lock (stored files.writer files.reader files.markers)
    recovered.cursor recovered.batches
  return ⟨lock, files.policy, files.reader, files.writer, files.markers, recovered, phase⟩

@[inline] def openExistingWith [Monad m] [MonadExceptOf String m]
    (io : OpenIO m handle) (attempt : {α : Type} → m α → m (Except error α))
    (rethrow : error → m ready)
    (recover : Policy → handle → handle → Option (handle × handle) → m Decoded)
    (stored : handle → handle → Option (handle × handle) → payload)
    (makeReady : Opened handle payload → m ready) (dir : FilePath) : m ready := do
  let lock ← acquireWith io dir
  match ← attempt (installWith io recover stored dir lock >>= makeReady) with
  | .ok ready => return ready
  | .error err =>
    let _ ← attempt (io.unlock lock)
    rethrow err

def nativeOpen : OpenIO FileM IO.FS.Handle where
  openFile _ path mode := IO.FS.Handle.mk path mode
  unbuffered h := Internal.disableBuffering h
  readPolicy path h := do
    let bytes ← Internal.readChunks h .empty
    match String.fromUTF8? bytes with
    | some text => return text
    | none => throw s!"Tried to read file '{path}' containing non UTF-8 data."
  tryLock h := h.tryLock
  unlock h := h.unlock
  sync h := Internal.syncHandle h

def recoverNative (policy : Policy) (reader _writer : IO.FS.Handle)
    (markers : Option (IO.FS.Handle × IO.FS.Handle)) : FileM Decoded :=
  recoverWith nativeRecovery reader markers policy

@[inline] def storeReadyWith [Monad m] {ref mutex : Type} (newRef : Phase handle payload → m ref)
    (newMutex : m mutex) (ready : Opened handle payload) : m (ref × mutex) := do
  let state ← newRef ready.phase
  return (state, ← newMutex)

def Internal.installReady (ready : Opened IO.FS.Handle (AppendFiles IO.FS.Handle)) : IO Handle := do
  let (state, mutex) ← storeReadyWith (m := BaseIO) IO.mkRef Std.BaseMutex.new ready
  return ⟨ready.policy, state, mutex⟩

/-- The handle contains exactly the phase cell and mutex allocated by the
install step; proofs compare this construction without exposing raw handles
to clients as an executable constructor. -/
def Handle.Assembled (h : Handle) (policy : Policy)
    (ref : IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle))) (mutex : Std.BaseMutex) : Prop :=
  h = ⟨policy, ref, mutex⟩

theorem Handle.Assembled.unique {h : Handle} (one : h.Assembled p r m) (two : h.Assembled p' r' m') :
    p = p' ∧ r = r' ∧ m = m' := Handle.mk.inj (one.symm.trans two)

theorem installReady_run (ready : Opened IO.FS.Handle (AppendFiles IO.FS.Handle))
    (w : Void IO.RealWorld) :
    let allocated := (IO.mkRef ready.phase : BaseIO _) w
    let guard := Std.BaseMutex.new allocated.state
    ∃ handle, Internal.installReady ready w = .ok handle guard.state ∧
      Handle.Assembled handle ready.policy allocated.val guard.val :=
  ⟨_, rfl, rfl⟩

def Internal.acquire (dir : FilePath) : IO IO.FS.Handle := checked (acquireWith nativeOpen dir)

def Internal.install (dir : FilePath) (lock : IO.FS.Handle) : IO Handle :=
  checked (installWith nativeOpen recoverNative appendFiles dir lock) >>= Internal.installReady

/-- Open a previously initialized directory, holding a nonblocking exclusive file
lock through recovery and until close. Failure releases the lock. -/
def openExisting (dir : FilePath) : IO Handle :=
  checked <| openExistingWith nativeOpen
    (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO _)) recoverNative appendFiles (fun ready => Internal.installReady ready) dir

/-- Initialize the durable contents before the single-file installation
schedule acquires its reader, writer and marker descriptions. -/
@[inline] def initializeFilesWith [Monad m] (writeDurable : FilePath → ByteArray → m Unit)
    (dir : FilePath) (policy : Policy) : m Unit := do
  writeDurable (dir / "policy") (if policy == .boundary then "v3 boundary" else "v3 log").toUTF8
  writeDurable (dir / "segment") ByteArray.empty
  if policy == .boundary then
    writeDurable (dir / "commit.0") (encodeBytes (encodeMarker 0 0))
    writeDurable (dir / "commit.1") ByteArray.empty

@[inline] def prepareCreateWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error) (list : FilePath → m (Array String))
    (writeDurable : FilePath → ByteArray → m Unit)
    (dir : FilePath) (policy : Policy) : m Unit := do
  let names ← list dir
  if names.any (· != "lock") then
    throw (invalid "WAL directory is not empty")
  else initializeFilesWith writeDurable dir policy

/-- The lock belongs to the create scope until the ready handle is returned. -/
@[inline] def createWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error) (acquire : m lock) (unlock : lock → m Unit)
    (list : FilePath → m (Array String)) (writeDurable : FilePath → ByteArray → m Unit)
    (install : FilePath → lock → m ready) (dir : FilePath) (policy : Policy) : m ready := do
  let lock ← acquire
  tryCatchThe error (prepareCreateWith invalid list writeDurable dir policy >>= fun _ => install dir lock)
    (fun err => do
      tryCatchThe error (unlock lock) (fun _ => pure ())
      throw err)

/-- Initialize an empty caller-owned directory. Existing files are never replaced;
an interrupted initialization is not automatically retried. -/
def create (dir : FilePath) (policy : Policy) : IO Handle :=
  createWith (error := IO.Error) IO.userError (Internal.acquire dir) (·.unlock)
    (fun path => do return (← Internal.readDirChecked path).map (·.fileName))
    Internal.writeAndSync Internal.install dir policy

@[inline] def appendWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload)
    (store : Phase handle payload → m Unit)
    (run : payload → Cursor → m Cursor)
    (payload : Bytes) : m Unit := do
  match phase with
  | .closed => throw "WAL closed"
  | .poisoned _ => throw "WAL poisoned; reopen required"
  | .active lock files cursor entries =>
    store (.poisoned lock) >>= fun _ => do
      let next ← run files cursor
      store (.active lock files next (entries ++ [payload]))

/-- An ACK follows the required barriers. Errors leave the shared phase poisoned. -/
def append (h : Handle) (payload : Bytes) : IO Unit := withMutex h do
  checked (appendWith (← h.state.get) h.state.set
    (fun files cursor => appendBatch (appendOps Internal.nativeAppend files) h.policy cursor payload) payload)

/-- Execution of a returned public append on the exact active ref. The
phase becomes poisoned before the first write and is reinstalled only
after the worker's completed barriers. The mutex is released on both channels. -/
theorem append_active_run (bound : h.Assembled policy cell mutex) (start : Void IO.RealWorld)
    (active : ((cell.get : BaseIO _) (mutex.lock start).state).val = .active fd files cursor entries)
    (batch : Bytes) :
    let read := (cell.get : BaseIO _) (mutex.lock start).state
    let began := ((cell.set (.poisoned fd) : BaseIO Unit) read.state).state
    append h batch start =
      match (appendBatch (appendOps Internal.nativeAppend files) policy cursor batch).run began with
      | .error e t => .error e (mutex.unlock t).state
      | .ok (.error err) t => .error (IO.userError err) (mutex.unlock t).state
      | .ok (.ok next) t =>
        let stored := ((cell.set (.active fd files next (entries ++ [batch])) : BaseIO Unit) t).state
        .ok () (mutex.unlock stored).state := by
  subst h
  let h : Handle := ⟨policy, cell, mutex⟩
  let locked := (mutex.lock start).state
  let read := (cell.get : BaseIO _) locked
  let began := ((cell.set (.poisoned fd) : BaseIO Unit) read.state).state
  have withMutex_run (a : IO Unit) : withMutex h a start =
      match a locked with
      | .ok x t => .ok x (h.mutex.unlock t).state
      | .error e t => .error e (h.mutex.unlock t).state := by
    have base (a : BaseIO Unit) (w : Void IO.RealWorld) :
        (liftM a : IO Unit) w = .ok (a w).val (a w).state := by
      change BaseIO.toEIO a w = _
      cases ran : a w
      simp [BaseIO.toEIO, ran]
    unfold withMutex
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, base, tryFinally,
      tryFinally', MonadFinally.tryFinally', instMonadFinallyEIO._aux_1,
      Functor.map, instMonadEIO._aux_1]
    cases a (h.mutex.lock start).state <;> rfl
  dsimp only
  unfold append
  rw [withMutex_run]
  have readRun : (cell.get : IO _) locked = .ok read.val read.state := rfl
  have poison : (cell.set (.poisoned fd) : FileM Unit).run read.state = .ok (.ok ()) began := rfl
  change read.val = _ at active
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, readRun, active, appendWith]
  unfold checked
  simp only [ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont, Bind.bind, instMonadEIO._aux_13, EST.bind] at poison ⊢
  rw [poison]
  simp only
  cases issued : (appendBatch (appendOps Internal.nativeAppend files) policy cursor batch).run began with
  | error => simp only [ExceptT.run] at issued; dsimp only [began, read, locked] at issued ⊢; simp only [EST.bind, issued]; rfl
  | ok response t => simp only [ExceptT.run] at issued; dsimp only [began, read, locked] at issued ⊢; simp only [EST.bind, issued, ExceptT.bindCont]; cases response <;> rfl

def scanWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload) : m (List Bytes) :=
  match phase with
  | .active _ _ _ entries => pure entries
  | .closed => throw "WAL closed"
  | .poisoned _ => throw "WAL poisoned; reopen required"

@[inline] def closeWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload)
    (store : Phase handle payload → m Unit) (unlock : handle → m Unit) : m Unit := do
  match phase with
  | .closed => throw "WAL closed"
  | .active lock _ _ _ | .poisoned lock => store .closed >>= fun _ => unlock lock

/-- Return the confirmed history from the last successful recovery and appends. -/
def scan (h : Handle) : IO (List Bytes) := withMutex h do
  checked (scanWith (← h.state.get))

/-- A read of the allocated, active phase under its own mutex returns the
stored scan and preserves the actual mutex finalizer's reached world. -/
theorem scan_active_run (bound : h.Assembled policy cell mutex) (start : Void IO.RealWorld)
    (active : ((cell.get : BaseIO _) (mutex.lock start).state).val =
      Phase.active lock files cursor entries) :
    scan h start = .ok entries
      (mutex.unlock ((cell.get : BaseIO _) (mutex.lock start).state).state).state := by
  subst h
  let locked := (mutex.lock start).state
  let read := (cell.get : BaseIO _) locked
  have readRun : (cell.get : IO _) locked = .ok read.val read.state := rfl
  have checkedRun : checked (scanWith read.val) read.state = .ok entries read.state := by
    change read.val = _ at active
    rw [active]
    rfl
  have base (a : BaseIO Unit) (w : Void IO.RealWorld) :
      (liftM a : IO Unit) w = .ok (a w).val (a w).state := by
    change BaseIO.toEIO a w = _
    cases ran : a w
    simp [BaseIO.toEIO, ran]
  unfold scan withMutex
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, base, tryFinally,
    tryFinally', MonadFinally.tryFinally', instMonadFinallyEIO._aux_1,
    Functor.map, instMonadEIO._aux_1]
  dsimp only [locked] at readRun
  rw [readRun]
  simp only
  rw [checkedRun]
  rfl

def close (h : Handle) : IO Unit := withMutex h do
  checked (closeWith (← h.state.get) h.state.set (fun lock => lock.unlock))

/-- Proof-only identification of the private phase and mutex. -/
def Handle.Binds (h : Handle) (cell : IO.Ref (Phase IO.FS.Handle (AppendFiles IO.FS.Handle)))
    (mutex : Std.BaseMutex) : Prop := h.state = cell ∧ h.mutex = mutex

theorem Handle.bindings (h : Handle) : ∃ cell mutex, h.Binds cell mutex := ⟨_, _, rfl, rfl⟩

/-- Public close operates on the phase under the very same mutex. A live
child is marked closed before unlocking its description. A previously
closed child only reports the primary error. Both paths leave the mutex. -/
theorem close_run {h : Handle} (binding : h.Binds cell mutex) (start : Void IO.RealWorld) :
    close h start =
      let locked := (mutex.lock start).state
      let read := (cell.get : BaseIO _) locked
      let release := fun (lock : IO.FS.Handle) =>
        lock.unlock ((cell.set .closed : BaseIO Unit) read.state).state
      let result := match read.val with
        | .closed => EST.Out.error (IO.userError "WAL closed") read.state
        | .active fd _ _ _ | .poisoned fd => release fd
      match result with
      | .ok x t => .ok x (mutex.unlock t).state
      | .error e t => .error e (mutex.unlock t).state := by
  obtain ⟨rfl, rfl⟩ := binding
  let locked := (h.mutex.lock start).state
  let read := (h.state.get : BaseIO _) locked
  let call := fun (p : Phase IO.FS.Handle (AppendFiles IO.FS.Handle)) =>
    checked (closeWith p h.state.set (fun lock => lock.unlock))
  have withMutex_run (a : IO Unit) : withMutex h a start =
      match a locked with
      | .ok x t => .ok x (h.mutex.unlock t).state
      | .error e t => .error e (h.mutex.unlock t).state := by
    have base (a : BaseIO Unit) (w : Void IO.RealWorld) :
        (liftM a : IO Unit) w = .ok (a w).val (a w).state := by
      change BaseIO.toEIO a w = _
      cases ran : a w
      simp [BaseIO.toEIO, ran]
    unfold withMutex
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, base, tryFinally,
      tryFinally', MonadFinally.tryFinally', instMonadFinallyEIO._aux_1,
      Functor.map, instMonadEIO._aux_1]
    cases a (h.mutex.lock start).state <;> rfl
  unfold close
  rw [withMutex_run]
  have readRun : (h.state.get : IO _) locked = .ok read.val read.state := rfl
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, readRun]
  change (match call read.val read.state with
    | .ok x t => EST.Out.ok x (h.mutex.unlock t).state
    | .error e t => EST.Out.error e (h.mutex.unlock t).state) = _
  dsimp only [locked, read]
  cases phase : (h.state.get : BaseIO _) (h.mutex.lock start).state with
  | mk p t =>
    cases p with
    | closed => rfl
    | active fd files cursor entries | poisoned fd =>
      let after := ((h.state.set .closed : BaseIO Unit) t).state
      have setRun : (h.state.set .closed : FileM Unit).run t = .ok (.ok ()) after := rfl
      have finish : checked ((h.state.set .closed : FileM Unit) >>= fun _ => (liftM fd.unlock : FileM Unit)) t =
          fd.unlock after := by
        unfold checked
        rw [ExceptT.run_bind]
        simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, setRun]
        cases u : fd.unlock after with
        | error e v =>
          have lifted : (liftM fd.unlock : FileM Unit).run after = .error e v := by
            change (Except.ok <$> fd.unlock : IO (Except String Unit)) after = _
            simp [Functor.map, instMonadEIO._aux_1, EST.bind, u]
          rw [lifted]
        | ok x v =>
          have lifted : (liftM fd.unlock : FileM Unit).run after = .ok (.ok x) v := by
            change (Except.ok <$> fd.unlock : IO (Except String Unit)) after = _
            simp [Functor.map, instMonadEIO._aux_1, EST.bind, EST.pure, u]
          rw [lifted]
          rfl
      simp only [call, closeWith]
      rw [finish]

end WalRecoverySlice.SingleFile
