import Alvoki.Experiments.WAL.Recovery
import Std.Sync.Mutex

/-! Experimental one-segment native handle. The caller owns the directory and
must not replace its files while a handle is open. -/
namespace WalRecoverySlice.SingleFile
open System

@[extern "alvoki_fsync"]
private opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_wal_unbuffered"]
private opaque disableBuffering (h : @& IO.FS.Handle) : IO Unit

private def openStream (file : FilePath) (mode : IO.FS.Mode) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk file mode
  disableBuffering h
  return h

private abbrev FileM := ExceptT String IO
private def encodeBytes (xs : Bytes) : ByteArray := ⟨xs.toArray⟩

private def writeAndSync (file : FilePath) (bytes : ByteArray) : IO Unit := do
  let h ← openStream file .writeNew
  h.write bytes
  h.flush
  syncHandle h

@[extern "alvoki_wal_truncate_at"]
private opaque truncateAt (h : @& IO.FS.Handle) (count : @& Nat) : IO Unit

/-- Recovery uses a read/write description for reading, truncating and syncing
the segment. The separate append stream owns the append barriers. -/
structure RecoveryIO (m : Type → Type) (handle : Type) where
  readFromStart : handle → m Bytes
  truncateAt : handle → Nat → m Unit
  sync : handle → m Unit

private def markerHandle [Monad m] [MonadExceptOf String m]
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

private def readFromStart (h : IO.FS.Handle) : IO Bytes := do
  h.rewind
  return (← h.readBinToEnd).data.toList

private def nativeRecovery : RecoveryIO FileM IO.FS.Handle where
  readFromStart h := readFromStart h
  truncateAt h n := truncateAt h n
  sync h := syncHandle h

private def fileOps (writer reader : IO.FS.Handle) (markers : Option (IO.FS.Handle × IO.FS.Handle)) : Ops FileM where
  append xs := do
    writer.write (encodeBytes xs)
    writer.flush
  syncData := syncHandle writer
  writeMarker slot bytes := do
    let some (a, b) := markers | throw "marker unavailable"
    let h := if slot == 0 then a else b
    h.rewind
    h.write (encodeBytes bytes)
    h.flush
  syncMarker slot := do
    let some (a, b) := markers | throw "marker unavailable"
    syncHandle (if slot == 0 then a else b)
  readData := readFromStart reader
  readMarker slot := do readFromStart (← markerHandle markers slot)
  truncate n := truncateAt reader n

private def checked (action : FileM α) : IO α := do
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
  private state : IO.Ref (Phase IO.FS.Handle (Ops FileM))
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
    (io : OpenIO m handle) (attempt : m ready → m (Except error ready))
    (rethrow : error → m ready)
    (recover : Policy → handle → handle → Option (handle × handle) → m Decoded)
    (stored : handle → handle → Option (handle × handle) → payload)
    (makeReady : Opened handle payload → m ready) (dir : FilePath) : m ready := do
  let lock ← acquireWith io dir
  match ← attempt (installWith io recover stored dir lock >>= makeReady) with
  | .ok ready => return ready
  | .error err =>
    io.unlock lock
    rethrow err

private def nativeOpen : OpenIO FileM IO.FS.Handle where
  openFile _ path mode := IO.FS.Handle.mk path mode
  unbuffered h := disableBuffering h
  readPolicy path h := do
    let bytes ← h.readBinToEnd
    match String.fromUTF8? bytes with
    | some text => return text
    | none => throw s!"Tried to read file '{path}' containing non UTF-8 data."
  tryLock h := h.tryLock
  unlock h := h.unlock
  sync h := syncHandle h

private def recoverNative (policy : Policy) (reader _writer : IO.FS.Handle)
    (markers : Option (IO.FS.Handle × IO.FS.Handle)) : FileM Decoded :=
  recoverWith nativeRecovery reader markers policy

@[inline] def storeReadyWith [Monad m] {ref mutex : Type} (newRef : Phase handle payload → m ref)
    (newMutex : m mutex) (ready : Opened handle payload) : m (ref × mutex) := do
  let state ← newRef ready.phase
  return (state, ← newMutex)

private def installReady (ready : Opened IO.FS.Handle (Ops FileM)) : IO Handle := do
  let (state, mutex) ← storeReadyWith (m := BaseIO) IO.mkRef Std.BaseMutex.new ready
  return ⟨ready.policy, state, mutex⟩

private def acquire (dir : FilePath) : IO IO.FS.Handle := checked (acquireWith nativeOpen dir)

private def install (dir : FilePath) (lock : IO.FS.Handle) : IO Handle :=
  checked (installWith nativeOpen recoverNative fileOps dir lock) >>= installReady

/-- Open a previously initialized directory, holding a nonblocking exclusive file
lock through recovery and until close. Failure releases the lock. -/
def openExisting (dir : FilePath) : IO Handle :=
  checked <| openExistingWith nativeOpen
    (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO _)) recoverNative fileOps (fun ready => installReady ready) dir

/-- Initialize an empty caller-owned directory. Existing files are never replaced;
an interrupted initialization is not automatically retried. -/
def create (dir : FilePath) (policy : Policy) : IO Handle := do
  let lock ← acquire dir
  try
    let entries ← dir.readDir
    if entries.any (fun entry => entry.fileName != "lock") then
      throw <| IO.userError "WAL directory is not empty"
    writeAndSync (dir / "policy") (if policy == .boundary then "v3 boundary" else "v3 log").toUTF8
    writeAndSync (dir / "segment") ByteArray.empty
    if policy == .boundary then
      writeAndSync (dir / "commit.0") (encodeBytes (encodeMarker 0 0))
      writeAndSync (dir / "commit.1") ByteArray.empty
    install dir lock
  catch e =>
    lock.unlock
    throw e

/-- An ACK means that the schedule's policy-specific durability barriers succeeded.
Any error poisons this handle; reopen to determine the durable history. -/
def append (h : Handle) (payload : Bytes) : IO Unit := withMutex h do
  match ← h.state.get with
  | .closed => throw <| IO.userError "WAL closed"
  | .poisoned _ => throw <| IO.userError "WAL poisoned; reopen required"
  | .active lock ops cursor entries =>
    -- Set the poison before entering IO, so every exceptional exit is conservative.
    h.state.set (.poisoned lock)
    let next ← checked (appendBatch ops h.policy cursor payload)
    h.state.set (.active lock ops next (entries ++ [payload]))

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

def close (h : Handle) : IO Unit := withMutex h do
  checked (closeWith (← h.state.get) h.state.set (fun lock => lock.unlock))

end WalRecoverySlice.SingleFile
