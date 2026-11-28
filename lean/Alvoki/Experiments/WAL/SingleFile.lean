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

@[extern "alvoki_read_dir_checked"]
private opaque readDirChecked (path : @& FilePath) : IO (Array IO.FS.DirEntry)

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
  readData : handle → m Bytes
  readMarker : handle → m Bytes
  truncateAt : handle → Nat → m Unit
  sync : handle → m Unit

private def markerHandle [Monad m] [MonadExceptOf String m]
    (markers : Option (handle × handle)) (slot : Nat) : m handle := do
  let some (a, b) := markers | throw "marker unavailable"
  return if slot == 0 then a else b

@[inline] def recoveryOps [Monad m] [MonadExceptOf String m]
    (io : RecoveryIO m handle) (data : handle) (markers : Option (handle × handle)) : Ops m where
  readData := io.readData data
  readMarker slot := do io.readMarker (← markerHandle markers slot)
  syncMarker slot := do io.sync (← markerHandle markers slot)
  truncate := io.truncateAt data
  syncData := io.sync data
  append _ := throw "append during recovery"
  writeMarker _ _ := throw "marker write during recovery"

@[inline] def recoverWith [Monad m] [MonadExceptOf String m]
    (io : RecoveryIO m handle) (data : handle) (markers : Option (handle × handle))
    (policy : Policy) : m Decoded :=
  reopen (recoveryOps io data markers) policy

/-- A marker can select at most 65535 bytes. The extra byte witnesses a
suffix. Drain oversized input in fixed chunks to retain read-error priority. -/
private def readPrefixFromStart (h : IO.FS.Handle) (limit : USize) : IO Bytes := do
  h.rewind
  let bytes ← h.read limit
  if bytes.size == limit.toNat then
    repeat
      if (← h.read 8192).isEmpty then break
  return bytes.data.toList

private def nativeRecovery : RecoveryIO FileM IO.FS.Handle where
  readData h := readPrefixFromStart h 65536
  readMarker h := readPrefixFromStart h (markerSize + 1).toUSize
  truncateAt h n := truncateAt h n
  sync h := syncHandle h

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

private def writeFlushed (h : IO.FS.Handle) (bytes : Bytes) : IO Unit := do
  h.write (encodeBytes bytes)
  h.flush

private def nativeAppend : AppendIO FileM IO.FS.Handle where
  appendFlushed h bytes := writeFlushed h bytes
  writeFromStart h bytes := do
    h.rewind
    writeFlushed h bytes
  sync h := syncHandle h

private def checked (action : FileM α) : IO α := do
  match ← action.run with
  | .ok value => return value
  | .error error => throw <| IO.userError error

inductive Phase (handle payload : Type) (history : Type := List Bytes) where
  | active (lock : handle) (stored : payload) (cursor : Cursor) (entries : history)
  | poisoned (lock : handle)
  | closed

private structure NativeFiles where
  append : AppendFiles IO.FS.Handle
  reader : IO.FS.Handle

/-- An alias of a handle shares its phase and mutex; closing any alias closes all. -/
structure Handle where private mk ::
  private policy : Policy
  private state : IO.Ref (Phase IO.FS.Handle NativeFiles Unit)
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

private def installReady (ready : Opened IO.FS.Handle (AppendFiles IO.FS.Handle)) : IO Handle := do
  let state ← IO.mkRef (.active ready.lock
    ⟨appendFiles ready.writer ready.reader ready.markers, ready.reader⟩ ready.recovered.cursor ())
  return ⟨ready.policy, state, ← Std.BaseMutex.new⟩

private def acquire (dir : FilePath) : IO IO.FS.Handle := checked (acquireWith nativeOpen dir)

private def install (dir : FilePath) (lock : IO.FS.Handle) : IO Handle :=
  checked (installWith nativeOpen recoverNative appendFiles dir lock) >>= installReady

/-- Fold validated batches strictly after the given base position. -/
def foldBatchesFrom (step : α → Nat → Bytes → α) (base : Nat) (seed : α) : List Bytes → α
  | [] => seed
  | batch :: rest =>
    let pos := base + 1
    foldBatchesFrom step pos (step seed pos batch) rest

def foldBatches (batches : List Bytes) (seed : α) (step : α → Nat → Bytes → α) : α :=
  foldBatchesFrom step 0 seed batches

private def openLoaded (dir : FilePath)
    (finish : Opened IO.FS.Handle (AppendFiles IO.FS.Handle) → IO α) : IO α :=
  checked <| openExistingWith nativeOpen
    (fun action => (checked action).toBaseIO)
    (fun err => liftM (throw err : IO _)) recoverNative appendFiles (fun ready => finish ready) dir

/-- Open a previously initialized directory with exclusive ownership.
The recovery worker settles the selected image before the handle is returned. -/
def openExistingPosition (dir : FilePath) : IO (Handle × Cursor) :=
  openLoaded dir fun ready => do
    return (← installReady ready, ready.recovered.cursor)

def openExisting (dir : FilePath) : IO Handle :=
  return (← openExistingPosition dir).1

/-- Fold the recovered segment without retaining its batch list in the handle.
The step is pure and its result is exposed only after successful recovery. -/
def openExistingFold (dir : FilePath) (seed : α) (step : α → Nat → Bytes → α) :
    IO (Handle × Cursor × α) :=
  openLoaded dir fun ready => do
    let result := foldBatches ready.recovered.batches seed step
    return (← installReady ready, ready.recovered.cursor, result)

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
  createWith (error := IO.Error) IO.userError (acquire dir) (·.unlock)
    (fun path => do return (← readDirChecked path).map (·.fileName))
    writeAndSync install dir policy

@[inline] def appendStateWith [Monad m] [MonadExceptOf String m]
    (phase : Phase handle payload history)
    (store : Phase handle payload history → m Unit)
    (run : payload → Cursor → m Cursor) (advance : history → history) : m Unit := do
  match phase with
  | .closed => throw "WAL closed"
  | .poisoned _ => throw "WAL poisoned; reopen required"
  | .active lock files cursor entries =>
    store (.poisoned lock)
    let next ← run files cursor
    store (.active lock files next (advance entries))

@[inline] def appendWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload)
    (store : Phase handle payload → m Unit)
    (run : payload → Cursor → m Cursor)
    (payload : Bytes) : m Unit :=
  appendStateWith phase store run (· ++ [payload])

/-- An ACK follows the required barriers. Errors leave the shared phase poisoned. -/
def append (h : Handle) (payload : Bytes) : IO Unit := withMutex h do
  checked (appendStateWith (← h.state.get) h.state.set
    (fun files cursor => appendBatch (appendOps nativeAppend files.append) h.policy cursor payload) id)

def scanWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload) : m (List Bytes) :=
  match phase with
  | .active _ _ _ entries => pure entries
  | .closed => throw "WAL closed"
  | .poisoned _ => throw "WAL poisoned; reopen required"

@[inline] def closeWith [Monad m] [MonadExceptOf String m] (phase : Phase handle payload history)
    (store : Phase handle payload history → m Unit) (unlock : handle → m Unit) : m Unit := do
  match phase with
  | .closed => throw "WAL closed"
  | .active lock _ _ _ | .poisoned lock => store .closed >>= fun _ => unlock lock

@[extern "alvoki_wal_read_installed"]
private opaque readInstalled (h : @& IO.FS.Handle) (count : USize) : IO ByteArray

private def withReady (h : Handle) (run : NativeFiles → Cursor → IO α) : IO α := withMutex h do
  match ← h.state.get with
  | .active _ files cursor _ => run files cursor
  | .closed => throw (IO.userError "WAL closed")
  | .poisoned _ => throw (IO.userError "WAL poisoned; reopen required")

def position (h : Handle) : IO Cursor := withReady h fun _ cursor => pure cursor

private def decodedOrError (decoded : Except String Decoded) : IO Decoded :=
  match decoded with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Read the installed extent on the reader acquired by open. Positional reads
leave the descriptor offset alone. A failure leaves the active phase intact. -/
def scanFold (h : Handle) (seed : α) (step : α → Nat → Bytes → α) : IO α :=
  withReady h fun files cursor => do
    let bytes ← readInstalled files.reader cursor.endPos.toUSize
    let decoded ← decodedOrError (WalRecoverySlice.scan bytes.data.toList cursor.endPos .boundary)
    unless decoded.cursor == cursor do throw (IO.userError "installed WAL cursor mismatch")
    return foldBatches decoded.batches seed step

/-- Read a sealed child's exact committed contents. The segmented caller owns
the root and validates the child binding before entering this read-only scope. -/
def scanSealedFold (dir : FilePath) (policy : Policy) (count : Nat)
    (seed : α) (step : α → Nat → Bytes → α) : IO α := do
  let marker ← if policy == .boundary then do
    let a ← IO.FS.withFile (dir / "commit.0") .read fun h =>
      readPrefixFromStart h (markerSize + 1).toUSize
    let b ← IO.FS.withFile (dir / "commit.1") .read fun h =>
      readPrefixFromStart h (markerSize + 1).toUSize
    match selectMarker a b with
    | .ok value => pure (some value)
    | .error error => throw (IO.userError error)
    else pure none
  let bytes ← IO.FS.withFile (dir / "segment") .read fun h => readPrefixFromStart h 65536
  let endPos := marker.map Marker.endPos |>.getD bytes.length
  let decoded ← decodedOrError (WalRecoverySlice.scan bytes endPos .boundary)
  unless bytes.length == endPos && decoded.cursor.nextSeq == count + 1 &&
      (marker.all fun selected => selected.lastSeq == count) do
    throw (IO.userError "sealed WAL cursor mismatch")
  return foldBatches decoded.batches seed step

def scan (h : Handle) : IO (List Bytes) := do
  return (← scanFold h [] (fun acc _ batch => batch :: acc)).reverse

def close (h : Handle) : IO Unit := withMutex h do
  checked (closeWith (← h.state.get) h.state.set (fun lock => lock.unlock))

end WalRecoverySlice.SingleFile
