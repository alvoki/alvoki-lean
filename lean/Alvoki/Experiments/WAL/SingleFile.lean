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
  readData := do
    reader.rewind
    return (← reader.readBinToEnd).data.toList
  readMarker slot := do
    let some (a, b) := markers | throw "marker unavailable"
    let h := if slot == 0 then a else b
    h.rewind
    return (← h.readBinToEnd).data.toList
  truncate n := do
    reader.rewind
    let prefixBytes ← reader.read n.toUSize
    unless prefixBytes.size == n do throw "short prefix read"
    reader.truncate

private def checked (action : FileM α) : IO α := do
  match ← action.run with
  | .ok value => return value
  | .error error => throw <| IO.userError error

private inductive Phase where
  | active (lock : IO.FS.Handle) (ops : Ops FileM) (cursor : Cursor) (entries : List Bytes)
  | poisoned (lock : IO.FS.Handle)
  | closed

/-- An alias of a handle shares its phase and mutex; closing any alias closes all. -/
structure Handle where private mk ::
  private policy : Policy
  private state : IO.Ref Phase
  private mutex : Std.BaseMutex

private def withMutex (h : Handle) (action : IO α) : IO α := do
  h.mutex.lock
  try action finally h.mutex.unlock

private def acquire (dir : FilePath) : IO IO.FS.Handle := do
  let lock ← IO.FS.Handle.mk (dir / "lock") .append
  unless ← lock.tryLock do throw <| IO.userError "WAL already open"
  return lock

private def install (dir : FilePath) (lock : IO.FS.Handle) : IO Handle := do
  let policy ← match ← IO.FS.readFile (dir / "policy") with
    | "v3 log" => pure Policy.logOnly
    | "v3 boundary" => pure Policy.boundary
    | _ => throw <| IO.userError "unrecognized WAL policy"
  let reader ← openStream (dir / "segment") .readWrite
  let writer ← openStream (dir / "segment") .append
  let markers ← if policy == .boundary then do
    let a ← openStream (dir / "commit.0") .readWrite
    let b ← openStream (dir / "commit.1") .readWrite
    pure (some (a, b))
    else pure none
  let ops := fileOps writer reader markers
  let recovered ← checked (reopen ops policy)
  -- A creator may have exited before making the visible names durable.
  IO.FS.withFile (dir / "policy") .read syncHandle
  IO.FS.withFile dir .read syncHandle
  return ⟨policy, ← IO.mkRef (.active lock ops recovered.cursor recovered.batches), ← Std.BaseMutex.new⟩

/-- Open a previously initialized directory, holding a nonblocking exclusive file
lock through recovery and until close. Failure releases the lock. -/
def openExisting (dir : FilePath) : IO Handle := do
  let lock ← acquire dir
  try install dir lock catch e =>
    lock.unlock
    throw e

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

/-- Return the confirmed history from the last successful recovery and appends. -/
def scan (h : Handle) : IO (List Bytes) := withMutex h do
  match ← h.state.get with
  | .active _ _ _ entries => return entries
  | .closed => throw <| IO.userError "WAL closed"
  | .poisoned _ => throw <| IO.userError "WAL poisoned; reopen required"

def close (h : Handle) : IO Unit := withMutex h do
  match ← h.state.get with
  | .closed => throw <| IO.userError "WAL closed"
  | .active lock _ _ _ | .poisoned lock =>
    h.state.set .closed
    lock.unlock

end WalRecoverySlice.SingleFile
