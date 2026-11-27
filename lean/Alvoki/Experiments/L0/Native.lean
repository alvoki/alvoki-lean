import Alvoki.Experiments.L0.Codecs
import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.DurableBlob.Native
import Alvoki.Experiments.SSTable.Native
import Alvoki.Experiments.WAL.Segmented.Native

namespace ExperimentalL0.Native
open System Lifecycle
private abbrev Wal := WalRecoverySlice.Segmented.Native.Handle
private abbrev FileM := ExceptT String IO

@[extern "alvoki_fsync"]
private opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

private def tablePath (dir : FilePath) (id : UInt64) : FilePath := dir / s!"table-{id.toNat}"

private def pathExists (path : FilePath) : IO Bool := do
  try
    let _ ← path.symlinkMetadata
    return true
  catch
    | .noFileOrDirectory .. => return false
    | err => throw err

private def findFree (dir : FilePath) (next : Nat) : IO UInt64 :=
  if full : next ≥ UInt64.size then throw (IO.userError "table IDs exhausted")
  else do
    let id := next.toUInt64
    if ← pathExists (tablePath dir id) then findFree dir (next + 1) else return id
termination_by UInt64.size - next
decreasing_by omega

private def createTable (dir : FilePath) (rows : Rows) : IO UInt64 := do
  let id ← findFree dir 0
  let remaining ← IO.mkRef rows
  let _ ← ImmutableSSTable.buildFileSynced (tablePath dir id) do
    match ← remaining.get with
    | [] => return none
    | row :: tail =>
      remaining.set tail
      return some (ImmutableSSTable.Entry.encode keyCodec mutationCodec row)
  IO.FS.withFile dir .read syncHandle
  return id

private def checked (operation : FileM α) : IO α := do
  match ← operation.run with
  | .ok result => return result
  | .error error => throw (IO.userError error)

/-- The callback returns a value or error without exporting the descriptor. -/
private def withTable (dir : FilePath) (id : UInt64)
    (use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α) : FileM α := do
  let path := tablePath dir id
  let metadata ← liftM path.symlinkMetadata
  unless metadata.type == .file && metadata.numLinks == 1 do
    throw "expected a singly linked regular SSTable"
  let result ← liftM <| IO.FS.withFile path .read fun handle => do
    (do
      let table ← ImmutableSSTable.openTable (ImmutableSSTable.handleSource handle)
      use ⟨table, keyCodec, mutationCodec⟩).toBaseIO
  match result with
  | .ok result => return result
  | .error error => throw error

private def tables (dir : FilePath) : Tables FileM where
  create rows := liftM (createTable dir rows)
  check id := withTable dir id (fun _ => pure ())
  lookup id key := withTable dir id (·.lookup key)

private def requireWal (phase : IO.Ref (Phase Wal)) : IO Wal := do
  let some handle := (← phase.get).wal | throw (IO.userError "WAL is offline")
  return handle

private def closeWal (phase : IO.Ref (Phase Wal)) : IO Unit := do
  let previous ← phase.swap .offline
  if let some handle := previous.wal then WalRecoverySlice.Segmented.Native.close handle

private def publishSession (phase : IO.Ref (Phase Wal)) (session : Session) : IO Unit := do
  let some next := (← phase.get).publish session | throw (IO.userError "L0 cannot publish a session")
  phase.set next

/-- The callbacks used by the Linux wrapper. Callers should use `withOpen`;
this entry point exposes the callback boundary for the proof. -/
def callbackComponents (root : FilePath) (phase : IO.Ref (Phase Wal)) : Components FileM :=
  let blob := DurableBlob.native (root / "manifest")
  {
    append batch := liftM do
      let _ ← WalRecoverySlice.Segmented.Native.append (← requireWal phase) batch
    scan := liftM do WalRecoverySlice.Segmented.Native.scan (← requireWal phase)
    reopenWal := liftM do
      let some attach := (← phase.get).attachWal | throw (IO.userError "L0 cannot open a WAL")
      let handle ← WalRecoverySlice.Segmented.Native.openExisting (root / "wal")
      phase.set (attach handle)
      WalRecoverySlice.Segmented.Native.scan handle
    manifest := L0Manifest.backend id {
      publish := fun bytes => liftM (blob.publish bytes)
      reopen := liftM blob.reopen
    }
    tables := tables (root / "tables")
  }

structure Handle where private mk ::
  private ops : Components FileM
  private phase : IO.Ref (Phase Wal)

/-- Exclusive root ownership is held for the entire callback. The caller
supplies an initialized root containing distinct, durably named wal,
manifest, and tables directories. All operations must be sequential.
An escaped handle is offline after the callback ends. -/
def withOpen (path : FilePath) (use : Handle → IO α) : IO α := do
  let root ← IO.FS.realPath path
  for name in ["wal", "manifest", "tables"] do
    unless (← (root / name).symlinkMetadata).type == .dir do
      throw (IO.userError s!"expected directory {name}")
  let lockPath := root / "l0.lock"
  if ← pathExists lockPath then
    let md ← lockPath.symlinkMetadata
    unless md.type == .file && md.numLinks == 1 do
      throw (IO.userError "expected a singly linked regular L0 lock file")
  IO.FS.withFile lockPath .append fun lock => do
    unless ← lock.tryLock do throw (IO.userError "L0 already open")
    let phase ← IO.mkRef (.opening : Phase Wal)
    let ops := callbackComponents root phase
    let result ← (do
      let recovered ← checked (recover ops)
      publishSession phase recovered
      use ⟨ops, phase⟩).toBaseIO
    let closed ← (try closeWal phase finally lock.unlock).toBaseIO
    match result, closed with
    | .error error, _ | .ok _, .error error => throw error
    | .ok result, .ok () => return result

private def online (handle : Handle) : IO Session := do
  let some session := (← handle.phase.get).session | throw (IO.userError "L0 requires reopen")
  return session

private def update (handle : Handle) (operation : Session → FileM Session) : IO Unit := do
  let some (next, session) := (← handle.phase.get).beginUpdate
    | throw (IO.userError "L0 requires reopen")
  handle.phase.set next
  try
    publishSession handle.phase (← checked (operation session))
  catch error =>
    try closeWal handle.phase catch _ => pure ()
    throw error

def put (handle : Handle) (key value : UInt64) : IO Unit :=
  update handle (fun session => write handle.ops session (key, .put value))

def delete (handle : Handle) (key : UInt64) : IO Unit :=
  update handle (fun session => write handle.ops session (key, .delete))

def flush (handle : Handle) : IO Unit :=
  update handle (ExperimentalL0.flush handle.ops)

def get (handle : Handle) (key : UInt64) : IO (Option UInt64) := do
  checked (ExperimentalL0.get handle.ops (← online handle) key)

end ExperimentalL0.Native
