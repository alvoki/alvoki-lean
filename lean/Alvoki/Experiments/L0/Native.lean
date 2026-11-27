import Alvoki.Experiments.L0.TableSchedule
import Alvoki.Experiments.L0.TableAllocation
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

private def buildSynced (dir : FilePath) (id : UInt64) (rows : Rows) : IO Unit := do
  let remaining ← IO.mkRef rows
  let _ ← ImmutableSSTable.buildFileSynced (tablePath dir id) do
    match ← remaining.get with
    | [] => return none
    | row :: tail =>
      remaining.set tail
      return some (ImmutableSSTable.Entry.encode keyCodec mutationCodec row)

private def createTable (dir : FilePath) (rows : Rows) : FileM UInt64 :=
  createTableAt (fun id => liftM (pathExists (tablePath dir id)))
    (fun id entries => liftM (buildSynced dir id entries))
    (liftM (IO.FS.withFile dir .read syncHandle)) rows

private def checked (operation : FileM α) : IO α := do
  match ← operation.run with
  | .ok result => return result
  | .error error => throw (IO.userError error)

/-- The stat and open refer to the same stable path under root ownership.
`IO.FS.withFile` drops its handle at the end of the call. Neither table
operation retains it, so the runtime can close it on success or error. -/
private def withTable (dir : FilePath) (id : UInt64)
    (use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α) : FileM α :=
  let path := tablePath dir id
  withTableDescriptor (liftM path.symlinkMetadata)
    (fun action => ExceptT.mk (IO.FS.withFile path .read fun handle => (action handle).run))
    (fun handle => nativeTableAction handle use)

private def tables (dir : FilePath) : Tables FileM where
  create := createTable dir
  check id := withTable dir id (fun _ => pure ())
  lookup id key := withTable dir id (·.lookup key)

private def requireWal (phase : IO.Ref (Phase Wal)) : IO Wal := do
  let some handle := (← phase.get).wal | throw (IO.userError "WAL is offline")
  return handle

private def phaseCell (phase : IO.Ref (Phase Wal)) : Cell IO Wal where
  read := phase.get
  swap := phase.swap

private def callbackComponents (root : FilePath) (phase : IO.Ref (Phase Wal)) : Components FileM :=
  let blob := DurableBlob.native (root / "manifest")
  {
    append batch := liftM do
      let _ ← WalRecoverySlice.Segmented.Native.append (← requireWal phase) batch
    scan := liftM do WalRecoverySlice.Segmented.Native.scan (← requireWal phase)
    reopenWal := liftM <| (phaseCell phase).reopenWal (IO.userError "L0 cannot open a WAL")
      (WalRecoverySlice.Segmented.Native.openExisting (root / "wal"))
      WalRecoverySlice.Segmented.Native.scan
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
    (phaseCell phase).withSession (IO.userError "L0 cannot publish a session")
      (checked (recover ops)) (use ⟨ops, phase⟩)
      WalRecoverySlice.Segmented.Native.close lock.unlock

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
  (phaseCell handle.phase).useSession (IO.userError "L0 requires reopen")
    (fun session => checked (ExperimentalL0.get handle.ops session key))

end ExperimentalL0.Native
