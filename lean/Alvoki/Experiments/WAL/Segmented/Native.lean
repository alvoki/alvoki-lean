import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Segmented.ControlCodec

/-! Native adapter for the segmented WAL experiment. The caller owns a durable
parent directory on one filesystem. Its canonical path stays in place while the
root lock is held. All participating writers respect that lock. -/
namespace WalRecoverySlice.Segmented.Native
open System

@[extern "alvoki_fsync"]
private opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_wal_unbuffered"]
private opaque disableBuffering (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_read_dir_checked"]
private opaque entries (path : @& FilePath) : IO (Array IO.FS.DirEntry)

private def metadata? (path : FilePath) : IO (Option IO.FS.Metadata) := do
  try return some (← path.symlinkMetadata) catch
    | .noFileOrDirectory .. => return none
    | err => throw err

private def regular (path : FilePath) (md : IO.FS.Metadata) : IO Unit := do
  unless md.type == .file && md.numLinks == 1 do
    throw <| IO.userError s!"expected singly linked regular file at {path}"

private def removeRegular (path : FilePath) : IO Unit := do
  if let some md ← metadata? path then
    regular path md
    IO.FS.removeFile path

def segmentName (id : Nat) : String := "segment-" ++ id.repr

def segmentPath (root : FilePath) (id : Nat) := root / segmentName id

def policyStamp (p : Policy) := if p == .boundary then "v3 boundary" else "v3 log"

private def childName (name : String) : Bool :=
  ["lock", "policy", "segment", "commit.0", "commit.1"].contains name

private def inspectChild (dir : FilePath) : IO (Array IO.FS.DirEntry) := do
  unless (← dir.symlinkMetadata).type == .dir do throw <| IO.userError s!"expected segment directory at {dir}"
  let names ← entries dir
  for item in names do
    let path := dir / item.fileName
    unless childName item.fileName do throw <| IO.userError s!"unexpected child {path}"
    regular path (← path.symlinkMetadata)
  return names

/-- Reclaim only recognized names after the shared protocol has established
the ID is retired or was never published. A partial deletion is retryable. -/
@[inline] def removeSegmentWith [Monad m] (present : FilePath → m Bool)
    (inspect : FilePath → m (Array entry)) (name : entry → String)
    (unlink rmdir : FilePath → m Unit) (root : FilePath) (id : Nat) : m Unit := do
  let dir := segmentPath root id
  if ← present dir then
    let members ← inspect dir
    members.forM fun item => unlink (dir / name item)
    rmdir dir

private def removeSegment (root : FilePath) (id : Nat) : IO Unit :=
  removeSegmentWith (fun dir => return (← metadata? dir).isSome)
    inspectChild (·.fileName) IO.FS.removeFile IO.FS.removeDir root id

private abbrev FileM := ExceptT String IO

@[inline] def acquireRootWith [Monad m] [MonadExceptOf String m]
    (metadata : FilePath → m (Option Bool)) (openFile : FilePath → IO.FS.Mode → m handle)
    (tryLock : handle → m Bool) (root : FilePath) : m handle := do
  let path := root / "lock"
  if (← metadata path) == some false then
    throw s!"expected singly linked regular file at {path}"
  let lock ← openFile path .append
  let granted ← tryLock lock
  if granted then pure lock else throw "segmented WAL already open"

private def checked (a : FileM α) : IO α := do
  match ← a.run with
  | .ok x => return x
  | .error e => throw <| IO.userError e

private def acquireRoot (root : FilePath) : IO IO.FS.Handle :=
  checked <| acquireRootWith
    (fun path => do
      let md ← metadata? path
      return md.map fun item => item.type == .file && item.numLinks == 1)
    (fun path mode => IO.FS.Handle.mk path mode) (fun handle => handle.tryLock) root

private structure Store where
  root : FilePath
  lock : IO.FS.Handle
  directory : IO.FS.Handle
  active : IO.Ref (Option (Nat × SingleFile.Handle))
  controlWriter : IO.Ref (Option IO.FS.Handle)

@[inline] def closeChildWith [Monad m] (take : m (Option (Nat × child)))
    (close : child → m Unit) : m Unit := do
  if let some (_, child) ← take then close child

private def Store.closeChild (s : Store) : IO Unit :=
  closeChildWith (s.active.swap none) SingleFile.close

/-- Dispose of the child before releasing the root lock. An I/O error
closing the child still runs the root unlock. -/
@[inline] def releaseWith [MonadFinally m] [Functor m] (closeChild unlock : m Unit) : m Unit :=
  tryFinally closeChild unlock

private def Store.release (s : Store) : IO Unit := do
  s.controlWriter.set none
  releaseWith s.closeChild s.lock.unlock

private def Store.prepare (s : Store) (p : Policy) (id : Nat) : IO Unit := do
  s.closeChild
  -- Only an unpublished successor can already occupy this ID after an interrupted rotation.
  removeSegment s.root id
  let dir := segmentPath s.root id
  IO.FS.createDir dir
  let child ← SingleFile.create dir p
  s.active.set (some (id, child))

@[inline] def validateChildWith [Monad m] [MonadExceptOf String m]
    (inspect : FilePath → m (Array String)) (policySize : FilePath → m Nat)
    (readPolicy : FilePath → m String) (dir : FilePath) (p : Policy) (id : Nat) :
    m Unit := do
  let names ← inspect dir
  let required := if p == .boundary then ["policy", "segment", "commit.0", "commit.1"] else ["policy", "segment"]
  unless required.all names.contains do throw s!"incomplete segment {id}"
  let expected := policyStamp p
  unless (← policySize (dir / "policy")) == expected.utf8ByteSize &&
      (← readPolicy (dir / "policy")) == expected do
    throw s!"segment policy mismatch at {id}"

/-- A selected child is opened at its computed path, installed in the
active cell, and scanned through the same returned handle. -/
@[inline] def openChildWith [Monad m] [MonadExceptOf String m]
    (closePrevious : m Unit) (inspect : FilePath → m (Array String))
    (policySize : FilePath → m Nat) (readPolicy : FilePath → m String)
    (openChild : FilePath → m child) (install : Nat → child → m Unit)
    (scanChild : child → m (List Bytes)) (root : FilePath) (p : Policy) (id : Nat) :
    m (List Bytes) := do
  closePrevious
  let dir := segmentPath root id
  validateChildWith inspect policySize readPolicy dir p id
  let child ← openChild dir
  install id child
  scanChild child

private def Store.openChild (s : Store) (p : Policy) (id : Nat) : IO (List Bytes) :=
  checked <| openChildWith
    (liftM s.closeChild)
    (fun path => do return (← inspectChild path).map (·.fileName))
    (fun path => do return (← path.metadata).byteSize.toNat)
    (fun path => IO.FS.readFile path)
    (fun path => SingleFile.openExisting path)
    (fun index child => s.active.set (some (index, child)))
    (fun child => SingleFile.scan child) s.root p id

def segmentId (name : String) : Except String (Option Nat) :=
  if ["lock", "CONTROL", "CONTROL.next"].contains name then .ok none
  else match (name.drop "segment-".length).toString.toNat? with
    | none => .error s!"unexpected segmented WAL entry {name}"
    | some id => if name == segmentName id then .ok (some id)
      else .error s!"invalid segment name {name}"

def collectId (ids : List Nat) (name : String) : Except String (List Nat) :=
  (segmentId name).map fun id => id.elim ids (· :: ids)

@[inline] def listedIds (name : entry → String) (items : Array entry) : Except String (List Nat) :=
  items.foldlM (fun ids item => collectId ids (name item)) []

private def Store.listIds (s : Store) : FileM (List Nat) := do
  match listedIds (·.fileName) (← entries s.root) with
  | .ok ids => return ids
  | .error err => throw err

/-- The CONTROL read uses the reached no-follow metadata and whole-file
read of the same protected path. Its decode and checks are shared. -/
@[inline] def readControlWith [Monad m] [MonadExceptOf String m]
    (metadata : FilePath → m (Bool × Nat)) (readBytes : FilePath → m ByteArray)
    (root : FilePath) : m Control := do
  let file := root / "CONTROL"
  let (regularFile, size) ← metadata file
  unless regularFile do throw s!"expected singly linked regular file at {file}"
  -- The version, policy, capacity, two UInt64 decimal fields and digest fit in 80 bytes.
  if size > 80 then throw "oversized segmented WAL control"
  let some control := ControlCodec.decode (← readBytes file)
    | throw "invalid segmented WAL control"
  return control

private def controlMetadata (path : FilePath) : FileM (Bool × Nat) := do
  let md ← path.symlinkMetadata
  return (md.type == .file && md.numLinks == 1, md.byteSize.toNat)

@[inline] def syncRootWith {m : Type → Type} (sync : descriptor → m Unit) (directory : descriptor) : m Unit :=
  sync directory

private def Store.callbacks (s : Store) : Ops FileM where
  prepareSegment p id := s.prepare p id
  syncRoot := syncRootWith (fun directory => liftM (syncHandle directory)) s.directory
  stageControl c := do
    unless c.active ≤ ControlCodec.wordMax && c.discarded ≤ ControlCodec.wordMax do throw "segmented WAL position exhausted"
    let stage := s.root / "CONTROL.next"
    removeRegular stage
    let h ← IO.FS.Handle.mk stage .writeNew
    disableBuffering h
    h.write (ControlCodec.encode c)
    h.flush
    s.controlWriter.set (some h)
  syncControl := do
    -- Consume the original writer on either outcome. An independently
    -- opened descriptor can miss a writeback error reported to this writer.
    let some h ← s.controlWriter.swap none | throw "no staged control writer"
    syncHandle h
  renameControl := IO.FS.rename (s.root / "CONTROL.next") (s.root / "CONTROL")
  readControl := readControlWith controlMetadata (fun file => IO.FS.readBinFile file) s.root
  openSegment p id := s.openChild p id
  appendSegment _ id batch := do
    let some (installed, child) ← s.active.get | throw "no active segment"
    unless installed == id do throw "incorrect active segment"
    SingleFile.append child batch
  listSegments := s.listIds
  removeSegment id := removeSegment s.root id

inductive Phase (store : Type) where
  | ready (owned : store) (session : Session)
  | poisoned (owned : store)
  | closed

structure Handle where private mk ::
  private state : IO.Ref (Phase Store)
  private mutex : Std.BaseMutex

@[inline] def reopenPhaseWith [Monad m] [MonadExceptOf String m]
    (callbacks : Ops m) (owned : store) : m (Phase store) :=
  return .ready owned (← Segmented.reopen callbacks)

@[inline] def openRootDirectoryWith [Monad m] (resolve : FilePath → m FilePath)
    (openFile : FilePath → IO.FS.Mode → m descriptor) (dir : FilePath) :
    m (FilePath × descriptor) := do
  let root ← resolve dir
  return (root, ← openFile root .read)

@[inline] def installPhaseWith [Monad m] [MonadExceptOf error m]
    (load : m phase) (newRef : phase → m cell) (newMutex : m mutex)
    (release : m Unit) : m (cell × mutex) := do
  let construct := do
    let phase ← load
    let state ← newRef phase
    return (state, ← newMutex)
  tryCatchThe error construct fun err => do
    release
    throw err

/-- Both descriptors and the store use the single resolved root path. -/
@[inline] def acquireStoreWith [Monad m]
    (resolve : FilePath → m FilePath) (openDirectory : FilePath → IO.FS.Mode → m directory)
    (lockRoot : FilePath → m lock) (allocate : FilePath → directory → lock → m store)
    (dir : FilePath) : m store := do
  let (root, directory) ← openRootDirectoryWith resolve openDirectory dir
  let lock ← lockRoot root
  allocate root directory lock

private def acquireStore (dir : FilePath) : IO Store :=
  acquireStoreWith IO.FS.realPath IO.FS.Handle.mk acquireRoot (fun root directory lock => do
    let active ← IO.mkRef none
    let controlWriter ← IO.mkRef none
    return {root, directory, lock, active, controlWriter}) dir

@[inline] def openWithStore [Monad m] [MonadExceptOf error m]
    (acquire : m store) (load : store → m phase) (newRef : phase → m cell)
    (newMutex : m mutex) (release : store → m Unit) : m (cell × mutex) := do
  let owned ← acquire
  installPhaseWith (error := error) (load owned) newRef newMutex (release owned)

private def install (dir : FilePath) (fresh : Option (Policy × Nat)) : IO Handle := do
  let load (store : Store) := match fresh with
    | some (policy, cap) => do
      unless (← entries store.root).all (fun e => e.fileName == "lock") do
        throw <| IO.userError "segmented WAL directory is not empty"
      pure (.ready store (← checked (Segmented.create store.callbacks policy cap)))
    | none => checked (reopenPhaseWith store.callbacks store)
  let (state, mutex) ← openWithStore (error := IO.Error) (acquireStore dir) load
    (fun phase => IO.mkRef phase) (liftM Std.BaseMutex.new) Store.release
  return ⟨state, mutex⟩

def create (dir : FilePath) (policy : Policy) (capacity : Nat) : IO Handle :=
  install dir (some (policy, capacity))

def openExisting (dir : FilePath) : IO Handle := install dir none

private def Handle.locked (h : Handle) (action : IO α) : IO α := do
  h.mutex.lock
  try action finally h.mutex.unlock

private def update (h : Handle) (action : Ops FileM → Session → FileM Session) : IO Session := h.locked do
  match ← h.state.get with
  | .ready store session =>
    h.state.set (.poisoned store)
    let next ← try checked (action store.callbacks session) finally store.controlWriter.set none
    h.state.set (.ready store next)
    return next
  | .poisoned _ => throw <| IO.userError "segmented WAL requires reopen"
  | .closed => throw <| IO.userError "segmented WAL closed"

/-- Return the absolute, one-based position only after the append schedule succeeds. -/
def append (h : Handle) (batch : Bytes) : IO Nat := do
  let next ← update h (fun ops s => Segmented.append ops s batch)
  return next.tailPosition

def discardThrough (h : Handle) (k : Nat) : IO Unit := do
  let _ ← update h (fun ops s => Segmented.discardThrough ops s k)
  pure ()

def scanWith [Monad m] [MonadExceptOf String m] (phase : Phase store) : m Contract.View :=
  match phase with
  | .ready _ session => pure session.view
  | .poisoned _ => throw "segmented WAL requires reopen"
  | .closed => throw "segmented WAL closed"

@[inline] def closeWith [Monad m] (swap : Phase store → m (Phase store))
    (release : store → m Unit) : m Unit := do
  match ← swap .closed with
  | .ready owned _ | .poisoned owned => release owned
  | .closed => pure ()

def scan (h : Handle) : IO Contract.View := h.locked do
  checked (scanWith (← h.state.get))

def close (h : Handle) : IO Unit := h.locked do
  closeWith h.state.swap Store.release

end WalRecoverySlice.Segmented.Native
