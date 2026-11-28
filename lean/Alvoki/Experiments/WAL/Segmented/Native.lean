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

@[inline] def closeChildWith [Monad m] (take : m (Option (Nat × child)))
    (close : child → m Unit) : m Unit := do
  if let some (_, child) ← take then close child

private def Store.closeChild (s : Store) : IO Unit :=
  closeChildWith (s.active.swap none) SingleFile.close

/-- A reported cleanup error never replaces the operation's primary error. -/
@[inline] def cleanupOnError [Monad m] [MonadExceptOf error m]
    (action : m α) (cleanup : m Unit) : m α :=
  tryCatchThe error action fun err => do
    tryCatchThe error cleanup (fun _ => pure ())
    throw err

/-- Unlock even if child close reports an error. Preserve that first error. -/
@[inline] def releaseWith [Monad m] [MonadExceptOf error m] (closeChild unlock : m Unit) : m Unit := do
  cleanupOnError (error := error) closeChild unlock
  unlock

private def Store.release (s : Store) : IO Unit := do
  releaseWith (error := IO.Error) s.closeChild s.lock.unlock

/-- Only an unpublished successor can already occupy this ID after an
interrupted rotation. Creation and the returned child use the same path. -/
@[inline] def prepareChildWith [Monad m]
    (remove : Nat → m Unit) (mkdir : FilePath → m Unit)
    (create : FilePath → Policy → m child) (root : FilePath) (p : Policy) (id : Nat) : m child := do
  remove id
  let dir := segmentPath root id
  mkdir dir
  create dir p

private def Store.prepareChild (s : Store) (p : Policy) (id : Nat) : IO SingleFile.Handle :=
  prepareChildWith (removeSegment s.root) IO.FS.createDir SingleFile.create s.root p id

@[inline] def registerPreparedWith [Monad m] (prepare : m child)
    (register : Option (Nat × child) → m Unit) (id : Nat) : m Unit := do
  let child ← prepare
  register (some (id, child))

private def Store.prepare (s : Store) (p : Policy) (id : Nat) : IO Unit := do
  s.closeChild
  registerPreparedWith (s.prepareChild p id) s.active.set id

def requiredChildNames (p : Policy) : List String :=
  if p == .boundary then ["policy", "segment", "commit.0", "commit.1"] else ["policy", "segment"]

@[inline] def validateChildWith [Monad m] [MonadExceptOf String m]
    (inspect : FilePath → m (Array String)) (policySize : FilePath → m Nat)
    (readPolicy : FilePath → m String) (dir : FilePath) (p : Policy) (id : Nat) :
    m Unit := do
  let names ← inspect dir
  unless (requiredChildNames p).all names.contains do throw s!"incomplete segment {id}"
  let expected := policyStamp p
  unless (← policySize (dir / "policy")) == expected.utf8ByteSize &&
      (← readPolicy (dir / "policy")) == expected do
    throw s!"segment policy mismatch at {id}"

private def Store.checkedChildPath (s : Store) (p : Policy) (id : Nat) : IO FilePath := do
  let dir := segmentPath s.root id
  checked <| validateChildWith
    (fun path => do return (← inspectChild path).map (·.fileName))
    (fun path => do return (← path.metadata).byteSize.toNat)
    (fun path => IO.FS.readFile path) dir p id
  return dir

/-- A sealed child is closed locally. A failed scan stays primary. -/
@[inline] def readSealedChildWith [Monad m] [MonadExceptOf error m]
    (acquire : m child) (scan : child → m (List Bytes)) (close : child → m Unit) :
    m (List Bytes) := do
  let child ← acquire
  let batches ← cleanupOnError (error := error) (scan child) (close child)
  close child
  return batches

/-- Transfer the child to the caller on success. Release it on a reported
failure anywhere in the continuation, including scan or collection. -/
@[inline] def withActiveChild [Monad m] [MonadExceptOf error m]
    (acquire : m child) (close : child → m Unit) (resume : child → m result) : m result := do
  let child ← acquire
  cleanupOnError (error := error) (resume child) (close child)

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

/-- The writer returned by staging is the input to the writer barrier.
The directory description is acquired and held by the root store. -/
structure ControlPrimitives (m : Type → Type) (writer directory : Type) where
  clearStage : FilePath → m Unit
  openWriter : FilePath → IO.FS.Mode → m writer
  disableBuffering : writer → m Unit
  write : writer → ByteArray → m Unit
  flush : writer → m Unit
  syncWriter : writer → m Unit
  rename : FilePath → FilePath → m Unit
  syncDirectory : directory → m Unit

@[inline] def publishControlWith [Monad m] [MonadExceptOf String m]
    (ops : ControlPrimitives m writer directory) (root : FilePath)
    (held : directory) (c : Control) : m Unit :=
  let stage := root / "CONTROL.next"
  let active := root / "CONTROL"
  DurableBlob.publishWith (do
    unless c.active ≤ ControlCodec.wordMax && c.discarded ≤ ControlCodec.wordMax do
      throw "segmented WAL position exhausted"
    ops.clearStage stage
    let writer ← ops.openWriter stage .writeNew
    ops.disableBuffering writer
    ops.write writer (ControlCodec.encode c)
    ops.flush writer
    pure writer)
    ops.syncWriter (ops.rename stage active) (ops.syncDirectory held)

private def controlPrimitives : ControlPrimitives FileM IO.FS.Handle IO.FS.Handle where
  clearStage path := liftM (removeRegular path)
  openWriter path mode := liftM (IO.FS.Handle.mk path mode)
  disableBuffering writer := liftM (disableBuffering writer)
  write writer bytes := liftM (writer.write bytes)
  flush writer := liftM writer.flush
  syncWriter writer := liftM (syncHandle writer)
  rename stage active := liftM (IO.FS.rename stage active)
  syncDirectory directory := liftM (syncHandle directory)

private def Store.callbacks (s : Store) : RootOps FileM where
  prepareSegment p id := s.prepare p id
  syncRoot := syncRootWith (fun directory => liftM (syncHandle directory)) s.directory
  publishControl := publishControlWith controlPrimitives s.root s.directory
  readControl := readControlWith controlMetadata (fun file => IO.FS.readBinFile file) s.root
  listSegments := s.listIds
  removeSegment id := removeSegment s.root id

inductive Phase (store : Type) (session : Type := Session) where
  | ready (owned : store) (state : session)
  | poisoned (owned : store)
  | closed

structure Handle where private mk ::
  private state : IO.Ref (Phase Store CompactSession)
  private mutex : Std.BaseMutex

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
  cleanupOnError (error := error) construct release

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
    return {root, directory, lock, active}) dir

@[inline] def openWithStore [Monad m] [MonadExceptOf error m]
    (acquire : m store) (load : store → m phase) (newRef : phase → m cell)
    (newMutex : m mutex) (release : store → m Unit) : m (cell × mutex) := do
  let owned ← acquire
  installPhaseWith (error := error) (load owned) newRef newMutex (release owned)

@[inline] def installReopenedWith [Monad m] (recovery : m (Session × child))
    (storeActive : Option (Nat × child) → m store) : m (Phase store) := do
  let (session, child) ← recovery
  let owned ← storeActive (some (session.control.active, child))
  return .ready owned session

/-- Check the acquired root before touching its initial child or CONTROL. -/
@[inline] def createPhaseWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error) (entries : FilePath → m (Array IO.FS.DirEntry))
    (root : FilePath) (owned : store) (create : m session) : m (Phase store session) := do
  unless (← entries root).all (fun e => e.fileName == "lock") do
    throw (invalid "segmented WAL directory is not empty")
  return .ready owned (← create)

def retainedStep (c : Control) (id : Nat) (step : α → Nat → Bytes → α)
    (acc : α) (localPos : Nat) (batch : Bytes) : α :=
  let pos := id * c.capacity + localPos
  if c.discarded < pos then step acc pos batch else acc

private def Store.openChildFold (s : Store) (c : Control) (id : Nat)
    (seed : α) (step : Option (α → Nat → Bytes → α)) : IO (SingleFile.Handle × Cursor × α) := do
  let path ← s.checkedChildPath c.policy id
  match step with
  | some consume => SingleFile.openExistingFold path seed (retainedStep c id consume)
  | none =>
    let (handle, cursor) ← SingleFile.openExistingPosition path
    return (handle, cursor, seed)

/-- Visit the contiguous sealed IDs before borrowing the installed active child. -/
def foldSealedWith [Monad m] (read : Nat → α → m α) (first : Nat) :
    Nat → α → m α
  | 0, acc => pure acc
  | count + 1, acc => do
    let next ← read first acc
    foldSealedWith read (first + 1) count next

def scanReadyWith [Monad m] (session : CompactSession) (seed : α)
    (readSealed : Nat → α → m α) (readActive : α → m α) : m (Bounds × α) := do
  let c := session.control
  let acc ← foldSealedWith readSealed c.firstNeeded (c.active - c.firstNeeded) seed
  return (session.bounds, ← readActive acc)

def recoverSealedWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error) (capacity : Nat) (openChild : m (child × Cursor × α))
    (close : child → m Unit) : m α := do
  let (child, cursor, next) ← openChild
  close child
  unless cursor.nextSeq == capacity + 1 do throw (invalid "incomplete sealed segment")
  return next

/-- Shared recovery schedule. Child opening returns its reached cursor and
accumulator. Only the active child can escape its scope. -/
def recoverCompactWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error) (select : m Control)
    (openChild : Control → Nat → α → m (child × Cursor × α))
    (close : child → m Unit) (collect : Control → m Unit)
    (register : Nat → child → m Unit) (seed : α) : m (CompactSession × α) := do
  let c ← select
  let acc ← foldSealedWith
    (fun id acc => recoverSealedWith invalid c.capacity (openChild c id acc) close)
    c.firstNeeded (c.active - c.firstNeeded) seed
  withActiveChild (error := error) (openChild c c.active acc)
    (fun acquired => close acquired.1) fun (child, cursor, next) => do
      let session : CompactSession := ⟨c, cursor.nextSeq - 1⟩
      if session.activeCount > c.capacity then throw (invalid "oversized active segment")
      if c.discarded > session.bounds.tail then throw (invalid "release beyond recovered data")
      collect c
      register c.active child
      return (session, next)

private def Store.recoverFold (s : Store) (seed : α) (step : Option (α → Nat → Bytes → α)) :
    IO (CompactSession × α) :=
  recoverCompactWith IO.userError (checked (selectControl s.callbacks))
    (fun c id acc => s.openChildFold c id acc step) SingleFile.close
    (fun c => checked (collect s.callbacks c)) (fun id child => s.active.set (some (id, child))) seed

private def install (dir : FilePath) (fresh : Option (Policy × Nat))
    (seed : α) (step : Option (α → Nat → Bytes → α)) : IO (Handle × Bounds × α) := do
  let load (store : Store) : IO (Phase Store CompactSession × Bounds × α) := do
    match fresh with
    | some (policy, cap) =>
      let phase ← createPhaseWith IO.userError entries store.root store do
        let control ← checked (createControl store.callbacks policy cap)
        return (⟨control, 0⟩ : CompactSession)
      return (phase, ⟨0, 0⟩, seed)
    | none =>
      let (session, result) ← store.recoverFold seed step
      return (.ready store session, session.bounds, result)
  let ((state, bounds, result), mutex) ← openWithStore (error := IO.Error) (acquireStore dir) load
    (fun (phase, bounds, result) => do return (← IO.mkRef phase, bounds, result))
    (liftM Std.BaseMutex.new) Store.release
  return (⟨state, mutex⟩, bounds, result)

def create (dir : FilePath) (policy : Policy) (capacity : Nat) : IO Handle := do
  let (handle, _, _) ← install dir (some (policy, capacity)) () none
  return handle

/-- Only a settled, registered child is transferred with the fold result. -/
def openExistingFold (dir : FilePath) (seed : α) (step : α → Nat → Bytes → α) :
    IO (Handle × Bounds × α) :=
  install dir none seed (some step)

def openExisting (dir : FilePath) : IO Handle := do
  let (handle, _, _) ← install dir none () none
  return handle

private def Handle.locked (h : Handle) (action : IO α) : IO α := do
  h.mutex.lock
  try action finally h.mutex.unlock

/-- Poison the public phase before running any mutation. The successful
phase and reply are derived from the same returned session. -/
@[inline] def updateWith [Monad m] [MonadExceptOf error m]
    (invalid : String → error)
    (get : m (Phase store session)) (set : Phase store session → m Unit)
    (action : store → session → m session) : m session := do
  match ← get with
  | .ready store session =>
    set (.poisoned store)
    let next ← action store session
    set (.ready store next)
    return next
  | .poisoned _ => throw (invalid "segmented WAL requires reopen")
  | .closed => throw (invalid "segmented WAL closed")

private def update (h : Handle) (action : Store → CompactSession → FileM CompactSession) : IO CompactSession :=
  h.locked <| updateWith (m := IO) IO.userError (do h.state.get)
    (fun phase => do h.state.set phase) (fun store session => checked (action store session))

/-- Acquire and consume a successor in one scope. The old child is released
before preparation. The successor goes into the store only on success. -/
@[inline] def appendOwnedCore [Monad m] [MonadExceptOf error m]
    (current : Control) (activeCount : Nat) (finish : Control → Nat → session) (batch : Bytes) (check : m Unit) (invalid : String → error)
    (getActive : m (Option (Nat × child))) (closeOld : m Unit)
    (prepare : Policy → Nat → m child) (close : child → m Unit)
    (syncRoot : m Unit) (publish : Control → m Unit)
    (write : child → Bytes → m Unit) (install : Option (Nat × child) → m Unit) : m session := do
  check
  if activeCount = current.capacity then
    let next := {current with active := current.active + 1}
    closeOld
    withActiveChild (error := error) (prepare next.policy next.active) close fun child => do
      syncRoot
      publish next
      write child batch
      install (some (next.active, child))
      pure (finish next 1)
  else
    let some (id, child) ← getActive | throw (invalid "no active segment")
    unless id == current.active do throw (invalid "incorrect active segment")
    write child batch
    pure (finish current (activeCount + 1))

@[inline] def appendOwnedWith [Monad m] [MonadExceptOf error m]
    (session : Session) (batch : Bytes) (check : m Unit) (invalid : String → error)
    (getActive : m (Option (Nat × child))) (closeOld : m Unit)
    (prepare : Policy → Nat → m child) (close : child → m Unit)
    (syncRoot : m Unit) (publish : Control → m Unit)
    (write : child → Bytes → m Unit) (install : Option (Nat × child) → m Unit) : m Session :=
  appendOwnedCore session.control session.activeCount
    (fun control count => ⟨control, count, session.view.append batch⟩) batch check invalid getActive
    closeOld prepare close syncRoot publish write install

/-- Return the absolute position from the session committed by the same update. -/
@[inline] def appendPositionWith [Monad m] (update : m Session) : m Nat := do
  let next ← update
  return next.tailPosition

/-- Return the absolute, one-based position only after the append schedule succeeds. -/
def append (h : Handle) (batch : Bytes) : IO Nat := do
  let next ← update h fun store session => do
    let check : IO Unit := do
      if batch.length > 32 then throw (IO.userError "batch out of bounds")
      if session.bounds.tail ≥ Contract.maxPosition then
        throw (IO.userError "segmented WAL position exhausted")
    liftM <| appendOwnedCore session.control session.activeCount CompactSession.mk batch check
      IO.userError store.active.get store.closeChild store.prepareChild SingleFile.close
      (checked store.callbacks.syncRoot) (fun control => checked (store.callbacks.publishControl control))
      SingleFile.append store.active.set
  return next.bounds.tail

def discardThrough (h : Handle) (k : Nat) : IO Unit := do
  let _ ← update h fun store session => do
    if k > session.bounds.tail then throw "discard past end"
    if k ≤ session.control.discarded then return session
    let control ← discardControl store.callbacks session.control k
    return {session with control}
  pure ()

def scanWith [Monad m] [MonadExceptOf String m] (phase : Phase store) : m Contract.View :=
  match phase with
  | .ready _ session => pure session.view
  | .poisoned _ => throw "segmented WAL requires reopen"
  | .closed => throw "segmented WAL closed"

@[inline] def closeWith [Monad m] (swap : Phase store session → m (Phase store session))
    (release : store → m Unit) : m Unit := do
  match ← swap .closed with
  | .ready owned _ | .poisoned owned => release owned
  | .closed => pure ()

private def withReady (h : Handle) (run : Store → CompactSession → IO α) : IO α := h.locked do
  match ← h.state.get with
  | .ready store session => run store session
  | .poisoned _ => throw (IO.userError "segmented WAL requires reopen")
  | .closed => throw (IO.userError "segmented WAL closed")

def bounds (h : Handle) : IO Bounds := withReady h fun _ session => pure session.bounds

/-- Read a single owned snapshot. The pure step remains private and errors
leave the installed phase, bindings, and disk untouched. -/
def scanFold (h : Handle) (seed : α) (step : α → Nat → Bytes → α) : IO (Bounds × α) :=
  withReady h fun store session => do
    let c := session.control
    let readSealed id acc := do
      let path ← store.checkedChildPath c.policy id
      SingleFile.scanSealedFold path c.policy c.capacity acc (retainedStep c id step)
    let readActive acc := do
      let some (id, child) ← store.active.get | throw (IO.userError "no active segment")
      unless id == c.active do throw (IO.userError "incorrect active segment")
      SingleFile.scanFold child acc (retainedStep c id step)
    scanReadyWith session seed readSealed readActive

def scan (h : Handle) : IO Contract.View := do
  let (bounds, batches) ← scanFold h [] (fun acc _ batch => batch :: acc)
  return ⟨bounds.base, batches.reverse⟩

def close (h : Handle) : IO Unit := h.locked do
  closeWith h.state.swap Store.release

end WalRecoverySlice.Segmented.Native
