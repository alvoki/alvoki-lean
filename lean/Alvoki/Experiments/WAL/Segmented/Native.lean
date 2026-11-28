import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Segmented.ControlCodec

/-! Native adapter for the segmented WAL experiment. The caller owns a durable
parent directory on one filesystem. Its canonical path stays in place while the
root lock is held. All participating writers respect that lock. -/
namespace WalRecoverySlice.Segmented.Native
open System

@[extern "alvoki_fsync"]
opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_wal_unbuffered"]
private opaque disableBuffering (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_read_dir_checked"]
opaque entries (path : @& FilePath) : IO (Array IO.FS.DirEntry)

def metadata? (path : FilePath) : IO (Option IO.FS.Metadata) :=
  tryCatchThe IO.Error (some <$> path.symlinkMetadata) fun
    | .noFileOrDirectory .. => pure none
    | err => throw err

def regular (path : FilePath) (md : IO.FS.Metadata) : IO Unit := do
  unless md.type == .file && md.numLinks == 1 do
    throw <| IO.userError s!"expected singly linked regular file at {path}"

private def removeRegular (path : FilePath) : IO Unit := do
  if let some md ← metadata? path then
    regular path md
    IO.FS.removeFile path

def segmentName (id : Nat) : String := "segment-" ++ id.repr

def segmentPath (root : FilePath) (id : Nat) := root / segmentName id

def policyStamp (p : Policy) := if p == .boundary then "v3 boundary" else "v3 log"

def childName (name : String) : Bool :=
  ["lock", "policy", "segment", "commit.0", "commit.1"].contains name

def inspectChild (dir : FilePath) : IO (Array IO.FS.DirEntry) := do
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

def removeSegment (root : FilePath) (id : Nat) : IO Unit :=
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

def checked (a : FileM α) : IO α := do
  match ← a.run with
  | .ok x => return x
  | .error e => throw <| IO.userError e

def acquireRoot (root : FilePath) : IO IO.FS.Handle :=
  checked <| acquireRootWith
    (fun path => do
      let md ← metadata? path
      return md.map fun item => item.type == .file && item.numLinks == 1)
    (fun path mode => IO.FS.Handle.mk path mode) (fun handle => handle.tryLock) root

structure Store where private mk ::
  root : FilePath
  lock : IO.FS.Handle
  directory : IO.FS.Handle
  active : IO.Ref (Option (Nat × SingleFile.Handle))

@[inline] def closeChildWith [Monad m] (take : m (Option (Nat × child)))
    (close : child → m Unit) : m Unit := do
  if let some (_, child) ← take then close child

def Store.closeChild (s : Store) : IO Unit :=
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

def Store.release (s : Store) : IO Unit := do
  releaseWith (error := IO.Error) s.closeChild s.lock.unlock

private def Store.prepare (s : Store) (p : Policy) (id : Nat) : IO Unit := do
  s.closeChild
  -- Only an unpublished successor can already occupy this ID after an interrupted rotation.
  removeSegment s.root id
  let dir := segmentPath s.root id
  IO.FS.createDir dir
  let child ← SingleFile.create dir p
  s.active.set (some (id, child))

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

def Store.acquireChild (s : Store) (p : Policy) (id : Nat) : IO SingleFile.Handle := do
  let dir := segmentPath s.root id
  checked <| validateChildWith
    (fun path => do return (← inspectChild path).map (·.fileName))
    (fun path => do return (← path.metadata).byteSize.toNat)
    (fun path => IO.FS.readFile path) dir p id
  SingleFile.openExisting dir

/-- A sealed child is closed locally. A failed scan stays primary. -/
@[inline] def readSealedChildWith [Monad m] [MonadExceptOf error m]
    (acquire : m child) (scan : child → m (List Bytes)) (close : child → m Unit) :
    m (List Bytes) := do
  let child ← acquire
  let batches ← cleanupOnError (error := error) (scan child) (close child)
  close child
  return batches

def Store.readSealedChild (s : Store) (p : Policy) (id : Nat) : IO (List Bytes) :=
  readSealedChildWith (error := IO.Error) (s.acquireChild p id) SingleFile.scan SingleFile.close

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

def Store.listIds (s : Store) : FileM (List Nat) := do
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

def controlMetadata (path : FilePath) : FileM (Bool × Nat) := do
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

def Store.callbacks (s : Store) : Ops FileM where
  prepareSegment p id := s.prepare p id
  syncRoot := syncRootWith (fun directory => liftM (syncHandle directory)) s.directory
  publishControl := publishControlWith controlPrimitives s.root s.directory
  readControl := readControlWith controlMetadata (fun file => IO.FS.readBinFile file) s.root
  openSegment p id := s.readSealedChild p id
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

def acquireStore (dir : FilePath) : IO Store :=
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

def Store.recoverChild (store : Store) : IO (Session × SingleFile.Handle) :=
  checked <| Segmented.reopenWith store.callbacks
    (fun policy id resume => liftM <| withActiveChild (error := IO.Error)
      (store.acquireChild policy id) SingleFile.close (fun child => do
        let batches ← SingleFile.scan child
        checked (resume child batches)))
    (fun session child => pure (session, child))

private def install (dir : FilePath) (fresh : Option (Policy × Nat)) : IO Handle := do
  let load (store : Store) := match fresh with
    | some (policy, cap) => do
      unless (← entries store.root).all (fun e => e.fileName == "lock") do
        throw <| IO.userError "segmented WAL directory is not empty"
      pure (.ready store (← checked (Segmented.create store.callbacks policy cap)))
    | none =>
      installReopenedWith store.recoverChild fun entry => do
        store.active.set entry
        return store

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
    let next ← checked (action store.callbacks session)
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

/-- The runtime semantics of a held reference: allocation binds the value,
a read consumes only a valid binding, and the mutex primitives frame it.
This contract contains no WAL operation or abstract disk predicate. -/
structure PhaseMemory where
  holds : {α : Type} → IO.Ref α → α → Void IO.RealWorld → Prop
  allocate : ∀ {α : Type} (value : α) w,
    let r := (IO.mkRef value : BaseIO (IO.Ref α)) w
    holds r.val value r.state
  allocateFrame : ∀ {α β : Type} {ref : IO.Ref α} {value w} (fresh : β),
    holds ref value w → holds ref value ((IO.mkRef fresh : BaseIO (IO.Ref β)) w).state
  set : ∀ {α : Type} (ref : IO.Ref α) (value : α) w,
    holds ref value ((ref.set value : BaseIO Unit) w).state
  newMutex : ∀ {α : Type} {ref : IO.Ref α} {value w},
    holds ref value w → holds ref value (Std.BaseMutex.new w).state
  lock : ∀ {α : Type} {ref : IO.Ref α} {value w} (mutex : Std.BaseMutex),
    holds ref value w → holds ref value (mutex.lock w).state
  read : ∀ {α : Type} {ref : IO.Ref α} {value w},
    holds ref value w →
    let got := (ref.get : BaseIO α) w
    got.val = value ∧ holds ref value got.state
  readFrame : ∀ {α β : Type} {ref : IO.Ref α} {value w} (other : IO.Ref β),
    holds ref value w → holds ref value ((other.get : BaseIO β) w).state
  unlock : ∀ {α : Type} {ref : IO.Ref α} {value w} (mutex : Std.BaseMutex),
    holds ref value w → holds ref value (mutex.unlock w).state

def PhaseMemory.Ready (heap : PhaseMemory) (handle : Handle) (session : Session)
    (w : Void IO.RealWorld) : Prop :=
  ∃ store child, heap.holds handle.state (.ready store session) w ∧
    heap.holds store.active (some (session.control.active, child)) w

/-- The concrete recovery run that produced this session also returned the
child stored under its active ID. The outer phase ref is allocated after
that transfer, and the public handle uses that ref and the reached mutex. -/
def ReturnedChild (dir : FilePath) (session : Session) (handle : Handle)
    (start finish : Void IO.RealWorld) : Prop :=
  ∃ store acquired child recovered,
    acquireStore dir start = .ok store acquired ∧
    store.recoverChild acquired = .ok (session, child) recovered ∧
    let attached := (store.active.set (some (session.control.active, child)) : BaseIO Unit) recovered
    let cell := (IO.mkRef (.ready store session : Phase Store) : BaseIO _) attached.state
    let mutex := Std.BaseMutex.new cell.state
    handle.state = cell.val ∧ handle.mutex = mutex.val ∧ finish = mutex.state

private theorem base_out (a : BaseIO α) (w : Void IO.RealWorld) :
    (liftM a : IO α) w = .ok (a w).val (a w).state := by
  change BaseIO.toEIO a w = _
  cases ran : a w
  simp [BaseIO.toEIO, ran]

private theorem attempt_ok (body : IO α) (cleanup : IO Unit)
    (ran : cleanupOnError (error := IO.Error) body cleanup w = .ok x t) :
    body w = .ok x t := by
  cases action : body w with
  | ok a u =>
    simpa [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, action] using ran
  | error e u =>
    cases released : cleanup u <;>
      simp [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, action, released,
        Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure,
        throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] at ran

theorem openExisting_ready (heap : PhaseMemory) (dir : FilePath)
    (opened : openExisting dir start = .ok handle finish) :
    ∃ session, ReturnedChild dir session handle start finish ∧ heap.Ready handle session finish := by
  let load (s : Store) := installReopenedWith s.recoverChild (fun entry => do
    s.active.set entry
    return s)
  let construct (s : Store) : IO (IO.Ref (Phase Store) × Std.BaseMutex) := do
    let p ← load s
    let cell ← IO.mkRef p
    return (cell, ← Std.BaseMutex.new)
  change (do
    let (ref, mutex) ← (do
      let s ← acquireStore dir
      cleanupOnError (error := IO.Error) (construct s) s.release)
    pure (Handle.mk ref mutex) : IO Handle) start = .ok handle finish at opened
  cases acquired : acquireStore dir start with
  | error e u => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, acquired] at opened
  | ok s u =>
    cases constructed : cleanupOnError (error := IO.Error) (construct s) s.release u with
    | error e t => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, acquired, constructed] at opened
    | ok pair t =>
      obtain ⟨ref, mutex⟩ := pair
      have success := attempt_ok (construct s) s.release constructed
      cases recovery : s.recoverChild u with
      | error e v =>
        simp [construct, load, installReopenedWith, Bind.bind, instMonadEIO._aux_13,
          EST.bind, recovery] at success
      | ok result v =>
        obtain ⟨session, child⟩ := result
        let attached := (s.active.set (some (session.control.active, child)) : BaseIO Unit) v
        let cell := (IO.mkRef (.ready s session : Phase Store) : BaseIO _) attached.state
        let made := Std.BaseMutex.new cell.state
        have wrote : (s.active.set (some (session.control.active, child)) : IO Unit) v =
            .ok attached.val attached.state := base_out _ _
        have mkCell : (liftM (IO.mkRef (.ready s session)) : IO (IO.Ref (Phase Store))) attached.state =
            .ok cell.val cell.state := base_out _ _
        have mkMutex : (liftM Std.BaseMutex.new : IO _) cell.state = .ok made.val made.state := base_out _ _
        have h : EST.Out.ok (cell.val, made.val) made.state = (EST.Out.ok (ref, mutex) t :
            EST.Out IO.Error IO.RealWorld _) := by
          simpa [construct, load, installReopenedWith, Bind.bind, instMonadEIO._aux_13,
            EST.bind, recovery, wrote, mkCell, mkMutex, Pure.pure, instMonadEIO._aux_5, EST.pure] using success
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := EST.Out.ok.inj h
        have outer : (Handle.mk cell.val made.val, made.state) = (handle, finish) := by
          simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, acquired, constructed,
            Pure.pure, instMonadEIO._aux_5, EST.pure] using opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj outer
        exact ⟨session, ⟨s, u, child, v, acquired, recovery, rfl, rfl, rfl⟩,
          s, child, heap.newMutex (heap.allocate _ _),
          heap.newMutex (heap.allocateFrame _ (heap.set _ _ _))⟩

theorem scan_readyAt (heap : PhaseMemory) {handle : Handle} (ready : heap.Ready handle session w) :
    ∃ t, scan handle w = .ok session.view t ∧ heap.Ready handle session t := by
  obtain ⟨store, child, owns, ownsChild⟩ := ready
  let locked := handle.mutex.lock w
  let got := (handle.state.get : BaseIO (Phase Store)) locked.state
  let released := handle.mutex.unlock got.state
  obtain ⟨value, stillHeld⟩ := heap.read (heap.lock handle.mutex owns)
  refine ⟨released.state, ?_, store, child, heap.unlock _ stillHeld,
    heap.unlock _ (heap.readFrame _ (heap.lock _ ownsChild))⟩
  change got.val = .ready store session at value
  have raw : (handle.state.get : IO (Phase Store)) locked.state =
      .ok (.ready store session) got.state := by
    change EST.Out.ok got.val got.state = _
    rw [value]
  have lockRun : (liftM handle.mutex.lock : IO Unit) w = .ok locked.val locked.state := base_out _ _
  have unlockRun : (liftM handle.mutex.unlock : IO Unit) got.state =
      .ok released.val released.state := base_out _ _
  unfold scan Handle.locked
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, lockRun, tryFinally, tryFinally',
    MonadFinally.tryFinally', instMonadFinallyEIO._aux_1, Functor.map, instMonadEIO._aux_1]
  rw [raw]
  have cached : checked (scanWith (.ready store session)) got.state = .ok session.view got.state := rfl
  simp only [cached, unlockRun]
  rfl

/-- Open and public scan agree on the recovered session using the original
handle's mutex, phase cell and registered child, starting at the reached
installation state. The byte/disk meaning of the inner recovery lives below
ReturnedChild and is needed to identify this view with a client's history. -/
theorem openExisting_scan (heap : PhaseMemory) (dir : FilePath)
    (opened : openExisting dir start = .ok h installed) :
    ∃ session t, ReturnedChild dir session h start installed ∧
      scan h installed = .ok session.view t ∧ heap.Ready h session t := by
  obtain ⟨session, returned, ready⟩ := openExisting_ready heap dir opened
  obtain ⟨t, scanned, stillReady⟩ := scan_readyAt heap ready
  exact ⟨session, t, returned, scanned, stillReady⟩

end WalRecoverySlice.Segmented.Native
