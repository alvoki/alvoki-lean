import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Segmented.Protocol

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

private def segmentPath (root : FilePath) (id : Nat) := root / s!"segment-{id}"

private def policyStamp (p : Policy) := if p == .boundary then "v3 boundary" else "v3 log"

private def childName (name : String) : Bool :=
  ["lock", "policy", "segment", "commit.0", "commit.1"].contains name

private def inspectChild (dir : FilePath) : IO (Array IO.FS.DirEntry) := do
  unless (← dir.symlinkMetadata).type == .dir do throw <| IO.userError s!"expected segment directory at {dir}"
  let names ← entries dir
  for item in names do
    unless childName item.fileName do throw <| IO.userError s!"unexpected child {item.path}"
    regular item.path (← item.path.symlinkMetadata)
  return names

/-- Reclaim only recognized names after the shared protocol has established
the ID is retired or was never published. A partial deletion is retryable. -/
private def removeSegment (root : FilePath) (id : Nat) : IO Unit := do
  let dir := segmentPath root id
  if (← metadata? dir).isSome then
    let members ← inspectChild dir
    for item in members do IO.FS.removeFile item.path
    IO.FS.removeDir dir

private def acquireRoot (root : FilePath) : IO IO.FS.Handle := do
  let path := root / "lock"
  if let some md ← metadata? path then regular path md
  let lock ← IO.FS.Handle.mk path .append
  unless ← lock.tryLock do throw <| IO.userError "segmented WAL already open"
  return lock

private def wordMax : Nat := 18446744073709551615

private def encodeControl (c : Control) : ByteArray :=
  let mode := if c.policy == .logOnly then "log" else "boundary"
  let body := s!"swal1 {mode} {c.capacity} {c.active} {c.discarded}".toUTF8
  body ++ ⟨(checksumBytes body.data.toList).toArray⟩

private def parseControl (bytes : ByteArray) : IO Control := do
  let bad := IO.userError "invalid segmented WAL control"
  let some body := String.fromUTF8? (bytes.extract 0 (bytes.size - 8)) | throw bad
  let ["swal1", mode, cap, last, base] := body.splitOn " " | throw bad
  let policy ← match mode with
    | "log" => pure Policy.logOnly
    | "boundary" => pure Policy.boundary
    | _ => throw bad
  let some capacity := cap.toNat? | throw bad
  let some active := last.toNat? | throw bad
  let some discarded := base.toNat? | throw bad
  let c := { policy, capacity, active, discarded : Control }
  unless active ≤ wordMax && discarded ≤ wordMax && bytes == encodeControl c do throw bad
  return c

private structure Store where
  root : FilePath
  lock : IO.FS.Handle
  directory : IO.FS.Handle
  active : IO.Ref (Option (Nat × SingleFile.Handle))

private def Store.closeChild (s : Store) : IO Unit := do
  if let some (_, child) ← s.active.swap none then SingleFile.close child

private def Store.release (s : Store) : IO Unit := do
  try s.closeChild finally s.lock.unlock

private def Store.prepare (s : Store) (p : Policy) (id : Nat) : IO Unit := do
  s.closeChild
  -- Only an unpublished successor can already occupy this ID after an interrupted rotation.
  removeSegment s.root id
  let dir := segmentPath s.root id
  IO.FS.createDir dir
  let child ← SingleFile.create dir p
  s.active.set (some (id, child))

private def Store.openChild (s : Store) (p : Policy) (id : Nat) : IO (List Bytes) := do
  s.closeChild
  let dir := segmentPath s.root id
  let names := (← inspectChild dir).map (·.fileName)
  let required := if p == .boundary then ["policy", "segment", "commit.0", "commit.1"] else ["policy", "segment"]
  unless required.all names.contains do throw <| IO.userError s!"incomplete segment {id}"
  let expected := policyStamp p
  unless (← (dir / "policy").metadata).byteSize.toNat == expected.utf8ByteSize &&
      (← IO.FS.readFile (dir / "policy")) == expected do
    throw <| IO.userError s!"segment policy mismatch at {id}"
  let child ← SingleFile.openExisting dir
  s.active.set (some (id, child))
  SingleFile.scan child

private def Store.listIds (s : Store) : IO (List Nat) := do
  let mut ids := []
  for item in ← entries s.root do
    if !["lock", "CONTROL", "CONTROL.next"].contains item.fileName then
      let some id := (item.fileName.drop "segment-".length).toString.toNat?
        | throw <| IO.userError s!"unexpected segmented WAL entry {item.fileName}"
      unless item.fileName == s!"segment-{id}" do throw <| IO.userError s!"invalid segment name {item.fileName}"
      ids := id :: ids
  return ids

private abbrev FileM := ExceptT String IO

private def Store.callbacks (s : Store) : Ops FileM where
  prepareSegment p id := s.prepare p id
  syncRoot := syncHandle s.directory
  stageControl c := do
    unless c.active ≤ wordMax && c.discarded ≤ wordMax do throw "segmented WAL position exhausted"
    let stage := s.root / "CONTROL.next"
    removeRegular stage
    liftM <| IO.FS.withFile stage .writeNew fun h => do
      disableBuffering h
      h.write (encodeControl c)
      h.flush
  syncControl := liftM <| IO.FS.withFile (s.root / "CONTROL.next") .read syncHandle
  renameControl := IO.FS.rename (s.root / "CONTROL.next") (s.root / "CONTROL")
  readControl := do
    let file := s.root / "CONTROL"
    let md ← file.symlinkMetadata
    regular file md
    -- The version, policy, capacity, two UInt64 decimal fields and digest fit in 80 bytes.
    if md.byteSize > 80 then throw "oversized segmented WAL control"
    parseControl (← IO.FS.readBinFile file)
  openSegment p id := s.openChild p id
  appendSegment _ id batch := do
    let some (installed, child) ← s.active.get | throw "no active segment"
    unless installed == id do throw "incorrect active segment"
    SingleFile.append child batch
  listSegments := s.listIds
  removeSegment id := removeSegment s.root id

private def checked (a : FileM α) : IO α := do
  match ← a.run with
  | .ok x => return x
  | .error e => throw <| IO.userError e

private inductive Phase where
  | ready (store : Store) (session : Session)
  | poisoned (store : Store)
  | closed

structure Handle where private mk ::
  private state : IO.Ref Phase
  private mutex : Std.BaseMutex

private def install (dir : FilePath) (fresh : Option (Policy × Nat)) : IO Handle := do
  let root ← IO.FS.realPath dir
  let directory ← IO.FS.Handle.mk root .read
  let lock ← acquireRoot root
  let store := {root, directory, lock, active := ← IO.mkRef none : Store}
  try
    let callbacks := store.callbacks
    let session ← match fresh with
      | some (policy, cap) => do
        unless (← entries root).all (fun e => e.fileName == "lock") do
          throw <| IO.userError "segmented WAL directory is not empty"
        checked (Segmented.create callbacks policy cap)
      | none => checked (Segmented.reopen callbacks)
    return ⟨← IO.mkRef (.ready store session), ← Std.BaseMutex.new⟩
  catch e =>
    store.release
    throw e

def create (dir : FilePath) (policy : Policy) (capacity : Nat) : IO Handle :=
  install dir (some (policy, capacity))

def openExisting (dir : FilePath) : IO Handle := install dir none

private def Handle.locked (h : Handle) (action : IO α) : IO α := do
  h.mutex.lock
  try action finally h.mutex.unlock

private def update (h : Handle) (action : Ops FileM → Session → FileM Session) : IO Unit := h.locked do
  match ← h.state.get with
  | .ready store session =>
    h.state.set (.poisoned store)
    let next ← checked (action store.callbacks session)
    h.state.set (.ready store next)
  | .poisoned _ => throw <| IO.userError "segmented WAL requires reopen"
  | .closed => throw <| IO.userError "segmented WAL closed"

def append (h : Handle) (batch : Bytes) : IO Unit := update h (fun ops s => Segmented.append ops s batch)

def discardThrough (h : Handle) (k : Nat) : IO Unit := update h (fun ops s => Segmented.discardThrough ops s k)

def scan (h : Handle) : IO Contract.View := h.locked do
  match ← h.state.get with
  | .ready _ s => return s.view
  | .poisoned _ => throw <| IO.userError "segmented WAL requires reopen"
  | .closed => throw <| IO.userError "segmented WAL closed"

def close (h : Handle) : IO Unit := h.locked do
  match ← h.state.swap .closed with
  | .ready store _ | .poisoned store => store.release
  | .closed => pure ()

end WalRecoverySlice.Segmented.Native
