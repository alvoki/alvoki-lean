import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.L0.DurableCatalog
import Alvoki.Experiments.L0.Refinement
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback
import Alvoki.Experiments.DurableBlob.Proofs

namespace ExperimentalL0.NativeRead
open ImmutableSSTable Unified Lifecycle
abbrev W := Void IO.RealWorld
abbrev F := ExceptT String IO

/-- Keep both native error channels when reasoning about the reported run. -/
def FilePost (P : W → Prop) (q : α → Prop) (a : F α) : Prop :=
  ∀ w, P w → match a.run w with
    | .ok (.ok x) t => P t ∧ q x
    | .ok (.error _) t | .error _ t => P t

/-- These constructors select the two executable table callbacks. Their
closed result families carry no reader, source, closure or descriptor. -/
inductive Operation where
  | check
  | lookup (key : UInt64)

abbrev Operation.Result : Operation → Type
  | .check => Unit
  | .lookup _ => Option Mutation

abbrev Operation.use : (op : Operation) → TypedTable (EIO String) UInt64 Mutation → EIO String op.Result
  | .check, _ => pure ()
  | .lookup key, table => table.lookup key

structure Call where
  directory : System.FilePath
  id : UInt64
  op : Operation
  start : W

/-- Successful construction of a handle followed by return to the caller
of this particular withFile scope. Keep the outer return separate from
the inner action's final world: in Lean their tokens can compare equal. -/
structure Exit (c : Call) where
  checked : W
  metadata : IO.FS.Metadata
  handle : IO.FS.Handle
  entered : W
  reached : W
  reply : Except String c.op.Result
  stat : (nativeTableStat (tablePath c.directory c.id)).run c.start = .ok (.ok metadata) checked
  regular : isTableFile metadata = true
  acquired : IO.FS.Handle.mk (tablePath c.directory c.id) .read checked = .ok handle entered
  body : (withTableSource (handleSource handle) c.id c.op.use).toBaseIO entered = ⟨reply, reached⟩
  returned : (nativeTableAt c.directory c.id c.op.use).run c.start = .ok reply reached

/-- Given the stat and successful open, the scope has an actual exit on both
inner outcomes. No successful action or independent release receipt is needed. -/
def Call.exitOfAcquire (c : Call)
    (stat : (nativeTableStat (tablePath c.directory c.id)).run c.start = .ok (.ok md) checked)
    (regular : isTableFile md = true)
    (acquired : IO.FS.Handle.mk (tablePath c.directory c.id) .read checked = .ok h entered) :
    Exit c := by
  let inner := (withTableSource (handleSource h) c.id c.op.use).toBaseIO entered
  refine ⟨checked, md, h, entered, inner.state, inner.val, stat, regular, acquired, rfl, ?_⟩
  rw [nativeTableAt_acquired stat regular acquired]
  change (BaseIO.toEIO (withTableSource (handleSource h) c.id c.op.use).toBaseIO) entered = _
  rfl

/-- The local runtime contract observes a released handle *at a labelled
scope exit*. A manual caller that keeps a reference can execute the same
primitives and reach the same opaque IO world; it has no such return event.
Private borrows exclude any reference saved in the heap or retained by FFI.
Failed fdopen can leak a raw fd on Lean 4.36 before an Exit exists. -/
structure Lifetime where
  privateBorrow : IO.FS.Handle → W → Prop
  liveAtReturn : {c : Call} → Exit c → IO.FS.Handle → Prop
  lastDrop : ∀ {c : Call} (exit : Exit c), privateBorrow exit.handle exit.reached →
    ¬ liveAtReturn exit exit.handle

def Call.Balanced (c : Call) (life : Lifetime) : Prop :=
  ∀ exit : Exit c, ¬ life.liveAtReturn exit exit.handle

theorem Call.Balanced.released {c : Call} (all : c.Balanced life)
    (stat : (nativeTableStat (tablePath c.directory c.id)).run c.start = .ok (.ok md) checked)
    (regular : isTableFile md = true)
    (acquired : IO.FS.Handle.mk (tablePath c.directory c.id) .read checked = .ok h entered) :
    ¬ life.liveAtReturn (c.exitOfAcquire stat regular acquired) h :=
  all (c.exitOfAcquire stat regular acquired)

/-- All fields concern a single primitive. A successful acquisition
transfers custody from an empty scope to a fresh, private borrow. -/
structure Primitives (ns : TableNamespace W) (life : Lifetime) (P : W → Prop) where
  inodeOf : IO.FS.Handle → W → Option ns.inode
  stat : ∀ path, FilePost P (fun _ => True) (nativeTableStat path)
  openRead : ∀ path inode bytes w, P w → ns.names w path = some inode →
    ns.contents w inode = some bytes →
    match IO.FS.Handle.mk path .read w with
    | .error _ t => P t
    | .ok h t => P t ∧ life.privateBorrow h t ∧ inodeOf h t = some inode ∧ ns.contents t inode = some bytes
  size : ∀ h inode bytes, ReadPost
    (fun w => P w ∧ life.privateBorrow h w ∧ inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
    (· = bytes.size) (nativeReadPrimitives.size h)
  pread : ∀ h inode bytes (offset : UInt64) (count : USize),
    count.toNat ≤ maxRowSize → offset.toNat + count.toNat ≤ maxFileSize → ReadPost
      (fun w => P w ∧ life.privateBorrow h w ∧ inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
      (· = bytes.extract offset.toNat (offset.toNat + count.toNat))
      (nativeReadPrimitives.pread h offset count)

theorem Primitives.reads (p : Primitives ns life P) (h inode bytes) : ScopedRead
    (fun w => P w ∧ life.privateBorrow h w ∧ p.inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
    (handleSource h) bytes where
  size := p.size h inode bytes
  read offset count := by
    by_cases fits : count ≤ maxRowSize ∧ offset + count ≤ maxFileSize
    · have small : maxRowSize < USize.size := by
        rcases System.Platform.numBits_eq with bits | bits <;> simp [USize.size, bits, maxRowSize]
      have countCast := USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt fits.1 small)
      have offsetCast := UInt64.toNat_ofNat_of_lt' (n := offset)
        (Nat.lt_of_le_of_lt (by omega : offset ≤ maxFileSize) (by decide))
      have read := p.pread h inode bytes offset.toUInt64 count.toUSize
      rw [offsetCast, countCast] at read
      simpa [handleSource, ReadPrimitives.source, Nat.not_lt_of_ge fits.1, Nat.not_lt_of_ge fits.2]
        using read fits.1 fits.2
    · intro w valid
      have outside : maxRowSize < count ∨ maxFileSize < offset + count := by omega
      rcases outside with large | large <;>
        simp [handleSource, ReadPrimitives.source, large, Bind.bind, instMonadEIO._aux_13, EST.bind] <;>
        exact valid

/-- A scoped result includes the resource guarantee for precisely the returned
table call. Stat rejection and failed construction cannot furnish an Exit. -/
theorem tableAction {id : UInt64} (prim : Primitives ns life P) (op : Operation)
    (q : op.Result → Prop) (bound : ∀ w, P w → ns.Bound w id rows)
    (body : ∀ h inode bytes, Image Alvoki.CRC32C.extend (tableLayout id)
        (rows.map (Entry.encode keyCodec mutationCodec)) bytes →
      ReadPost (fun w => P w ∧ life.privateBorrow h w ∧ prim.inodeOf h w = some inode ∧
          ns.contents w inode = some bytes) q (withTableSource (handleSource h) id op.use))
    (w : W) (valid : P w) :
    let c : Call := ⟨ns.directory, id, op, w⟩
    c.Balanced life ∧ match (nativeTableAt ns.directory id op.use).run w with
      | .ok (.ok x) t => P t ∧ q x
      | .ok (.error _) t | .error _ t => P t := by
  intro c
  have keep := prim.stat (tablePath ns.directory id) w valid
  constructor
  · intro exit
    obtain ⟨t, md, h, entered, reached, reply, stat, regular, opened, done_, returned⟩ := exit
    rw [stat] at keep
    obtain ⟨inode, bytes, named, stored, built⟩ := bound t keep.1
    have held := prim.openRead _ _ _ _ keep.1 named stored
    rw [opened] at held
    have obs := body h inode bytes built entered held
    apply life.lastDrop
    cases ran : withTableSource (handleSource h) id op.use entered with
    | ok x after =>
      rw [ran] at obs
      change (withTableSource (handleSource h) id op.use).toBaseIO entered = _ at done_
      simp [EIO.toBaseIO, ran] at done_
      exact done_.2 ▸ obs.1.2.1
    | error e after =>
      rw [ran] at obs
      change (withTableSource (handleSource h) id op.use).toBaseIO entered = _ at done_
      simp [EIO.toBaseIO, ran] at done_
      exact done_.2 ▸ obs.2.1
  · rw [nativeTableAt_reached]
    cases st : (nativeTableStat (tablePath ns.directory id)).run w with
    | error e t => rw [st] at keep; exact keep
    | ok r t =>
      rw [st] at keep
      cases r with
      | error e => exact keep
      | ok md =>
        by_cases regular : isTableFile md = true
        · simp only [regular, ite_true]
          obtain ⟨inode, bytes, named, stored, built⟩ := bound t keep.1
          have acquired := prim.openRead _ _ _ _ keep.1 named stored
          cases opened : IO.FS.Handle.mk (tablePath ns.directory id) .read t with
          | error e u => simpa [opened] using acquired
          | ok h u =>
            rw [opened] at acquired
            have obs := body h inode bytes built u acquired
            have lifted : (nativeTableAction h id op.use).run u =
                (BaseIO.toEIO (withTableSource (handleSource h) id op.use).toBaseIO : IO _) u := rfl
            simp only [lifted]
            cases ran : withTableSource (handleSource h) id op.use u with
            | error e v =>
              rw [ran] at obs
              simpa [BaseIO.toEIO, EIO.toBaseIO, ran] using obs.1
            | ok x v =>
              rw [ran] at obs
              simpa [BaseIO.toEIO, EIO.toBaseIO, ran] using And.intro obs.1.1 obs.2
        · simpa [regular] using keep.1

theorem table {id : UInt64} (prim : Primitives ns life P)
    (bound : ∀ w, P w → ns.Bound w id rows) (key : UInt64) (w : W) (valid : P w) :
    (Call.mk ns.directory id (.lookup key) w).Balanced life ∧
    match (nativeTableAt ns.directory id (·.lookup key)).run w with
    | .ok (.ok x) t => P t ∧ x = lookupRows rows key
    | .ok (.error _) t | .error _ t => P t := by
  have post := tableAction prim (.lookup key) (fun x => x = lookupRows rows key) bound
    (fun h inode bytes built => table_lookup_scoped (prim.reads h inode bytes) built key) w valid
  constructor
  · exact post.1
  · have same : (Operation.lookup key).use = (fun t => t.lookup key) := rfl
    have obs := post.2
    rw [same] at obs
    cases ran : (nativeTableAt ns.directory id (·.lookup key)).run w with
    | error => rw [ran] at obs; exact obs
    | ok r t => rw [ran] at obs; cases r <;> exact obs

/-- Erase the distinction between reported errors only inside the existing L0
model proof. Both error channels carry their actual reached world. -/
def lower (a : F α) : StorageM W α := fun w =>
  match a.run w with
  | .ok (.ok x) t => .ok x t
  | .ok (.error e) t => .error e t
  | .error e t => .error (toString e) t

private theorem lower_bind (a : F α) (f : α → F β) :
    lower (a >>= f) = lower a >>= fun x => lower (f x) := by
  funext w
  unfold lower
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ran : a.run w with
  | error => rfl
  | ok r t => cases r <;> rfl

private def project (ops : Components F) : Components (StorageM W) where
  append b := lower (ops.append b)
  scan := lower ops.scan
  reopenWal := lower ops.reopenWal
  manifest := ⟨fun v => lower (ops.manifest.publish v), lower ops.manifest.reopen⟩
  tables := ⟨fun rows => lower (ops.tables.create rows), fun id => lower (ops.tables.check id),
    fun id k => lower (ops.tables.lookup id k)⟩

private theorem lower_tables (ops : Components F) (k : UInt64) (ids : List UInt64) :
    lower (lookupTables ops.tables k ids) = lookupTables (project ops).tables k ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [lookupTables, lower_bind]
    congr 1
    funext x
    cases x with
    | none => exact ih
    | some => rfl

private theorem lower_get (ops : Components F) (session : Session) (key : UInt64) :
    lower (get ops session key) = get (project ops) session key := by
  unfold get
  split
  · rfl
  · rw [lower_bind, lower_tables]
    rfl

abbrev Wal := WalRecoverySlice.Segmented.Native.Handle

private def readOps (dir : System.FilePath) : Components F := {
    append := fun _ => throw "unused", scan := throw "unused", reopenWal := throw "unused",
    manifest := ⟨fun _ => throw "unused", throw "unused"⟩,
    tables := ⟨fun _ => throw "unused", fun _ => throw "unused",
      fun id k => nativeTableAt dir id (·.lookup k)⟩ }

/-- Instrument only the lookup field of the shared get schedule. The trace
contains each dynamically reached table scope, most recent first. -/
private def logged (dir : System.FilePath) : Components (StorageM (W × List Call)) where
  append _ := throw "unused"
  scan := throw "unused"
  reopenWal := throw "unused"
  manifest := ⟨fun _ => throw "unused", throw "unused"⟩
  tables := ⟨fun _ => throw "unused", fun _ => throw "unused", fun id key state =>
    let calls := Call.mk dir id (.lookup key) state.1 :: state.2
    match lower (nativeTableAt dir id (·.lookup key)) state.1 with
    | .ok x t => .ok x (t, calls)
    | .error e t => .error e (t, calls)⟩

private def erase : EStateM.Result String (W × List Call) α → EStateM.Result String W α
  | .ok x s => .ok x s.1
  | .error e s => .error e s.1

private def calls : EStateM.Result String (W × List Call) α → List Call
  | .ok _ s | .error _ s => s.2

private def Erases (logged : StorageM (W × List Call) α) (plain : StorageM W α) : Prop :=
  ∀ w log, erase (logged (w, log)) = plain w

private theorem Erases.bind {a : StorageM (W × List Call) α} {b : StorageM W α}
    {f : α → StorageM (W × List Call) β} {g : α → StorageM W β}
    (first : Erases a b) (next : ∀ x, Erases (f x) (g x)) :
    Erases (a >>= f) (b >>= g) := by
  intro w log
  simp only [Bind.bind, EStateM.bind, ← first w log]
  cases a (w, log) with
  | error => rfl
  | ok x t => exact next x t.1 t.2

private theorem erasesTables (dir : System.FilePath) (key : UInt64) (ids : List UInt64) :
    Erases (lookupTables (logged dir).tables key ids) (lookupTables (project (readOps dir)).tables key ids) := by
  induction ids with
  | nil => intro _ _; rfl
  | cons id ids ih =>
    simp only [lookupTables]
    apply Erases.bind
    · intro w log
      simp only [logged, project, readOps]
      cases lower (nativeTableAt dir id (·.lookup key)) w <;> rfl
    · intro x
      cases x with
      | none => exact ih
      | some => intro _ _; rfl

theorem erasesGet (dir : System.FilePath) (session : Session) (key : UInt64) (w : W) :
    erase (get (logged dir) session key (w, [])) = lower (get (readOps dir) session key) w := by
  rw [lower_get]
  suffices Erases (get (logged dir) session key) (get (project (readOps dir)) session key) from this w []
  unfold get
  split
  · intro _ _; rfl
  · apply Erases.bind (erasesTables dir key session.version.tables)
    intro _ _ _
    rfl

/-- The concrete phase read determines the session and exact entry world
of the logged shared schedule. Erasure preserves its actual returned world
and its returned result (with error-message projection). -/
def publicCalls (ref : IO.Ref (Phase Wal)) (dir : System.FilePath) (key : UInt64) (start : W) : List Call :=
  match (ref.get : IO (Phase Wal)) start with
  | .ok (.online _ session) entered => calls (get (logged dir) session key (entered, []))
  | _ => []

def Released (life : Lifetime) (ref : IO.Ref (Phase Wal)) (dir : System.FilePath)
    (key : UInt64) (start : W) : Prop :=
  ∀ c ∈ publicCalls ref dir key start, c.Balanced life

/-- The value and resource postconditions are proved on the same instrumented
execution. Its erasure runs the callback actually assembled at this root. -/
theorem publicGet (ref : IO.Ref (Phase Wal)) (root : System.FilePath)
    (binding : Native.Handle.AtRoot handle root ref)
    (ns : TableNamespace W) (directory : ns.directory = root / "tables")
    (P : W → Prop) (valid : P start)
    (phase : ∀ w, P w → ∃ t, (ref.get : IO (Phase Wal)) w = .ok (.online wal session) t ∧ P t)
    (catalog : ∀ w, P w → ns.Represents w image.tables)
    (installed : Installed session image history)
    (prim : Primitives ns life P) (key : UInt64) :
    Released life ref ns.directory key start ∧ match Native.get handle key start with
      | .ok x t => x = denote history key ∧ P t
      | .error _ t => P t := by
  let ops := readOps ns.directory
  obtain ⟨entered, read, frame⟩ := phase start valid
  rw [Native.get_atRoot binding read ops (by simp [ops, readOps, directory])]
  let holds := fun s : W × List Call => P s.1 ∧ ∀ c ∈ s.2, c.Balanced life
  have law := get_refines_from (ops := logged ns.directory) (selected := fun _ => image) holds
    (fun s id k rows owned present => by
      obtain ⟨balanced, post⟩ := table prim (fun u hu => catalog u hu id rows present) k s.1 owned.1
      have all_ (c) (member : c ∈ Call.mk ns.directory id (.lookup k) s.1 :: s.2) : c.Balanced life := by
        rcases List.mem_cons.mp member with rfl | old
        · exact balanced
        · exact owned.2 _ old
      simp only [logged, lower]
      cases ran : (nativeTableAt ns.directory id (·.lookup k)).run s.1 with
      | error e t => rw [ran] at post; exact ⟨trivial, post, all_⟩
      | ok r t =>
        rw [ran] at post
        cases r with
        | error => exact ⟨trivial, post, all_⟩
        | ok => exact ⟨post.2, trivial, post.1, all_⟩)
    (entered, []) ⟨frame, by simp⟩ session installed key
  have same := erasesGet ns.directory session key entered
  have post :
      (∀ c ∈ calls (get (logged ns.directory) session key (entered, [])), c.Balanced life) ∧
      match lower (get ops session key) entered with
      | .ok x t => x = denote history key ∧ P t
      | .error _ t => P t := by
    rw [← same]
    cases ran : get (logged ns.directory) session key (entered, []) with
    | error e t => rw [ran] at law; exact ⟨law.2.2, law.2.1⟩
    | ok x t => rw [ran] at law; exact ⟨law.2.2.2, law.1, law.2.2.1⟩
  constructor
  · simpa only [Released, publicCalls, read] using post.1
  · obtain ⟨_, result⟩ := post
    unfold lower at result
    cases ran : (get ops session key).run entered with
    | error e t =>
      simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
      simpa [ran] using result
    | ok r t =>
      cases r <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure,
        instMonadEIO._aux_5, EST.pure] <;> simp [ran] at result <;> assumption

/-- A size error from the first required descriptor reaches the caller with
its exact message and world, for every possible older run list. -/
theorem firstSizeError {id : UInt64} (root : System.FilePath) (ref : IO.Ref (Phase Wal))
    (binding : Native.Handle.AtRoot handle root ref)
    (phase : (ref.get : IO (Phase Wal)) start = .ok (.online wal session) w)
    (miss : session.mem[key]? = none) (first : session.version.tables = id :: older)
    (stat : (nativeTableStat (tablePath (root / "tables") id)).run w = .ok (.ok md) checked)
    (regular : isTableFile md = true)
    (opened : IO.FS.Handle.mk (tablePath (root / "tables") id) .read checked = .ok h entered)
    (failed : (handleSource h).size entered = .error e after) :
    Native.get handle key start = .error (IO.userError e) after ∧
      publicCalls ref (root / "tables") key start = [⟨root / "tables", id, .lookup key, w⟩] := by
  have action : withTableSource (handleSource h) id (·.lookup key) entered = .error e after := by
    simp [withTableSource, openTableChecked, openChecked, readFooter, Bind.bind,
      instMonadEIO._aux_13, EST.bind, failed]
  have lookupError : (nativeTableAt (root / "tables") id (·.lookup key)).run w =
      .ok (.error e) after := by
    rw [nativeTableAt_acquired stat regular opened]
    change (BaseIO.toEIO (withTableSource (handleSource h) id (·.lookup key)).toBaseIO) entered = _
    simp [EIO.toBaseIO, BaseIO.toEIO, action]
  constructor
  · rw [Native.get_atRoot binding phase (readOps (root / "tables")) rfl]
    simp only [get, miss, first, lookupTables, readOps, ExceptT.run_bind]
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, lookupError]
    rfl
  · simp [publicCalls, phase, get, miss, first, lookupTables, logged, lower, lookupError,
      Bind.bind, EStateM.bind, calls]

theorem memHit (ref : IO.Ref (Phase Wal)) (binding : Native.Handle.AtRoot handle root ref)
    (phase : (ref.get : IO (Phase Wal)) w = .ok (.online wal session) entered)
    (hit : session.mem[key]? = some mutation) :
    Native.get handle key w = .ok mutation.value entered := by
  rw [Native.get_atRoot binding phase (readOps (root / "tables")) rfl]
  simp only [get, hit]
  rfl

/-- The caller catches each reported read error and tries the next key on the
same handle. The second get starts in the actual reached world of the first. -/
def readTwice (handle : Native.Handle) (first second : UInt64) :
    BaseIO (Except IO.Error (Option UInt64) × Except IO.Error (Option UInt64)) := do
  let a ← (Native.get handle first).toBaseIO
  let b ← (Native.get handle second).toBaseIO
  return (a, b)

def Observes (history : Rows) (key : UInt64) : Except IO.Error (Option UInt64) → Prop
  | .ok value => value = denote history key
  | .error _ => True

/-- Projections of the owned runtime and storage resources for one root.
The selected logical WAL, manifest and catalog are witnesses associated
with these observations by Online. -/
structure Footprint (inode : Type) where
  rootLock : Option (System.FilePath × IO.FS.Handle)
  phaseRef : Option (IO.Ref (Phase Wal))
  phase : Phase Wal
  readyWal : Wal → Option WalRecoverySlice.Segmented.Session
  disk : WalRecoverySlice.Segmented.Model.Disk
  manifest : DurableBlob.Image
  names : System.FilePath → Option inode
  contents : inode → Option ByteArray

variable {inode : Type}

def tableNamespace (physical : W → Footprint inode) (root : System.FilePath) : TableNamespace W :=
  ⟨root / "tables", inode, fun w => (physical w).names, fun w => (physical w).contents⟩

def Owned (atWorld : Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : IO.Ref (Phase Wal)) : Prop :=
  atWorld.rootLock = some (root, lock) ∧ atWorld.phaseRef = some ref

open WalRecoverySlice.Segmented (Model.Disk)

abbrev Writebacks := WalRecoverySlice.Segmented.Writebacks

namespace Writebacks
export WalRecoverySlice.Segmented.Writebacks (nil next trans installed)
end Writebacks

structure FrameTo (physical : W → Footprint inode) (root : System.FilePath)
    (wal : Wal) (tables : Catalog) (before after : W) (next : Phase Wal) : Prop where
  lock : (physical after).rootLock = (physical before).rootLock
  ref : (physical after).phaseRef = (physical before).phaseRef
  phase : (physical after).phase = next
  child : (physical after).readyWal wal = (physical before).readyWal wal
  disk : Writebacks (physical before).disk (physical after).disk
  manifest : (physical after).manifest.active = (physical before).manifest.active
  survivors : (physical after).manifest.survivors = (physical before).manifest.survivors
  tablesKept : (tableNamespace physical root).Keeps before after tables

abbrev Frame (physical : W → Footprint inode) (root : System.FilePath)
    (wal : Wal) (tables : Catalog) (before after : W) :=
  FrameTo physical root wal tables before after (physical before).phase

theorem Frame.refl : Frame physical root wal tables w w :=
  ⟨rfl, rfl, rfl, rfl, .nil, rfl, rfl, fun _ _ _ _ _ a b => ⟨a, b⟩⟩

theorem Frame.trans (a : Frame physical root wal tables s t) (b : Frame physical root wal tables t u) :
    Frame physical root wal tables s u :=
  ⟨b.lock.trans a.lock, b.ref.trans a.ref, b.phase.trans a.phase, b.child.trans a.child,
    a.disk.trans b.disk, b.manifest.trans a.manifest, b.survivors.trans a.survivors,
    a.tablesKept.trans b.tablesKept⟩

/-- Recovery publishes precisely this session, having obtained the cached
view from the acquired WAL, settled the encoded manifest, and checked
the referenced tables on the reached namespace. -/
structure SessionAt (physical : W → Footprint inode) (root : System.FilePath)
    (lock : IO.FS.Handle) (ref : IO.Ref (Phase Wal)) (wal : Wal) (session : Session)
    (image : Selected) (history : Rows) (w : W) (stage : Phase Wal) : Prop where
  owned : Owned (physical w) root lock ref
  phase : (physical w).phase = stage
  child : ∃ child, (physical w).readyWal wal = some child ∧
    WalRecoverySlice.Segmented.Installed child (physical w).disk ∧ child.view = image.view
  manifest : (physical w).manifest.Stable (L0Manifest.encode image.version)
  catalog : (tableNamespace physical root).Represents w image.tables
  installed : Installed session image history

abbrev Online (physical : W → Footprint inode) (root : System.FilePath)
    (lock : IO.FS.Handle) (ref : IO.Ref (Phase Wal)) (wal : Wal) (session : Session)
    (image : Selected) (history : Rows) (w : W) :=
  SessionAt physical root lock ref wal session image history w (.online wal session)

theorem SessionAt.advance (ready : SessionAt physical root lock ref wal session image history s current)
    (step : FrameTo physical root wal image.tables s t next) :
    SessionAt physical root lock ref wal session image history t next := by
  obtain ⟨child, cached, childDisk, view⟩ := ready.child
  exact ⟨⟨step.lock.trans ready.owned.1, step.ref.trans ready.owned.2⟩,
    step.phase,
    ⟨child, step.child.trans cached, step.disk.installed childDisk, view⟩,
    ⟨step.manifest.trans ready.manifest.1, step.survivors.trans ready.manifest.2⟩,
    ready.catalog.frame step.tablesKept, ready.installed⟩

theorem Online.frame (ready : Online physical root lock ref wal session image history s)
    (step : Frame physical root wal image.tables s t) :
    Online physical root lock ref wal session image history t := by
  have kept := ready.advance step
  rw [ready.phase] at kept
  exact kept

/-- Owned reference primitive. The phase read is required only when the
caller demonstrably holds this lock and owns this exact phase reference. -/
def RefRead (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : IO.Ref (Phase Wal)) (wal : Wal) (tables : Catalog) : Prop :=
  ∀ w, Owned (physical w) root lock ref →
    ∃ t, (ref.get : IO (Phase Wal)) w = .ok (physical w).phase t ∧
      Frame physical root wal tables w t

theorem onlineGet (ready : Online physical root lock ref wal session image history epoch)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables epoch))
    (reached : Frame physical root wal image.tables epoch start) (key : UInt64) :
    Released life ref (root / "tables") key start ∧ match Native.get handle key start with
    | .ok x t => x = denote history key ∧ Frame physical root wal image.tables epoch t ∧
        Online physical root lock ref wal session image history t
    | .error _ t => Frame physical root wal image.tables epoch t ∧
        Online physical root lock ref wal session image history t := by
  obtain ⟨released, post⟩ := publicGet ref root binding (tableNamespace physical root) rfl _ reached
    (fun w valid => by
      have online := ready.frame valid
      obtain ⟨t, ran, keeps⟩ := read w online.owned
      exact ⟨t, online.phase ▸ ran, valid.trans keeps⟩)
    (fun _ frame => (ready.frame frame).catalog) ready.installed prim key
  refine ⟨released, ?_⟩
  cases ran : Native.get handle key start with
  | error =>
    rw [ran] at post
    exact ⟨post, ready.frame post⟩
  | ok =>
    rw [ran] at post
    exact ⟨post.1, post.2, ready.frame post.2⟩

theorem onlineGetTwice (ready : Online physical root lock ref wal session image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables start))
    (first second : UInt64) :
    let result := readTwice handle first second start
    Observes history first result.val.1 ∧ Observes history second result.val.2 ∧
      Released life ref (root / "tables") first start ∧
      Released life ref (root / "tables") second ((Native.get handle first).toBaseIO start).state ∧
      Frame physical root wal image.tables start result.state ∧
      Online physical root lock ref wal session image history result.state := by
  have step (key w) (frame : Frame physical root wal image.tables start w) :
      let r := (Native.get handle key).toBaseIO w
      Observes history key r.val ∧ Released life ref (root / "tables") key w ∧
        Frame physical root wal image.tables start r.state ∧
        Online physical root lock ref wal session image history r.state := by
    obtain ⟨released, post⟩ := onlineGet ready binding read prim frame key
    cases ran : Native.get handle key w with
    | error e t =>
      rw [ran] at post
      simpa only [EIO.toBaseIO, ran] using
        (show Observes history key (.error e) ∧ _ from ⟨trivial, released, post⟩)
    | ok x t =>
      rw [ran] at post
      simpa only [EIO.toBaseIO, ran] using
        (show Observes history key (.ok x) ∧ _ from ⟨post.1, released, post.2⟩)
  obtain ⟨observed, released, frame, _⟩ := step first start .refl
  obtain ⟨next, released', finalFrame, final⟩ := step second _ frame
  exact ⟨observed, next, released, released', finalFrame, final⟩

end ExperimentalL0.NativeRead
