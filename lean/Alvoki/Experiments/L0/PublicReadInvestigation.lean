import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.L0.NativeTableReads

namespace ExperimentalL0.PublicReadInvestigation
open ImmutableSSTable Unified Lifecycle
abbrev W := Void IO.RealWorld
abbrev F := ExceptT String IO

/-- Keep both native error channels when reasoning about the reported run. -/
def FilePost (P : W → Prop) (q : α → Prop) (a : F α) : Prop :=
  ∀ w, P w → match a.run w with
    | .ok (.ok x) t => P t ∧ q x
    | .ok (.error _) t | .error _ t => P t

/-- All fields concern a single primitive or an immutable descriptor's
size and positional reads. The caller chooses the protected footprint P. -/
structure Primitives (ns : TableNamespace W) (P : W → Prop) where
  inodeOf : IO.FS.Handle → W → Option ns.inode
  stat : ∀ path, FilePost P (fun _ => True) (nativeTableStat path)
  openRead : ∀ path inode bytes w, P w → ns.names w path = some inode →
    ns.contents w inode = some bytes →
    match IO.FS.Handle.mk path .read w with
    | .error _ t => P t
    | .ok h t => P t ∧ inodeOf h t = some inode ∧ ns.contents t inode = some bytes
  size : ∀ h inode bytes, ReadPost
    (fun w => P w ∧ inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
    (· = bytes.size) (nativeReadPrimitives.size h)
  pread : ∀ h inode bytes (offset : UInt64) (count : USize),
    count.toNat ≤ maxRowSize → offset.toNat + count.toNat ≤ maxFileSize → ReadPost
      (fun w => P w ∧ inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
      (· = bytes.extract offset.toNat (offset.toNat + count.toNat))
      (nativeReadPrimitives.pread h offset count)

private theorem Primitives.reads (p : Primitives ns P) (h inode bytes) : ScopedRead
    (fun w => P w ∧ p.inodeOf h w = some inode ∧ ns.contents w inode = some bytes)
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

/-- The correct binding is read *after* stat. This allows unrelated state
to move while stat holds the protected catalog invariant. -/
theorem table {id : UInt64} (prim : Primitives ns P)
    (bound : ∀ w, P w → ns.Bound w id rows) (key : UInt64) :
    FilePost P (· = lookupRows rows key) (nativeTableAt ns.directory id (·.lookup key)) := by
  intro w valid
  have keep := prim.stat (tablePath ns.directory id) w valid
  rw [nativeTableAt_reached]
  cases st : (nativeTableStat (tablePath ns.directory id)).run w with
  | error e t =>
    rw [st] at keep
    exact keep
  | ok r t =>
    rw [st] at keep
    cases r with
    | error e =>
      exact keep
    | ok md =>
      by_cases regular : isTableFile md = true
      · simp only [regular, ite_true]
        obtain ⟨inode, bytes, named, stored, built⟩ := bound t keep.1
        have acquired := prim.openRead _ _ _ _ keep.1 named stored
        cases op : IO.FS.Handle.mk (tablePath ns.directory id) .read t with
        | error e u => simpa [op] using acquired
        | ok h u =>
          rw [op] at acquired
          have result := table_lookup_scoped (prim.reads h inode bytes) built key u acquired
          have lifted : (nativeTableAction h id (·.lookup key)).run u =
              (BaseIO.toEIO (withTableSource (handleSource h) id (·.lookup key)).toBaseIO : IO _) u := rfl
          simp only [lifted]
          cases action : withTableSource (handleSource h) id (·.lookup key) u with
          | error e v =>
            rw [action] at result
            simpa [nativeTableAction, ExceptT.run, EIO.toBaseIO, BaseIO.toEIO, action] using result.1
          | ok x v =>
            rw [action] at result
            simpa [nativeTableAction, ExceptT.run, EIO.toBaseIO, BaseIO.toEIO, action] using
              And.intro result.1.1 result.2
      · simpa [regular] using keep.1

/-- Erase the distinction between reported errors only inside the existing L0
model proof. Both error channels carry their actual reached world. -/
private def lower (a : F α) : StorageM W α := NativeTableReads.call id (fun _ t => t) a

private theorem lower_bind (a : F α) (f : α → F β) :
    lower (a >>= f) = lower a >>= fun x => lower (f x) := by
  funext w
  unfold lower NativeTableReads.call
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind, id_eq]
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

/-- The ref and directory are the ones assembled at withOpen. The footprint
can include the root lock, WAL, phase ownership and namespace resources. -/
theorem publicGet (ref : IO.Ref (Phase Wal)) (root : System.FilePath)
    (binding : Native.Handle.AtRoot handle root ref)
    (ns : TableNamespace W) (directory : ns.directory = root / "tables")
    (P : W → Prop) (valid : P start)
    (phase : ∀ w, P w → ∃ t, (ref.get : IO (Phase Wal)) w = .ok (.online wal session) t ∧ P t)
    (catalog : ∀ w, P w → ns.Represents w image.tables)
    (installed : Installed session image history)
    (prim : Primitives ns P) (key : UInt64) :
    match Native.get handle key start with
    | .ok x t => x = denote history key ∧ P t
    | .error _ t => P t := by
  let ops := readOps ns.directory
  obtain ⟨entered, read, frame⟩ := phase start valid
  rw [Native.get_atRoot binding read ops (by simp [ops, readOps, directory])]
  have law := get_refines_from (ops := project ops) (selected := fun _ => image) P
    (fun w id k rows owned present => by
      have post := table prim (fun u hu => catalog u hu id rows present) k w owned
      simp only [project, ops, readOps]
      unfold lower NativeTableReads.call
      simp only [id_eq]
      cases ran : (nativeTableAt ns.directory id (·.lookup k)).run w with
      | error e t => rw [ran] at post; exact ⟨trivial, post⟩
      | ok r t =>
        rw [ran] at post
        cases r with
        | error => exact ⟨trivial, post⟩
        | ok => exact ⟨post.2, trivial, post.1⟩)
    entered frame session installed key
  rw [← lower_get] at law
  unfold lower NativeTableReads.call at law
  cases ran : (get ops session key).run entered with
  | error e t =>
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
    simpa [ran] using law
  | ok r t =>
    cases r <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure] <;> simp [ran] at law <;> assumption

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
    Native.get handle key start = .error (IO.userError e) after := by
  have action : withTableSource (handleSource h) id (·.lookup key) entered = .error e after := by
    simp [withTableSource, openTableChecked, openChecked, readFooter, Bind.bind,
      instMonadEIO._aux_13, EST.bind, failed]
  have lookupError : (nativeTableAt (root / "tables") id (·.lookup key)).run w =
      .ok (.error e) after := by
    rw [nativeTableAt_acquired stat regular opened]
    change (BaseIO.toEIO (withTableSource (handleSource h) id (·.lookup key)).toBaseIO) entered = _
    simp [EIO.toBaseIO, BaseIO.toEIO, action]
  rw [Native.get_atRoot binding phase (readOps (root / "tables")) rfl]
  simp only [get, miss, first, lookupTables, readOps, ExceptT.run_bind]
  simp [Bind.bind, instMonadEIO._aux_13, EST.bind, lookupError]
  rfl

/-- A concrete instantiation of the protected observations. Leaf contracts
frame projected values. Catalog representation and logical correctness are
derived from this frame and the entry invariant. -/
structure Footprint (inode : Type) where
  phase : Phase Wal
  rootHeld : Bool
  selected : Selected
  names : System.FilePath → Option inode
  contents : inode → Option ByteArray

theorem onlineGet {inode : Type} (physical : W → Footprint inode)
    (root : System.FilePath) (ref : IO.Ref (Phase Wal))
    (binding : Native.Handle.AtRoot handle root ref)
    (refRead : ∀ w, ∃ t, (ref.get : IO (Phase Wal)) w = .ok (physical w).phase t ∧
      physical t = physical w)
    (online : (physical start).phase = .online wal session)
    (lock : (physical start).rootHeld = true)
    (installed : Installed session (physical start).selected history)
    (key : UInt64) :
    let ns : TableNamespace W := ⟨root / "tables", inode, fun w => (physical w).names,
      fun w => (physical w).contents⟩
    ns.Represents start (physical start).selected.tables →
    Primitives ns (fun w => physical w = physical start) →
    match Native.get handle key start with
    | .ok x t => x = denote history key ∧ physical t = physical start ∧ (physical t).phase = .online wal session ∧
        (physical t).rootHeld = true ∧ Installed session (physical t).selected history ∧
        ns.Represents t (physical t).selected.tables
    | .error _ t => physical t = physical start ∧ (physical t).phase = .online wal session ∧
        (physical t).rootHeld = true ∧ Installed session (physical t).selected history ∧
        ns.Represents t (physical t).selected.tables := by
  intro ns catalog prim
  have represents (t) (same : physical t = physical start) :
      ns.Represents t (physical start).selected.tables := by
    intro id rows found
    obtain ⟨identity, bytes, named, data, built⟩ := catalog id rows found
    exact ⟨identity, bytes, by simpa [ns, same] using named, by simpa [ns, same] using data, built⟩
  have post := publicGet (wal := wal) ref root binding ns rfl (fun w => physical w = physical start) rfl
    (fun w same => by
      obtain ⟨t, ran, frame⟩ := refRead w
      exact ⟨t, by simpa [same, online] using ran, frame.trans same⟩)
    represents installed prim key
  cases ran : Native.get handle key start with
  | error e t =>
    rw [ran] at post
    dsimp only at post ⊢
    rw [post]
    exact ⟨rfl, online, lock, installed, represents t post⟩
  | ok x t =>
    rw [ran] at post
    dsimp only at post ⊢
    rw [post.2]
    exact ⟨post.1, rfl, online, lock, installed, represents t post.2⟩

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

theorem onlineGetTwice {inode : Type} (physical : W → Footprint inode)
    (root : System.FilePath) (ref : IO.Ref (Phase Wal))
    (binding : Native.Handle.AtRoot handle root ref)
    (refRead : ∀ w, ∃ t, (ref.get : IO (Phase Wal)) w = .ok (physical w).phase t ∧
      physical t = physical w)
    (online : (physical start).phase = .online wal session)
    (lock : (physical start).rootHeld = true)
    (installed : Installed session (physical start).selected history) (first second : UInt64) :
    let ns : TableNamespace W := ⟨root / "tables", inode, fun w => (physical w).names,
      fun w => (physical w).contents⟩
    ns.Represents start (physical start).selected.tables →
    Primitives ns (fun w => physical w = physical start) →
    let result := readTwice handle first second start
    Observes history first result.val.1 ∧ Observes history second result.val.2 ∧
      physical result.state = physical start ∧ ns.Represents result.state (physical start).selected.tables := by
  intro ns catalog prim
  have step (key w) (same : physical w = physical start)
      (present : ns.Represents w (physical w).selected.tables) :
      let r := (Native.get handle key).toBaseIO w
      Observes history key r.val ∧ physical r.state = physical start ∧
        ns.Represents r.state (physical r.state).selected.tables := by
    have post := onlineGet physical root ref binding refRead (wal := wal)
      (same.symm ▸ online : (physical w).phase = .online wal session)
      (same.symm ▸ lock : (physical w).rootHeld = true)
      (same.symm ▸ installed : Installed session (physical w).selected history) key present
      (by simpa only [same] using prim)
    cases ran : Native.get handle key w with
    | ok x t =>
      rw [ran] at post
      obtain ⟨value, frame, _, _, _, remains⟩ := post
      simpa only [EIO.toBaseIO, ran] using
        (show Observes history key (.ok x) ∧ physical t = physical start ∧
          ns.Represents t (physical t).selected.tables from ⟨value, frame.trans same, remains⟩)
    | error e t =>
      rw [ran] at post
      obtain ⟨frame, _, _, _, remains⟩ := post
      simpa only [EIO.toBaseIO, ran] using
        (show Observes history key (.error e) ∧ physical t = physical start ∧
          ns.Represents t (physical t).selected.tables from ⟨trivial, frame.trans same, remains⟩)
  obtain ⟨observed, same, present⟩ := step first start rfl catalog
  obtain ⟨next, finalFrame, finalCatalog⟩ := step second _ same present
  rw [finalFrame] at finalCatalog
  exact ⟨observed, next, finalFrame, finalCatalog⟩

end ExperimentalL0.PublicReadInvestigation
