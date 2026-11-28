import Alvoki.Experiments.L0.TableProofs

namespace ExperimentalL0
open ImmutableSSTable Unified

/-- The table namespace projections used at creation, restart and lookup. -/
structure TableNamespace (σ : Type) where
  directory : System.FilePath
  inode : Type
  names : σ → System.FilePath → Option inode
  contents : σ → inode → Option ByteArray

/-- L0's custody cell does not own table names or inode contents. -/
def TableNamespace.storage (ns : TableNamespace σ) : TableNamespace (phase × σ) where
  directory := ns.directory
  inode := ns.inode
  names s := ns.names s.2
  contents s := ns.contents s.2

def TableNamespace.Bound (ns : TableNamespace σ) (s : σ) (id : UInt64) (rows : Rows) : Prop :=
  ∃ identity bytes, ns.names s (tablePath ns.directory id) = some identity ∧
    ns.contents s identity = some bytes ∧
    Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes

def TableNamespace.Represents (ns : TableNamespace σ) (s : σ) (tables : Catalog) : Prop :=
  ∀ id rows, tables id = some rows → ns.Bound s id rows

theorem TableNamespace.empty (ns : TableNamespace σ) (s : σ) :
    ns.Represents s (fun _ => none) := by
  intro id rows absent
  cases absent

/-- A namespace frame preserves the name and contents of each durable
catalog binding. Unreferenced names may vary across interruption. -/
def TableNamespace.Keeps (ns : TableNamespace σ) (before after : σ) (tables : Catalog) : Prop :=
  ∀ id rows identity bytes, tables id = some rows →
    ns.names before (tablePath ns.directory id) = some identity →
    ns.contents before identity = some bytes →
    ns.names after (tablePath ns.directory id) = some identity ∧
      ns.contents after identity = some bytes

theorem TableNamespace.Keeps.trans {ns : TableNamespace σ}
    (first : ns.Keeps a b tables) (second : ns.Keeps b c tables) :
    ns.Keeps a c tables := by
  intro id rows identity bytes bound name content
  obtain ⟨name, content⟩ := first id rows identity bytes bound name content
  exact second id rows identity bytes bound name content

theorem TableNamespace.Represents.frame {ns : TableNamespace σ}
    (valid : ns.Represents before tables) (keeps : ns.Keeps before after tables) :
    ns.Represents after tables := by
  intro id rows bound
  obtain ⟨identity, bytes, name, content, image⟩ := valid id rows bound
  obtain ⟨name, content⟩ := keeps id rows identity bytes bound name content
  exact ⟨identity, bytes, name, content, image⟩

/-- Exact insertion into the logical catalog paired with durable namespace
publication. Earlier bindings remain available without reclamation. -/
theorem TableNamespace.Represents.insert {id : UInt64} {ns : TableNamespace σ}
    (valid : ns.Represents before tables) (keeps : ns.Keeps before after tables)
    (new : ns.Bound after id rows) :
    ns.Represents after (fun key => if key = id then some rows else tables key) := by
  intro key content found
  by_cases same : key = id
  · subst key
    simp at found
    subst content
    exact new
  · simp [same] at found
    exact (valid.frame keeps) key content found

theorem TableNamespace.lookup {id : UInt64} {ns : TableNamespace σ}
    (bound : ns.Bound s id rows) (handle : IO.FS.Handle)
    (inodeAt : IO.FS.Handle → Option ns.inode)
    (selected : inodeAt handle = ns.names s (tablePath ns.directory id))
    (readEffects : ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      nativeReadPrimitives.ReadsExactly handle bytes) (key : UInt64) :
    withTableSource (handleSource handle) id (·.lookup key) = pure (lookupRows rows key) := by
  obtain ⟨inode, bytes, name, content, image⟩ := bound
  exact native_table_lookup handle image (readEffects inode bytes (selected.trans name) content) key

/-- The selected descriptor serves the immutable image. Use the stat
and scoped action reports at the worlds actually reached, including the
world returned after the descriptor scope exits. -/
theorem TableNamespace.scopedLookup {id : UInt64} {ns : TableNamespace σ}
    (bound : ns.Bound s id rows) (handle : IO.FS.Handle) (key : UInt64)
    {start checked entered acted done : Void IO.RealWorld}
    (stat : (nativeTableStat (tablePath ns.directory id)).run start = .ok (.ok metadata) checked)
    (regular : isTableFile metadata = true)
    (action : (nativeTableAction handle id (·.lookup key)).run entered = .ok (.ok value) acted)
    (scope : (nativeTableReadScope (tablePath ns.directory id)
        (fun held => nativeTableAction held id (·.lookup key))).run checked = .ok (.ok value) done)
    (inodeAt : IO.FS.Handle → Option ns.inode)
    (picked : inodeAt handle = ns.names s (tablePath ns.directory id))
    (reads : ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      nativeReadPrimitives.ReadsExactly handle bytes) :
    (nativeTableAt ns.directory id (·.lookup key)).run start =
      .ok (.ok (lookupRows rows key)) done := by
  have read := ns.lookup bound handle inodeAt picked reads key
  have actual : nativeTableAction handle id (·.lookup key) = pure (lookupRows rows key) := by
    unfold nativeTableAction
    rw [read]
    rfl
  rw [actual] at action
  change EST.Out.ok (Except.ok (lookupRows rows key)) entered = _ at action
  have same := Except.ok.inj (EST.Out.ok.inj action).1
  let resume (md : IO.FS.Metadata) : ExceptT String IO (Option Mutation) :=
    if isTableFile md then nativeTableReadScope (tablePath ns.directory id)
      (fun held => nativeTableAction held id (·.lookup key))
    else throw "expected a singly linked regular SSTable"
  change ((nativeTableStat (tablePath ns.directory id) >>= resume).run) start = _
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, stat]
  simpa [resume, regular, same] using scope

end ExperimentalL0
