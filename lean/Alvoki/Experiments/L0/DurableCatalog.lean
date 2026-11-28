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

/-- The healthy check uses the same catalog binding and scoped acquire
as lookup. Its typed continuation returns no descriptor. -/
theorem TableNamespace.scopedCheck {id : UInt64} {ns : TableNamespace σ}
    (bound : ns.Bound s id rows) (handle : IO.FS.Handle)
    {start checked entered : Void IO.RealWorld}
    (stat : (nativeTableStat (tablePath ns.directory id)).run start = .ok (.ok metadata) checked)
    (regular : isTableFile metadata = true)
    (acquired : IO.FS.Handle.mk (tablePath ns.directory id) .read checked = .ok handle entered)
    (inodeAt : IO.FS.Handle → Option ns.inode)
    (picked : inodeAt handle = ns.names s (tablePath ns.directory id))
    (reads : ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      nativeReadPrimitives.ReadsExactly handle bytes) :
    (nativeTableAt ns.directory id (fun _ => pure ())).run start = .ok (.ok ()) entered := by
  rw [nativeTableAt_acquired stat regular acquired]
  obtain ⟨inode, bytes, name, content, image⟩ := bound
  have checked := native_table_check handle image (reads inode bytes (picked.trans name) content)
  unfold nativeTableAction
  rw [checked]
  rfl

/-- Stat and acquire select the durable name. The executable scope passes
the acquired handle to the checked SSTable reader, which produces the
lookup result for this inode. -/
theorem TableNamespace.scopedLookup {id : UInt64} {ns : TableNamespace σ}
    (bound : ns.Bound s id rows) (handle : IO.FS.Handle) (key : UInt64)
    {start checked entered : Void IO.RealWorld}
    (stat : (nativeTableStat (tablePath ns.directory id)).run start = .ok (.ok metadata) checked)
    (regular : isTableFile metadata = true)
    (acquired : IO.FS.Handle.mk (tablePath ns.directory id) .read checked = .ok handle entered)
    (inodeAt : IO.FS.Handle → Option ns.inode)
    (picked : inodeAt handle = ns.names s (tablePath ns.directory id))
    (reads : ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      ReadSafety (handleSource handle) bytes)
    (ran : (nativeTableAt ns.directory id (·.lookup key)).run start = .ok (.ok value) reached) :
    value = lookupRows rows key := by
  obtain ⟨identity, bytes, named, stored, built⟩ := bound
  have safe := reads identity bytes (picked.trans named) stored
  rw [nativeTableAt_acquired stat regular acquired] at ran
  change (BaseIO.toEIO (withTableSource (handleSource handle) id (·.lookup key)).toBaseIO)
    entered = _ at ran
  cases step : withTableSource (handleSource handle) id (·.lookup key) entered with
  | error error after =>
    simp [BaseIO.toEIO, EIO.toBaseIO, step] at ran
  | ok actual after =>
    have exactValue := table_lookup_success built safe key step
    simp [BaseIO.toEIO, EIO.toBaseIO, step] at ran
    exact ran.1.symm.trans exactValue

end ExperimentalL0
