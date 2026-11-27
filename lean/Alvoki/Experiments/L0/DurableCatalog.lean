import Alvoki.Experiments.L0.TableProofs

namespace ExperimentalL0
open ImmutableSSTable Unified

/-- The table namespace projections used at creation, restart and lookup. -/
structure TableNamespace (σ : Type) where
  directory : System.FilePath
  inode : Type
  names : σ → System.FilePath → Option inode
  contents : σ → inode → Option ByteArray

def TableNamespace.Bound (ns : TableNamespace σ) (s : σ) (id : UInt64) (rows : Rows) : Prop :=
  ∃ identity bytes, ns.names s (tablePath ns.directory id) = some identity ∧
    ns.contents s identity = some bytes ∧
    Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes

def TableNamespace.Represents (ns : TableNamespace σ) (s : σ) (tables : Catalog) : Prop :=
  ∀ id rows, tables id = some rows → ns.Bound s id rows

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

end ExperimentalL0
