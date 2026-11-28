import Std.Data.TreeMap
import Alvoki.Experiments.Manifest.Basic
import Alvoki.Experiments.WAL.Segmented.Contract

namespace ExperimentalL0
open WalRecoverySlice.Segmented

inductive Mutation where
  | put (value : UInt64)
  | delete
  deriving BEq, DecidableEq, Repr

abbrev Change := UInt64 × Mutation
abbrev Rows := List Change
abbrev MemTable := Std.TreeMap UInt64 Mutation
abbrev Database := UInt64 → Option UInt64

def Mutation.value : Mutation → Option UInt64
  | .put v => some v
  | .delete => none

def Change.apply (change : Change) (db : Database) : Database :=
  fun key => if key = change.1 then change.2.value else db key

def insert (mem : MemTable) (change : Change) : MemTable :=
  mem.insert change.1 change.2

def replay (changes : Rows) : MemTable := changes.foldl insert ∅

def lookupRows (rows : Rows) (key : UInt64) : Option Mutation :=
  (rows.find? (fun entry => entry.1 == key)).map Prod.snd

def Rows.Ordered (rows : Rows) : Prop := rows.Pairwise (fun a b => a.1 < b.1)

/-- One mutation occupies exactly one batch. Length distinguishes the formats. -/
def encode (change : Change) : Contract.Batch :=
  let key := Alvoki.pushWordFast ByteArray.empty change.1
  let bytes := match change.2 with
    | .delete => key
    | .put value => Alvoki.pushWordFast key value
  bytes.data.toList

def decode (batch : Contract.Batch) : Option Change :=
  let bytes : ByteArray := ⟨batch.toArray⟩
  if bytes.size = 8 then some (Alvoki.word bytes 0, .delete)
  else if bytes.size = 16 then some (Alvoki.word bytes 0, .put (Alvoki.word bytes 8))
  else none

/-- Successful create allocates a fresh ID and makes exactly the supplied
ordered rows durable. Opens see the same rows across crashes. A failed
create may leave an unreachable artifact. Existing IDs are never modified.
A healthy lookup returns the mutation, including a stored tombstone. -/
structure Tables (m : Type → Type) where
  create : Rows → m UInt64
  check : UInt64 → m Unit
  lookup : UInt64 → UInt64 → m (Option Mutation)

/-- Logical durable rows named by an immutable table ID. A native adapter
must establish these relations on durable names, including after reboot. -/
abbrev Catalog := UInt64 → Option Rows

def Catalog.Preserves (before after : Catalog) : Prop :=
  ∀ id rows, before id = some rows → after id = some rows

def Catalog.Created (before after : Catalog) (id : UInt64) (rows : Rows) : Prop :=
  before id = none ∧ after id = some rows ∧ before.Preserves after

structure Components (m : Type → Type) where
  append : Contract.Batch → m Unit
  scan : m Contract.View
  reopenWal : m Contract.View
  manifest : DurableBlob.Backend m L0Manifest.Version
  tables : Tables m

structure Session where
  version : L0Manifest.Version
  mem : MemTable

def checkTables [Monad m] (ops : Tables m) : List UInt64 → m Unit
  | [] => pure ()
  | id :: ids => do
    ops.check id
    checkTables ops ids

def recover [Monad m] [MonadExceptOf String m] (ops : Components m) : m Session := do
  let version ← ops.manifest.reopen
  let view ← ops.reopenWal
  let boundary := version.flushedThrough.toNat
  unless view.base ≤ boundary ∧ boundary ≤ view.tail do
    throw "manifest watermark outside the WAL view"
  let some changes := (view.batches.drop (boundary - view.base)).mapM decode
    | throw "invalid L0 mutation batch"
  checkTables ops.tables version.tables
  return ⟨version, replay changes⟩

def write [Monad m] [MonadExceptOf String m] (ops : Components m)
    (session : Session) (change : Change) : m Session := do
  unless (← ops.scan).tail + 1 < UInt64.size do
    throw "absolute WAL position exhausted"
  ops.append (encode change)
  return { session with mem := insert session.mem change }

def flush [Monad m] [MonadExceptOf String m] (ops : Components m) (session : Session) : m Session := do
  if session.mem.isEmpty then return session
  let tail := (← ops.scan).tail
  unless tail < UInt64.size do throw "absolute WAL position exhausted"
  let id ← ops.tables.create session.mem.toList
  let version : L0Manifest.Version := ⟨id :: session.version.tables, tail.toUInt64⟩
  ops.manifest.publish version
  return ⟨version, ∅⟩

def lookupTables [Monad m] (tables : Tables m) (key : UInt64) :
    List UInt64 → m (Option Mutation)
  | [] => pure none
  | id :: ids => do
    match ← tables.lookup id key with
    | some mutation => pure (some mutation)
    | none => lookupTables tables key ids

def get [Monad m] (ops : Components m) (session : Session) (key : UInt64) : m (Option UInt64) := do
  match session.mem[key]? with
  | some mutation => return mutation.value
  | none => return (← lookupTables ops.tables key session.version.tables).bind Mutation.value

end ExperimentalL0
