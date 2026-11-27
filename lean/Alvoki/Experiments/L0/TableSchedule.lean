import Alvoki.Experiments.L0.Codecs
import Alvoki.Experiments.SSTable.Native

namespace ExperimentalL0
open System

def tablePath (dir : FilePath) (id : UInt64) : FilePath := dir / s!"table-{id.toNat}"

/-- Open and use the table on the source supplied by the adapter. In the
native adapter, that source retains the read descriptor for this call. -/
def withTableSource [Monad m] [MonadExceptOf String m]
    (source : ImmutableSSTable.Source m)
    (use : ImmutableSSTable.TypedTable m UInt64 Mutation → m α) : m α := do
  let table ← ImmutableSSTable.openTable source
  use ⟨table, keyCodec, mutationCodec⟩

/-- Validate the result of no-follow stat before entering the read scope. -/
def isTableFile (metadata : IO.FS.Metadata) : Bool :=
  metadata.type == .file && metadata.numLinks == 1

def withTableDescriptor [Monad m] [MonadExceptOf String m]
    (stat : m IO.FS.Metadata) (withRead : (handle → m α) → m α)
    (use : handle → m α) : m α := do
  let metadata ← stat
  if isTableFile metadata then withRead use
  else throw "expected a singly linked regular SSTable"

/-- Both syscalls use the name derived from the same requested ID. -/
def withTableAt [Monad m] [MonadExceptOf String m]
    (stat : FilePath → m IO.FS.Metadata) (withRead : FilePath → (handle → m α) → m α)
    (dir : FilePath) (id : UInt64) (use : handle → m α) : m α :=
  let path := tablePath dir id
  withTableDescriptor (stat path) (withRead path) use

/-- Lift the shared typed operation without exporting the descriptor. Native
callers restrict its result to a mutation observation or unit. -/
def nativeTableAction (handle : IO.FS.Handle)
    (use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α) :
    ExceptT String IO α :=
  ExceptT.mk (liftM (withTableSource (ImmutableSSTable.handleSource handle) use).toBaseIO)

end ExperimentalL0
