import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

/-- The observations of an immutable table with healthy reads, indexed by its
logical contents. A consumer can carry this relation alongside the handle. -/
structure Table.Represents [Monad m] [MonadExceptOf String m]
    (table : Table m) (rows : List Entry) : Prop where
  ordered : Ordered rows
  lookup : ∀ key, table.lookup key = pure (Contents.lookup rows key)
  seek : ∀ key, ∃ i, table.seek key = pure i ∧ Contents.IsSeek rows key i
  next : ∀ i, table.next i = pure (Contents.next rows i)

end ImmutableSSTable
