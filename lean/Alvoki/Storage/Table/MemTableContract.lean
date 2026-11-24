import Alvoki.Storage.Table.SequentialModel

namespace Alvoki.Storage
open Alvoki.Sequential (History)
open Alvoki.Compaction.Model

namespace MemTableContract

/-- Clip the versions to a half-open key interval, including tombstones. -/
def clip (history : History UInt64) (start stop : UInt64) : History UInt64 :=
  ⟨history.rows.filter (fun row => start ≤ row.key && row.key < stop),
    history.ordered.filter _⟩

end MemTableContract

/-- A backend implements the same ordered version history. Lookup returns the
winning entry, so a tombstone can still mask an older packed run. -/
structure MemTableBackend (σ : Type) where
  history : σ → History UInt64
  empty : σ
  insert : σ → Entry (Option UInt64) → σ
  isEmpty : σ → Bool
  lookup : σ → UInt64 → UInt64 → Option (Entry (Option UInt64))
  range : σ → UInt64 → UInt64 → History UInt64
  history_empty : history empty = .empty
  history_insert (state row) : history (insert state row) = (history state).union (.singleton row)
  isEmpty_spec (state) : isEmpty state = (history state).rows.isEmpty
  lookup_spec (state key snapshot) : lookup state key snapshot = winner (history state).rows key snapshot
  range_spec (state start stop) : range state start stop = MemTableContract.clip (history state) start stop

def MemTableBackend.list : MemTableBackend (History UInt64) where
  history := id
  empty := .empty
  insert := fun history row => history.union (.singleton row)
  isEmpty := fun history => history.rows.isEmpty
  lookup := fun history => winner history.rows
  range := MemTableContract.clip
  history_empty := rfl
  history_insert := fun _ _ => rfl
  isEmpty_spec := fun _ => rfl
  lookup_spec := fun _ _ _ => rfl
  range_spec := fun _ _ _ => rfl

end Alvoki.Storage
