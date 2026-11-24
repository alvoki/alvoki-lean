import Alvoki.Storage.Table.MemTableTree

namespace Alvoki.Storage
open Alvoki.Sequential (History)
open Alvoki.Compaction.Model

/-- The mutable part of the LSM. The history is the common specification
used by the packed table and its persistent recovery proofs. -/
inductive MemTable where
  | list (state : History UInt64)
  | tree (state : MemTableTree)

namespace MemTable

inductive Kind where
  | list
  | tree

@[inline] def emptyWith : Kind → MemTable
  | .list => .list MemTableBackend.list.empty
  | .tree => .tree MemTableTree.backend.empty

@[inline] def empty : MemTable := emptyWith .tree

@[inline] def clear : MemTable → MemTable
  | .list _ => .list MemTableBackend.list.empty
  | .tree _ => .tree MemTableTree.backend.empty

@[inline] def history : MemTable → History UInt64
  | .list state => MemTableBackend.list.history state
  | .tree state => MemTableTree.backend.history state

@[inline] def insert (state : MemTable) (row : Entry (Option UInt64)) : MemTable :=
  match state with
  | .list state => .list (MemTableBackend.list.insert state row)
  | .tree state => .tree (MemTableTree.backend.insert state row)

@[inline] def isEmpty : MemTable → Bool
  | .list state => MemTableBackend.list.isEmpty state
  | .tree state => MemTableTree.backend.isEmpty state

@[inline] def lookup (state : @& MemTable) (key snapshot : UInt64) : Option (Entry (Option UInt64)) :=
  match state with
  | .list state => MemTableBackend.list.lookup state key snapshot
  | .tree state => MemTableTree.backend.lookup state key snapshot

@[inline] def range (state : @& MemTable) (start stop : UInt64) : History UInt64 :=
  match state with
  | .list state => MemTableBackend.list.range state start stop
  | .tree state => MemTableTree.backend.range state start stop

@[simp] theorem history_emptyWith (kind : Kind) : (emptyWith kind).history = .empty := by
  cases kind
  · exact MemTableBackend.list.history_empty
  · exact MemTableTree.backend.history_empty

@[simp] theorem history_empty : empty.history = .empty := history_emptyWith .tree

@[simp] theorem history_clear (state : MemTable) : state.clear.history = .empty := by
  cases state
  · exact MemTableBackend.list.history_empty
  · exact MemTableTree.backend.history_empty

theorem history_insert (state : MemTable) (row : Entry (Option UInt64)) :
    (state.insert row).history = state.history.union (.singleton row) := by
  cases state
  · exact MemTableBackend.list.history_insert _ _
  · exact MemTableTree.backend.history_insert _ _

theorem isEmpty_spec (state : MemTable) : state.isEmpty = state.history.rows.isEmpty := by
  cases state
  · exact MemTableBackend.list.isEmpty_spec _
  · exact MemTableTree.backend.isEmpty_spec _

theorem lookup_spec (state : MemTable) (key snapshot : UInt64) :
    state.lookup key snapshot = winner state.history.rows key snapshot := by
  cases state
  · exact MemTableBackend.list.lookup_spec _ _ _
  · exact MemTableTree.backend.lookup_spec _ _ _

theorem range_spec (state : MemTable) (start stop : UInt64) :
    state.range start stop = MemTableContract.clip state.history start stop := by
  cases state
  · exact MemTableBackend.list.range_spec _ _ _
  · exact MemTableTree.backend.range_spec _ _ _

end MemTable
end Alvoki.Storage
