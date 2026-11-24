import Alvoki.Storage.Disk.Recovery

namespace Alvoki.Storage

open Alvoki.WAL

private def prepareBatchLoop (state : PackedTable) (reversed : List Write) :
    List (UInt64 × Option UInt64) → Option (List Write × PackedTable)
  | [] => some (reversed.reverse, state)
  | (key, value) :: rest => do
    let (event, next) ← prepareWrite state key value
    prepareBatchLoop next (event :: reversed) rest

/-- Prepare the entire batch before mutating disk or publishing its table. -/
def prepareBatch (state : PackedTable) (rows : List (UInt64 × Option UInt64)) :
    Option (List Write × PackedTable) :=
  prepareBatchLoop state [] rows

private theorem prepareBatchLoop_spec (state : PackedTable) (reversed : List Write)
    (rows : List (UInt64 × Option UInt64)) {events : List Write} {next : PackedTable}
    (prepared : prepareBatchLoop state reversed rows = some (events, next)) :
    ∃ suffix, events = reversed.reverse ++ suffix ∧ suffix.length = rows.length ∧
      replay state suffix = .ok next ∧
      suffix.map (fun event => (event.key, event.value)) = rows ∧
      OrdinalsFrom (state.committed.toNat + 1) suffix := by
  induction rows generalizing state reversed with
  | nil =>
    cases prepared
    exact ⟨[], by simp, rfl, rfl, rfl, trivial⟩
  | cons row rest ih =>
    obtain ⟨key, value⟩ := row
    cases step : prepareWrite state key value with
    | none => simp [prepareBatchLoop, step] at prepared
    | some pair =>
      obtain ⟨event, intermediate⟩ := pair
      have restPrepared : prepareBatchLoop intermediate (event :: reversed) rest = some (events, next) := by
        simpa [prepareBatchLoop, step] using prepared
      obtain ⟨suffix, bytes, length, replayed, keys, ordered⟩ :=
        ih intermediate (event :: reversed) restPrepared
      have stepFacts : (event.key, event.value) = (key, value) ∧
          event.sequence = intermediate.committed ∧
          intermediate.committed.toNat = state.committed.toNat + 1 := by
        unfold prepareWrite at step
        obtain ⟨_, written, equal⟩ := Option.map_eq_some_iff.mp step
        cases equal
        exact ⟨rfl, rfl, (PackedTable.write_spec written).1⟩
      obtain ⟨payload, sequence, clock⟩ := stepFacts
      refine ⟨event :: suffix, ?_, by simp [length], ?_, by simp [payload, keys], ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using bytes
      · unfold replay at *
        rw [List.foldlM_cons, replay_prepared step]
        exact replayed
      · exact ⟨by rw [sequence, clock], by simpa only [clock] using ordered⟩

theorem prepareBatch_spec {state next : PackedTable} {rows : List (UInt64 × Option UInt64)}
    {events : List Write} (prepared : prepareBatch state rows = some (events, next)) :
    events.length = rows.length ∧ replay state events = .ok next ∧
      events.map (fun event => (event.key, event.value)) = rows ∧
      OrdinalsFrom (state.committed.toNat + 1) events := by
  obtain ⟨suffix, bytes, length, replayed, keys, ordered⟩ := prepareBatchLoop_spec state [] rows prepared
  simp at bytes
  subst events
  exact ⟨length, replayed, keys, ordered⟩

end Alvoki.Storage

namespace Alvoki.WAL

/-- Accumulate frames from left to right so existing bytes need not be prepended again. -/
def encodeBatch (events : List Write) : ByteArray :=
  events.foldl (fun bytes event => bytes ++ encodeFrame event) ByteArray.empty

private theorem encodeBatch_fold (events : List Write) (prefixBytes : ByteArray) :
    events.foldl (fun bytes event => bytes ++ encodeFrame event) prefixBytes =
      prefixBytes ++ encode events := by
  induction events generalizing prefixBytes with
  | nil => simp [encode]
  | cons event rest ih => simp [List.foldl_cons, ih, encode, ByteArray.append_assoc]

theorem encodeBatch_eq (events : List Write) : encodeBatch events = encode events := by
  simp [encodeBatch, encodeBatch_fold]

end Alvoki.WAL


namespace Alvoki.Storage

/-- The batch marker counts precisely the old encoded history and all of the
prepared batch frames. The new table follows the same logical writes as replay. -/
theorem prepareBatch_extends_history {state next : PackedTable}
    {rows : List (UInt64 × Option UInt64)} {history events : List WAL.Write}
    (ordered : WAL.OrdinalsFrom 1 history) (count : history.length = state.committed.toNat)
    (prepared : prepareBatch state rows = some (events, next)) :
    next.committed.toNat = history.length + rows.length ∧
      WAL.OrdinalsFrom 1 (history ++ events) ∧
      WAL.encode (history ++ events) = WAL.encode history ++ WAL.encodeBatch events ∧
      (WAL.encode (history ++ events)).size =
        (WAL.encode history).size + WAL.frameSize * rows.length := by
  obtain ⟨length, replayed, _, ordinals⟩ := prepareBatch_spec prepared
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [replay_committed_count events replayed, count, length]
  · apply (ordinals_append_iff 1 history events).mpr
    exact ⟨ordered, by simpa only [count, Nat.add_comm 1] using ordinals⟩
  · rw [WAL.encode_append, WAL.encodeBatch_eq]
  · simp [List.length_append, Nat.mul_add, length]

theorem prepareBatch_refines {state next : PackedTable} {model : Sequential.SnapshotTable UInt64}
    {rows : List (UInt64 × Option UInt64)} {events : List WAL.Write}
    (refines : state.Refines model) (prepared : prepareBatch state rows = some (events, next)) :
    ∃ after, SnapshotWalReplay model events after ∧ next.Refines after :=
  replay_refines refines (prepareBatch_spec prepared).2.1

end Alvoki.Storage
