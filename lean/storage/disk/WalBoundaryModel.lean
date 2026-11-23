import WalBoundary
import DiskPublicationModel

namespace Alvoki.WAL.Boundary
open Storage Storage.Publication

private def marker (events : List WAL.Write) : ByteArray :=
  encode (WAL.encode events).size.toUInt64

/-- Before append sync succeeds, only the old marker is installed and the
physical append may be arbitrary. After that sync, marker publication may be
interrupted or retried with the complete appended frame already durable. -/
inductive WriteCut (before : List WAL.Write) (event : WAL.Write) : ByteArray → Image → Prop where
  | appending (tail : ByteArray) :
      WriteCut before event (WAL.encode before ++ tail) (.settled (some (marker before)))
  | publishing (path : Retry (fun _ next => next = marker (before ++ [event]))
        (.settled (some (marker before))) image) :
      WriteCut before event (WAL.encode (before ++ [event])) image

theorem commit_append_error (err : String) (publish : Except String Unit) :
    commit (.error err) publish = .error err := rfl

private theorem select_marker (events : List WAL.Write) (tail : ByteArray)
    (fits : (WAL.encode events).size < UInt64.size) :
    (do
      let size ← decode (marker events)
      select size (WAL.encode events ++ tail)) = .ok (WAL.encode events) := by
  rw [marker, decode_encode]
  exact select_encoded events tail fits

/-- The boundary bytes at a chosen visible or crash-surviving binding select
the exact encoding of the acknowledged history or that history plus the new event. -/
theorem write_cut_selects_old_or_new {before : List WAL.Write} {event : WAL.Write}
    {wal : ByteArray} {image : Image}
    (cut : WriteCut before event wal image)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size)
    {binding : Option ByteArray} (chosen : binding = image.active ∨ binding ∈ image.crashImages) :
    ∃ bytes events, binding = some bytes ∧ (events = before ∨ events = before ++ [event]) ∧
      (do
        let size ← decode bytes
        select size wal) = .ok (WAL.encode events) := by
  cases cut with
  | appending tail =>
    have old : binding = some (marker before) := by
      rcases chosen with visible | survives
      · exact visible
      · exact List.mem_singleton.mp survives
    exact ⟨marker before, before, old, Or.inl rfl, select_marker before tail oldFits⟩
  | publishing path =>
    let allowed := fun candidate => candidate = some (marker before) ∨
      candidate = some (marker (before ++ [event]))
    have valid : image.Valid allowed := retry_preserves
      (fun _ next _ written => Or.inr (congrArg some written))
      (Image.settled_valid (Or.inl rfl)) path
    have admissible : allowed binding := by
      rcases chosen with visible | survives
      · exact visible.symm ▸ valid.activeValid
      · exact valid.crashValid binding survives
    rcases admissible with old | new
    · refine ⟨marker before, before, old, Or.inl rfl, ?_⟩
      rw [WAL.encode_append]
      exact select_marker before (WAL.encode [event]) oldFits
    · refine ⟨marker (before ++ [event]), before ++ [event], new, Or.inr rfl, ?_⟩
      simpa only [ByteArray.append_empty] using
        select_marker (before ++ [event]) ByteArray.empty newFits

private theorem replay_selected (base : PackedTable) {bytes wal : ByteArray} {events : List WAL.Write}
    (selected : (do
      let size ← decode bytes
      select size wal) = .ok (WAL.encode events)) :
    (do
      let size ← decode bytes
      let selected ← select size wal
      recoverCheckpoint base selected) = recoverCheckpoint base (WAL.encode events) := by
  rw [← bind_assoc, selected]
  rfl

/-- Every modeled crash image selects either the already acknowledged prefix
or that prefix plus the complete new event, regardless of torn append length. -/
theorem write_cut_replays_old_or_new (base : PackedTable) {before : List WAL.Write} {event : WAL.Write}
    {wal : ByteArray} {image : Image}
    (cut : WriteCut before event wal image)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size)
    {onDisk : Option ByteArray} (survives : onDisk ∈ image.crashImages) :
    ∃ bytes, onDisk = some bytes ∧
      let recovered := do
        let size ← decode bytes
        let selected ← select size wal
        recoverCheckpoint base selected
      recovered = recoverCheckpoint base (WAL.encode before) ∨
        recovered = recoverCheckpoint base (WAL.encode (before ++ [event])) := by
  obtain ⟨bytes, events, binding, history, selected⟩ :=
    write_cut_selects_old_or_new cut oldFits newFits (Or.inr survives)
  refine ⟨bytes, binding, ?_⟩
  rcases history with rfl | rfl
  · exact Or.inl (replay_selected base selected)
  · exact Or.inr (replay_selected base selected)

/-- Once boundary publication returns success, a crash can only select the
synced, extended WAL, so every acknowledged append is part of replay. -/
theorem acknowledged_write_replays_new (base : PackedTable) (events : List WAL.Write)
    (fits : (WAL.encode events).size < UInt64.size) {initial published : Image}
    (done : (run (Image.perform (marker events))).run initial = some ((), published))
    {onDisk : Option ByteArray} (survives : onDisk ∈ published.crashImages) :
    ∃ bytes, onDisk = some bytes ∧ (do
      let size ← decode bytes
      let selected ← select size (WAL.encode events)
      recoverCheckpoint base selected) = recoverCheckpoint base (WAL.encode events) := by
  rw [run_model_success] at done
  cases done
  refine ⟨marker events, List.mem_singleton.mp survives, ?_⟩
  apply replay_selected base
  simpa only [ByteArray.append_empty] using select_marker events ByteArray.empty fits

end Alvoki.WAL.Boundary
