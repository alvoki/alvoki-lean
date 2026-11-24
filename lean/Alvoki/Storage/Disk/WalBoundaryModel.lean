import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Publication.DiskPublicationModel

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

private theorem fixed_marker_retry_shape {older newer : ByteArray} {image : Image}
    (path : Retry (fun _ bytes => bytes = newer) (.settled (some older)) image) :
    (image.active = some older ∧ ∀ binding ∈ image.crashImages, binding = some older) ∨
      (image.active = some newer ∧ ∀ binding ∈ image.crashImages,
        binding = some older ∨ binding = some newer) := by
  induction path with
  | refl => exact .inl ⟨rfl, fun _ survives => List.mem_singleton.mp survives⟩
  | attempt _ chosen cut ran prior =>
    cases chosen
    rcases cut with _ | _ | _ | _ | cut
    · cases ran; exact prior
    · cases ran; exact prior
    · cases ran; exact prior
    · cases ran
      refine .inr ⟨rfl, ?_⟩
      intro binding survives
      rcases List.mem_cons.mp survives with renamed | earlier
      · exact .inr renamed
      · rcases prior with ⟨_, oldOnly⟩ | ⟨_, oldOrNew⟩
        · exact .inl (oldOnly binding earlier)
        · exact oldOrNew binding earlier
    · simp [steps, Image.execute, Image.step] at ran
      cases ran
      exact .inr ⟨rfl, fun _ survives => .inr (List.mem_singleton.mp survives)⟩
  | crash _ survives prior =>
    rcases prior with ⟨_, oldOnly⟩ | ⟨_, oldOrNew⟩
    · cases oldOnly _ survives
      exact .inl ⟨rfl, fun _ survives => List.mem_singleton.mp survives⟩
    · rcases oldOrNew _ survives with rfl | rfl
      · exact .inl ⟨rfl, fun _ survives => List.mem_singleton.mp survives⟩
      · exact .inr ⟨rfl, fun _ survives => .inr (List.mem_singleton.mp survives)⟩

/-- At a modeled write cut, the visible marker is at least as long as every
crash-surviving marker. A crash resets the visible marker to its chosen image. -/
theorem write_cut_active_bounds_marker {before : List WAL.Write} {event : WAL.Write}
    {wal : ByteArray} {image : Image} (cut : WriteCut before event wal image)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size) :
    ∃ markerBytes length, image.active = some markerBytes ∧ decode markerBytes = .ok length ∧
      ∀ binding, (binding = image.active ∨ binding ∈ image.crashImages) →
        ∃ candidate count, binding = some candidate ∧ decode candidate = .ok count ∧
          count.toNat ≤ length.toNat := by
  let oldLength := (WAL.encode before).size.toUInt64
  let newLength := (WAL.encode (before ++ [event])).size.toUInt64
  have oldDecode : decode (marker before) = .ok oldLength := decode_encode _
  have newDecode : decode (marker (before ++ [event])) = .ok newLength := decode_encode _
  have bound : oldLength.toNat ≤ newLength.toNat := by
    dsimp [oldLength, newLength]
    rw [UInt64.toNat_ofNat_of_lt' oldFits, UInt64.toNat_ofNat_of_lt' newFits,
      WAL.encode_append, ByteArray.size_append]
    exact Nat.le_add_right _ _
  have onlyOld {snapshot : Image} (visible : snapshot.active = some (marker before))
      (crash : ∀ binding ∈ snapshot.crashImages, binding = some (marker before)) :
      ∀ binding, (binding = snapshot.active ∨ binding ∈ snapshot.crashImages) →
        ∃ candidate count, binding = some candidate ∧ decode candidate = .ok count ∧
          count.toNat ≤ oldLength.toNat := by
    intro binding chosen
    have raw := chosen.elim (·.trans visible) (crash binding)
    exact ⟨marker before, oldLength, raw, oldDecode, Nat.le_refl _⟩
  cases cut with
  | appending =>
    exact ⟨marker before, oldLength, rfl, oldDecode,
      onlyOld rfl (fun _ survives => List.mem_singleton.mp survives)⟩
  | publishing path =>
    rcases fixed_marker_retry_shape path with ⟨visible, crash⟩ | ⟨visible, crash⟩
    · exact ⟨marker before, oldLength, visible, oldDecode, onlyOld visible crash⟩
    · refine ⟨marker (before ++ [event]), newLength, visible, newDecode, ?_⟩
      intro binding chosen
      have allowed := chosen.elim (fun active => Or.inr (active.trans visible)) (crash binding)
      rcases allowed with old | new
      · exact ⟨marker before, oldLength, old, oldDecode, bound⟩
      · exact ⟨marker (before ++ [event]), newLength, new, newDecode, Nat.le_refl _⟩

/-- The boundary bytes at a chosen visible or crash-surviving binding select
the exact encoding of the acknowledged history or that history plus the new event. -/
theorem write_cut_selects_old_or_new {before : List WAL.Write} {event : WAL.Write}
    {wal : ByteArray} {image : Image}
    (cut : WriteCut before event wal image)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size)
    {binding : Option ByteArray} (chosen : binding = image.active ∨ binding ∈ image.crashImages) :
    ∃ bytes events, binding = some bytes ∧ bytes = encode (WAL.encode events).size.toUInt64 ∧
      (events = before ∨ events = before ++ [event]) ∧
      (do
        let size ← decode bytes
        select size wal) = .ok (WAL.encode events) := by
  cases cut with
  | appending tail =>
    have old : binding = some (marker before) := by
      rcases chosen with visible | survives
      · exact visible
      · exact List.mem_singleton.mp survives
    exact ⟨marker before, before, old, rfl, Or.inl rfl, select_marker before tail oldFits⟩
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
    · refine ⟨marker before, before, old, rfl, Or.inl rfl, ?_⟩
      rw [WAL.encode_append]
      exact select_marker before (WAL.encode [event]) oldFits
    · refine ⟨marker (before ++ [event]), before ++ [event], new, rfl, Or.inr rfl, ?_⟩
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
  obtain ⟨bytes, events, binding, _, history, selected⟩ :=
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
