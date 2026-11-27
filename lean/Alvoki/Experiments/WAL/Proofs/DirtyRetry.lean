import Alvoki.Experiments.WAL.Contract
import Alvoki.Experiments.WAL.Proofs.ProcessExit
import Alvoki.Experiments.WAL.Proofs.Retry

namespace WalRecoverySlice.Persistence

open WalRecoverySlice.Contract (Permitted)

def pendingFrame (known : List Bytes) (pending : Option Bytes) : Bytes :=
  (pending.map (frame (1 + known.length))).getD []

def Image.MarkersSettled (image : Image) : Prop :=
  image.slot0.live = image.slot0.durable ∧ image.slot1.live = image.slot1.durable

/-- Raw contents of one observation of the files. Each observation uses
one complete marker pair. The log-only reader sees a prefix of the one
submitted frame following the canonical acknowledged bytes. -/
def ReplayView (policy : Policy) (known : List Bytes) (pending : Option Bytes) (image : Image) : Prop :=
  match policy with
  | .logOnly => ∃ count, image.data.live = encodeFrames 1 known ++ (pendingFrame known pending).take count
  | .boundary => ∃ selected, Permitted known pending selected ∧ BoundaryEntry image (historyCursor selected) ∧
      ∃ suffix, image.data.live = encodeFrames 1 selected ++ suffix

/-- A failed call can leave separate live and durable observations. Until
both marker slots agree across them, the common data bytes support both
selections and at most one slot differs. After the two marker barriers the
data repair may temporarily leave different live and durable tails. -/
structure Dirty (policy : Policy) (known : List Bytes) (pending : Option Bytes) (image : Image) : Prop where
  bounded : ∀ b ∈ known ++ pending.toList, b.length ≤ 32
  fits : (known ++ pending.toList).length ≤ 255
  live : ReplayView policy known pending image.liveSnapshot
  durable : ReplayView policy known pending image.powerLoss
  markers : policy = .boundary → image.MarkersSettled ∨
    image.data.live = image.data.durable ∧
      (image.slot0.live = image.slot0.durable ∨ image.slot1.live = image.slot1.durable)

theorem Dirty.powerLoss {policy known pending image} (dirty : Dirty policy known pending image) :
    Dirty policy known pending image.powerLoss :=
  ⟨dirty.bounded, dirty.fits, dirty.durable, dirty.durable, fun _ => .inl ⟨rfl, rfl⟩⟩

private theorem permitted_bounds {known : List Bytes} {pending : Option Bytes} {batches : List Bytes}
    (permitted : Permitted known pending batches)
    (bounded : ∀ b ∈ known ++ pending.toList, b.length ≤ 32)
    (fits : (known ++ pending.toList).length ≤ 255) :
    (∀ b ∈ batches, b.length ≤ 32) ∧ batches.length ≤ 255 := by
  rcases permitted with rfl | rfl
  · exact ⟨fun b mem => bounded b (List.mem_append_left _ mem), by simp at fits; omega⟩
  · exact ⟨bounded, fits⟩

private theorem allowed_data {known : List Bytes} {pending : Option Bytes} {batches : List Bytes}
    (permitted : Permitted known pending batches) :
    ∃ count, encodeFrames 1 batches = encodeFrames 1 known ++ (pendingFrame known pending).take count := by
  rcases permitted with rfl | rfl
  · exact ⟨0, by simp⟩
  · cases pending with
    | none => exact ⟨0, by simp⟩
    | some payload =>
      exact ⟨(pendingFrame known (some payload)).length, by
        simpa [pendingFrame] using encodeFrames_snoc 1 known payload⟩

private theorem Image.liveSnapshot_marker (image : Image) (slot : Nat) :
    (image.liveSnapshot.marker slot).durable = (image.marker slot).live := by
  by_cases zero : slot = 0 <;> simp [Image.liveSnapshot, FileImage.liveSnapshot, Image.marker, zero]

private theorem select_latest {image : Image} {slot : Nat} {selected : Marker} {other : Option Marker}
    (fits : slot < 2)
    (accepted : decodeMarker slot (image.marker slot).live = .ok (some selected))
    (alternate : decodeMarker (1 - slot) (image.marker (1 - slot)).live = .ok other)
    (newer : ∀ prior, other = some prior → prior.lastSeq < selected.lastSeq) :
    selectMarker image.slot0.live image.slot1.live = .ok selected := by
  have which : slot = 0 ∨ slot = 1 := by omega
  rcases which with rfl | rfl
  · cases other with
    | none => exact selectMarker_one (.inl ⟨accepted, alternate⟩)
    | some prior => simpa [newer prior rfl] using selectMarker_both accepted alternate
  · cases other with
    | none => exact selectMarker_one (.inr ⟨alternate, accepted⟩)
    | some prior =>
      simpa [Nat.not_lt_of_ge (Nat.le_of_lt (newer prior rfl))] using selectMarker_both alternate accepted

/-- A raw live view fixes the actual reader result and the canonical bytes
that would remain if this recovery reached its truncation. -/
private theorem Dirty.selects {policy known pending image} (dirty : Dirty policy known pending image) :
    ∃ (marker : Option Marker) (d : Decoded),
      ReopenSelection policy image marker d ∧
      Permitted known pending d.batches ∧
      d.cursor = historyCursor d.batches ∧
      image.data.live.take d.cursor.endPos = encodeFrames 1 d.batches ∧
      (policy = .boundary → BoundaryEntry image.liveSnapshot d.cursor) := by
  cases policy with
  | logOnly =>
    obtain ⟨count, physical⟩ := dirty.live
    change image.data.live = encodeFrames 1 known ++ (pendingFrame known pending).take count at physical
    have ⟨oldBounded, oldFits⟩ := permitted_bounds (batches := known) (.inl rfl) dirty.bounded dirty.fits
    have takeOld (tail : Bytes) : (encodeFrames 1 known ++ tail).take (historyCursor known).endPos =
        encodeFrames 1 known := by simp [historyCursor]
    cases pending with
    | none =>
      simp [pendingFrame] at physical
      refine ⟨none, ⟨known, historyCursor known⟩, ?_, .inl rfl, rfl, ?_, fun branch => by cases branch⟩
      · change scan image.data.live image.data.live.length .logOnly = _
        rw [physical]
        exact scan_encodeFrames .logOnly oldBounded oldFits
      · simpa only [physical, List.append_nil] using takeOld []
    | some payload =>
      change image.data.live = encodeFrames 1 known ++ (frame (1 + known.length) payload).take count at physical
      have fits : (known ++ [payload]).length ≤ 255 := dirty.fits
      have nextBounded := dirty.bounded payload (by simp)
      by_cases short : count < (frame (1 + known.length) payload).length
      · refine ⟨none, ⟨known, historyCursor known⟩, ?_, .inl rfl, rfl, ?_, fun branch => by cases branch⟩
        · change scan image.data.live image.data.live.length .logOnly = _
          rw [physical]
          exact scan_torn_encodeFrames payload count oldBounded (by simp at fits; omega) nextBounded short
        · simpa only [physical] using takeOld ((frame (1 + known.length) payload).take count)
      · rw [List.take_of_length_le (Nat.le_of_not_gt short), ← encodeFrames_snoc] at physical
        let kept := known ++ [payload]
        refine ⟨none, ⟨kept, historyCursor kept⟩, ?_, .inr rfl, rfl, ?_, fun branch => by cases branch⟩
        · change scan image.data.live image.data.live.length .logOnly = _
          rw [physical]
          exact scan_encodeFrames .logOnly dirty.bounded fits
        · simp [historyCursor, physical, kept]
  | boundary =>
    obtain ⟨selected, permitted, entry, suffix, physical⟩ := dirty.live
    have ⟨bounded, fits⟩ := permitted_bounds permitted dirty.bounded dirty.fits
    let count := selected.length
    let bytes := encodeFrames 1 selected
    let marker : Marker := ⟨bytes.length, count⟩
    let d : Decoded := ⟨selected, historyCursor selected⟩
    have active : (image.marker (count % 2)).live = encodeMarker bytes.length count := by
      simpa only [historyCursor, Nat.add_sub_cancel_left, Image.liveSnapshot_marker] using entry.selected
    have accepted : decodeMarker (count % 2) (image.marker (count % 2)).live = .ok (some marker) := by
      rw [active]
      have bound := encoded_history_size selected 1 bounded
      have extent : bytes.length < 65536 := by dsimp [bytes]; omega
      exact decodeMarker_encode _ _ (by omega) extent (by cases selected <;> simp [bytes, count, encodeFrames, frame_length])
    obtain ⟨other, read, older⟩ := entry.other
    simp only [historyCursor, Nat.add_sub_cancel_left, Image.liveSnapshot_marker] at read older
    have otherSlot : 1 - count % 2 = (1 + count) % 2 := by omega
    have picked := select_latest (Nat.mod_lt _ (by decide)) accepted (otherSlot ▸ read) older
    change image.data.live = bytes ++ suffix at physical
    have scanOK : scan image.data.live marker.endPos .boundary = .ok d := by
      rw [physical]
      exact scan_encodeFrames_append suffix .boundary bounded fits
    refine ⟨some marker, d, ⟨picked, scanOK, by simp [d, marker, count, historyCursor, Nat.add_comm]⟩,
      permitted, rfl, ?_, fun _ => entry⟩
    rw [physical]
    simp [d, historyCursor, bytes]

private def settleMarker (image : Image) (slot : Nat) : Image :=
  image.withMarker slot ⟨(image.marker slot).live, (image.marker slot).live⟩

private theorem FileImage.liveSnapshot_eq {file : FileImage} (stable : file.live = file.durable) :
    file.liveSnapshot = file := by
  cases file
  cases stable
  rfl

private theorem Image.settleMarker_live (image : Image) (slot : Nat) :
    (settleMarker image slot).liveSnapshot = image.liveSnapshot := by
  by_cases zero : slot = 0 <;> simp [settleMarker, Image.withMarker, Image.marker,
    Image.liveSnapshot, FileImage.liveSnapshot, zero]

private theorem Image.settleMarker_stillClean {image : Image} (stable : image.MarkersSettled) (slot : Nat) :
    (settleMarker image slot).MarkersSettled := by
  obtain ⟨zeroClean, oneClean⟩ := stable
  by_cases zero : slot = 0 <;> simp [settleMarker, Image.withMarker, Image.marker,
    Image.MarkersSettled, zero, zeroClean, oneClean]

/-- At most one marker may be dirty. Settling either slot preserves the old
durable observation or selects the whole previous live observation. -/
private theorem Dirty.afterSlot {known pending image} (dirty : Dirty .boundary known pending image)
    (slot : Nat) : Dirty .boundary known pending (settleMarker image slot) := by
  have live := dirty.live
  rw [← Image.settleMarker_live image slot] at live
  by_cases zero : slot = 0
  · subst slot
    by_cases clean : image.slot0.live = image.slot0.durable
    · have same : settleMarker image 0 = image := by
        have unchanged := FileImage.liveSnapshot_eq clean
        exact congrArg (fun slot0 => {image with slot0}) unchanged
      exact same.symm ▸ dirty
    · have shared : image.data.live = image.data.durable ∧ image.slot1.live = image.slot1.durable := by
        rcases dirty.markers rfl with ⟨impossible, _⟩ | ⟨data, impossible | one⟩
        · exact (clean impossible).elim
        · exact (clean impossible).elim
        · exact ⟨data, one⟩
      have whole : (settleMarker image 0).powerLoss = image.liveSnapshot := by
        simp [settleMarker, Image.withMarker, Image.marker, Image.liveSnapshot, Image.powerLoss,
          FileImage.liveSnapshot, FileImage.powerLoss, shared.1, shared.2]
      exact ⟨dirty.bounded, dirty.fits, live, whole.symm ▸ dirty.live, fun _ => .inl ⟨rfl, shared.2⟩⟩
  · by_cases clean : image.slot1.live = image.slot1.durable
    · have same : settleMarker image slot = image := by
        simpa only [settleMarker, Image.withMarker, Image.marker, FileImage.liveSnapshot, ite_eq_right zero] using
          congrArg (fun slot1 => {image with slot1}) (FileImage.liveSnapshot_eq clean)
      exact same.symm ▸ dirty
    · have shared : image.data.live = image.data.durable ∧ image.slot0.live = image.slot0.durable := by
        rcases dirty.markers rfl with ⟨_, impossible⟩ | ⟨data, other | impossible⟩
        · exact (clean impossible).elim
        · exact ⟨data, other⟩
        · exact (clean impossible).elim
      have whole : (settleMarker image slot).powerLoss = image.liveSnapshot := by
        simp [settleMarker, Image.withMarker, Image.marker, Image.liveSnapshot, Image.powerLoss,
          FileImage.liveSnapshot, FileImage.powerLoss, zero, shared.1, shared.2]
      refine ⟨dirty.bounded, dirty.fits, live, whole.symm ▸ dirty.live, fun _ => .inl ?_⟩
      simpa [settleMarker, Image.withMarker, Image.marker, Image.MarkersSettled, zero] using shared.2

private theorem Image.bothSynced_clean (image : Image) (marker : Marker) :
    (image.bothSynced (some marker)).MarkersSettled := by
  let slot := marker.lastSeq % 2
  change (settleMarker (settleMarker image slot) (1 - slot)).MarkersSettled
  have range : slot < 2 := Nat.mod_lt _ (by decide)
  have which : slot = 0 ∨ slot = 1 := by omega
  rcases which with h | h <;>
    simp [settleMarker, Image.withMarker, Image.marker, Image.MarkersSettled, h]

private theorem Dirty.afterMarkers {policy known pending image marker d}
    (dirty : Dirty policy known pending image) (selects : ReopenSelection policy image marker d) :
    Dirty policy known pending (image.selectedSync marker) ∧
    Dirty policy known pending (image.bothSynced marker) ∧
    (image.bothSynced marker).liveSnapshot = image.liveSnapshot ∧
    (image.MarkersSettled → (image.selectedSync marker).MarkersSettled) ∧
    (policy = .boundary ∨ image.MarkersSettled → (image.bothSynced marker).MarkersSettled) := by
  cases policy <;> cases marker <;> try contradiction
  · exact ⟨dirty, dirty, rfl, id, fun h => h.resolve_left (by intro impossible; cases impossible)⟩
  · rename_i m
    let slot := m.lastSeq % 2
    have first := dirty.afterSlot slot
    have second := first.afterSlot (1 - slot)
    exact ⟨first, second, (Image.settleMarker_live _ _).trans (Image.settleMarker_live _ _),
      fun clean => Image.settleMarker_stillClean clean slot, fun _ => image.bothSynced_clean m⟩

theorem BoundaryEntry.sameSlots {source target : Image} {cursor : Cursor}
    (entry : BoundaryEntry source cursor) (frameSlots : ∀ slot, (target.marker slot).durable = (source.marker slot).durable) :
    BoundaryEntry target cursor := by
  constructor
  · rw [frameSlots]
    exact entry.selected
  · rw [frameSlots]
    exact entry.other

private theorem FileImage.powerLoss_eq {file : FileImage} (stable : file.live = file.durable) :
    file.powerLoss = file := by
  cases file
  cases stable
  rfl

theorem Image.stableDataAndMarkers {image : Image}
    (data : image.data.live = image.data.durable) (markers : image.MarkersSettled) : image.powerLoss = image := by
  unfold Image.powerLoss
  rw [FileImage.powerLoss_eq data, FileImage.powerLoss_eq markers.1, FileImage.powerLoss_eq markers.2]

private theorem Image.liveSnapshot_eq {image : Image}
    (data : image.data.live = image.data.durable) (markers : image.MarkersSettled) : image.liveSnapshot = image := by
  unfold Image.liveSnapshot
  rw [FileImage.liveSnapshot_eq data, FileImage.liveSnapshot_eq markers.1, FileImage.liveSnapshot_eq markers.2]

private theorem Dirty.finish {policy known pending image d}
    (dirty : Dirty policy known pending image)
    (allowed : Permitted known pending d.batches)
    (cursor : d.cursor = historyCursor d.batches)
    (bytes : image.data.live.take d.cursor.endPos = encodeFrames 1 d.batches)
    (selected : policy = .boundary → BoundaryEntry image.liveSnapshot d.cursor)
    (settled : policy = .boundary → image.MarkersSettled) :
    let cropped := image.trimmed d
    let synced := cropped.dataSettled
    Dirty policy known pending cropped ∧ Dirty policy known pending synced ∧ Ready policy synced d.batches ∧
      (image.MarkersSettled → synced.powerLoss = synced) := by
  intro cropped synced
  have sameLive : synced.liveSnapshot = cropped.liveSnapshot := rfl
  have sameDisk : cropped.powerLoss = image.powerLoss := rfl
  have afterCropped : ReplayView policy known pending cropped.liveSnapshot := by
    cases policy with
    | logOnly =>
      obtain ⟨count, encoded⟩ := allowed_data allowed
      exact ⟨count, bytes.trans encoded⟩
    | boundary =>
      have original := selected rfl
      rw [cursor] at original
      refine ⟨d.batches, allowed, original.sameSlots ?_, [], ?_⟩
      · intro slot
        by_cases zero : slot = 0 <;> simp [Image.marker, zero, cropped, Image.trimmed, Image.liveSnapshot]
      · exact bytes.trans (List.append_nil _).symm
  have afterSynced : ReplayView policy known pending synced.powerLoss := by
    cases policy with
    | logOnly =>
      obtain ⟨count, encoded⟩ := allowed_data allowed
      exact ⟨count, bytes.trans encoded⟩
    | boundary =>
      have clean : synced.powerLoss = synced := Image.stableDataAndMarkers rfl (settled rfl)
      have same : synced.liveSnapshot = synced := Image.liveSnapshot_eq rfl (settled rfl)
      rw [clean, ← same, sameLive]
      exact afterCropped
  refine ⟨⟨dirty.bounded, dirty.fits, afterCropped, sameDisk.symm ▸ dirty.durable, fun branch => .inl (settled branch)⟩,
    ⟨dirty.bounded, dirty.fits, sameLive.symm ▸ afterCropped, afterSynced, fun branch => .inl (settled branch)⟩,
    ⟨?_, ?_⟩, fun clean => Image.stableDataAndMarkers rfl clean⟩
  · refine ⟨?_, rfl⟩
    change FileImage.mk (image.data.live.take d.cursor.endPos) (image.data.live.take d.cursor.endPos) = _
    rw [bytes]
  · intro branch
    have original := selected branch
    rw [cursor] at original
    apply original.sameSlots
    intro slot
    have clean := settled branch
    by_cases zero : slot = 0
    · simpa [Image.marker, zero, synced, cropped, Image.trimmed, Image.dataSettled,
        Image.liveSnapshot, FileImage.liveSnapshot] using clean.1.symm
    · simpa [Image.marker, zero, synced, cropped, Image.trimmed, Image.dataSettled,
        Image.liveSnapshot, FileImage.liveSnapshot] using clean.2.symm

/-- Every actual recovery attempt, even if it errors after changing files or
is interrupted, leaves another admitted live/durable image for the same
client submissions. Successful recovery also installs the selected history
and the physical entry for the next append. -/
theorem Dirty.reopen {policy known pending image} (dirty : Dirty policy known pending image) (effects : Effects) :
    let result := (WalRecoverySlice.reopen (ops effects) policy).run image
    Dirty policy known pending (reached result) ∧
    (image.MarkersSettled → (reached result).MarkersSettled) ∧
    ∀ decoded, acknowledged result = some decoded →
      Permitted known pending decoded.batches ∧
      decoded.cursor = historyCursor decoded.batches ∧
      Ready policy (reached result) decoded.batches ∧
      (∀ b ∈ decoded.batches, b.length ≤ 32) ∧ decoded.batches.length ≤ 255 ∧
      (policy = .boundary ∨ image.MarkersSettled → (reached result).powerLoss = reached result) := by
  intro result
  obtain ⟨marker, decoded, selected, allowed, cursor, captured, selection⟩ := dirty.selects
  obtain ⟨first, both, liveSame, firstClean, bothClean⟩ := dirty.afterMarkers selected
  have dataSame : (image.bothSynced marker).data.live = image.data.live :=
    congrArg (fun snapshot => snapshot.data.live) liveSame
  have bytes : (image.bothSynced marker).data.live.take decoded.cursor.endPos =
      encodeFrames 1 decoded.batches := by rw [dataSame, captured]
  have markerAgrees (branch : policy = .boundary) :
      BoundaryEntry (image.bothSynced marker).liveSnapshot decoded.cursor :=
    liveSame.symm ▸ selection branch
  obtain ⟨trim, finish, ready, fixed⟩ := both.finish allowed cursor bytes markerAgrees
    (fun branch => bothClean (.inl branch))
  obtain ⟨cuts, exactReturn⟩ := reopen_cuts effects selected
  have preserved : Dirty policy known pending (reached result) ∧
      (image.MarkersSettled → (reached result).MarkersSettled) := by
    change Dirty policy known pending (reached ((WalRecoverySlice.reopen (ops effects) policy).run image)) ∧ _
    rcases cuts with atRead | atFirst | atBoth | atTrim | atFinish
    · rw [atRead]
      exact ⟨dirty, id⟩
    · rw [atFirst]
      exact ⟨first, firstClean⟩
    · rw [atBoth]
      exact ⟨both, fun clean => bothClean (.inr clean)⟩
    · rw [atTrim]
      exact ⟨trim, fun clean => bothClean (.inr clean)⟩
    · rw [atFinish]
      exact ⟨finish, fun clean => bothClean (.inr clean)⟩
  refine ⟨preserved.1, preserved.2, ?_⟩
  intro returned success
  obtain ⟨rfl, complete⟩ := exactReturn returned success
  rw [complete]
  have ⟨bound, fit⟩ := permitted_bounds allowed dirty.bounded dirty.fits
  exact ⟨allowed, cursor, ready, bound, fit, fun stable => fixed (bothClean stable)⟩

/-- When the primitive operations are available, the actual open succeeds
from any admitted live view. -/
theorem Dirty.healthy_reopen {policy known pending image} (dirty : Dirty policy known pending image) :
    ∃ decoded after, (WalRecoverySlice.reopen (ops healthyReopen) policy).run image = .ok (.ok decoded) after := by
  obtain ⟨marker, decoded, selected, _, _, _, _⟩ := dirty.selects
  exact ⟨decoded, ((image.bothSynced marker).trimmed decoded).dataSettled, reopen_selected_healthy selected⟩

end WalRecoverySlice.Persistence
