import Alvoki.Storage.Disk.WalSegmentCommitEffects
import Alvoki.Storage.Disk.WalSegmentRepairEffects

namespace Alvoki.Storage.WalSegmentRepair

open WAL.Boundary

private theorem oldHistory_fits (before : List WAL.Write) (event : WAL.Write)
    (fits : (WAL.encode (before ++ [event])).size < UInt64.size) :
    (WAL.encode before).size < UInt64.size := by
  apply Nat.lt_of_le_of_lt _ fits
  rw [WAL.encode_append, ByteArray.size_append]
  exact Nat.le_add_right _ _

private theorem appendedMarker_ne (before : List WAL.Write) (event : WAL.Write)
    (fits : (WAL.encode (before ++ [event])).size < UInt64.size) :
    WAL.Boundary.encode (WAL.encode before).size.toUInt64 ≠
      WAL.Boundary.encode (WAL.encode (before ++ [event])).size.toUInt64 := by
  intro same
  have lengths := congrArg WAL.Boundary.decode same
  rw [decode_encode, decode_encode] at lengths
  have sizes := congrArg UInt64.toNat (Except.ok.inj lengths)
  rw [UInt64.toNat_ofNat_of_lt' (oldHistory_fits before event fits), UInt64.toNat_ofNat_of_lt' fits] at sizes
  simp only [WAL.encode_size, List.length_append, List.length_singleton, WAL.frameSize] at sizes
  omega

private theorem Target.accepts_of_selected {target : Target} {count : UInt64} {bytes : ByteArray}
    (selected : selectRetained target.first count bytes = .ok target.trimmed) :
    target.Accepts (some bytes) := by
  by_cases beforeCutoff : count.toNat < target.first * WAL.frameSize
  · simp [selectRetained, beforeCutoff] at selected
  · have accepted : select (count.toNat - target.first * WAL.frameSize).toUInt64 bytes = .ok target.trimmed := by
      simpa only [selectRetained, beforeCutoff, ↓reduceIte] using selected
    obtain ⟨tail, exactBytes⟩ := select_prefix accepted
    exact ⟨tail, congrArg some exactBytes⟩

theorem _root_.Alvoki.Storage.DirectoryPublication.Bindings.walRange_of_counts
    {pair : DirectoryPublication.Bindings} {marker : ByteArray}
    {count : UInt64} {watermark through : Nat}
    (checkpoint : selectedCheckpointWatermark pair.manifest = some watermark)
    (visible : pair.walBoundary = some marker) (decoded : decode marker = .ok count)
    (size : count.toNat = through * WAL.frameSize) (covers : watermark ≤ through) :
    pair.walRange = some ⟨watermark, through⟩ := by
  simp only [DirectoryPublication.Bindings.walRange, checkpoint, visible, decoded, Except.toOption,
    Bind.bind, Option.bind]
  rw [size, Nat.mul_mod_left, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  simp only [covers, and_self, ite_true]

/-- One observed marker fixes the cutoff for every compatible keeper
candidate after an append report. The observed pair can be live or an
admitted crash choice. The caller supplies the projected keeper observations
and confirms durable absence of later files. Exact reads of preceding sealed
segments are checked separately. -/
theorem prepareAfterAppendCut {before : List WAL.Write} {first watermark : Nat}
    (starts : first ≤ before.length) (covered : watermark ≤ before.length)
    (event : WAL.Write) (fits : (WAL.encode (before ++ [event])).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark manifest = some watermark)
    (image : FileImage) {keeperBytes : ByteArray}
    (readKeeper : image.keeper.active = some keeperBytes)
    (keeperCrash : image.keeper.crashImages ≠ [])
    (noLater : image.later.DurablyEmpty) :
    let cut := (writeFilesAfter (runWriteEffects before event effects scratch)).reopenSegment first before manifest
    image.directory.active ∈ cut.directory.active :: cut.directory.crashImages →
    (∀ binding ∈ image.keeper.active :: image.keeper.crashImages,
      binding ∈ cut.wal.active :: cut.wal.crashImages) →
    ∃ history target,
      (history = before ∨ history = before ++ [event]) ∧
      target.pair = image.directory.active ∧ target.pair.manifest = manifest ∧
      target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      target.first = first ∧ target.range = ⟨watermark, history.length⟩ ∧
      target.trimmed = WAL.encode (history.drop first) ∧
      Prepared image target ⟨history.length, first, [], keeperBytes⟩ := by
  intro cut chosen observed
  have active := observed image.keeper.active (List.mem_cons_self ..)
  rw [readKeeper] at active
  obtain ⟨history, allowed, sameManifest, rawMarker, _⟩ :=
    WalSegmentCommit.selectSegment_atReportedCut starts event fits effects manifest scratch
      image.directory.active keeperBytes chosen active
  have lengthMonotone : before.length ≤ history.length := by
    rcases allowed with old | new
    · simp [old]
    · simp [new]
  have historyFits : (WAL.encode history).size < UInt64.size := by
    rcases allowed with old | new
    · simpa only [old] using oldHistory_fits before event fits
    · simpa only [new] using fits
  have count : (WAL.encode history).size.toUInt64.toNat = history.length * WAL.frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' historyFits, WAL.encode_size, Nat.mul_comm]
  have covers : watermark ≤ history.length := Nat.le_trans covered lengthMonotone
  have decoded : image.directory.active.walRange = some ⟨watermark, history.length⟩ := by
    exact DirectoryPublication.Bindings.walRange_of_counts
      (sameManifest ▸ checkpoint) rawMarker (decode_encode _) count covers
  let target : Target :=
    ⟨image.directory.active, ⟨watermark, history.length⟩, decoded, first, Nat.le_trans starts lengthMonotone,
      WAL.encode (history.drop first), by rw [WAL.encode_size, List.length_drop, Nat.mul_comm]⟩
  have sameHistory {other : List WAL.Write} (permitted : other = before ∨ other = before ++ [event])
      (same : image.directory.active.walBoundary =
        some (WAL.Boundary.encode (WAL.encode other).size.toUInt64)) : other = history := by
    have markers := Option.some.inj (same.symm.trans rawMarker)
    rcases permitted with oldOther | newOther <;> rcases allowed with old | new
    · exact oldOther.trans old.symm
    · rw [oldOther, new] at markers
      exact False.elim (appendedMarker_ne before event fits markers)
    · rw [newOther, old] at markers
      exact False.elim (appendedMarker_ne before event fits markers.symm)
    · exact newOther.trans new.symm
  have accepted (binding : Option ByteArray) (member : binding ∈ image.keeper.active :: image.keeper.crashImages) :
      target.Accepts binding := by
    have survived := observed binding member
    obtain ⟨tail, _, rfl⟩ := (writeFilesAfter (runWriteEffects before event effects scratch)).candidate_from_tail
      (before.drop first) manifest survived
    obtain ⟨other, allowedOther, _, markerOther, selected⟩ :=
      WalSegmentCommit.selectSegment_atReportedCut starts event fits effects manifest scratch
        image.directory.active _ chosen survived
    rw [sameHistory allowedOther markerOther] at selected
    exact Target.accepts_of_selected selected
  have later : image.later.Beyond target.range.through := by
    intro names appears
    rw [noLater.1, noLater.2] at appears
    obtain rfl : names = [] := by simpa using appears
    simp
  exact ⟨history, target, allowed, rfl, sameManifest, rawMarker, rfl, rfl, rfl,
    ⟨rfl, ⟨keeperCrash, accepted _ (List.mem_cons_self ..),
      fun binding h => accepted binding (List.mem_cons_of_mem _ h)⟩,
      later, rfl, rfl, noLater.1.symm, readKeeper⟩⟩

end Alvoki.Storage.WalSegmentRepair
