import Alvoki.Storage.Disk.VersionedCheckpointRetry
import Alvoki.Storage.Disk.WalSegmentReadPlan

namespace Alvoki.Storage.CheckpointPublication

open Manifest
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- A checkpoint cut changes the manifest and run namespace. Reuse its
directory projection with the same settled marker and untouched segments. -/
def Image.segmentedCheckpointView (published : Image) (before : WalSegmentImage) : WalSegmentImage :=
  { before with directory :=
      (published.markedReopenImage ⟨before.directory, .settled (some before.active.bytes)⟩).directory }

private theorem Image.segmentedCheckpointView_pair {published : Image} {before : WalSegmentImage}
    {pair : DirectoryPublication.Bindings} (chosen : (published.segmentedCheckpointView before).Selects pair) :
    pair.walBoundary = before.directory.active.walBoundary ∧
      (published.manifest.active = pair.manifest ∨ pair.manifest ∈ published.manifest.crashImages) := by
  rcases List.mem_cons.mp chosen with rfl | survives
  · exact ⟨rfl, .inl rfl⟩
  · obtain ⟨candidate, member, rfl⟩ := List.mem_map.mp survives
    exact ⟨rfl, .inr member⟩

private theorem walRange_of_reports {pair : DirectoryPublication.Bindings} {marker : ByteArray}
    {count : UInt64} {watermark through : Nat}
    (checkpoint : selectedCheckpointWatermark pair.manifest = some watermark)
    (visible : pair.walBoundary = some marker) (decoded : WAL.Boundary.decode marker = .ok count)
    (size : count.toNat = through * frameSize) (covered : watermark ≤ through) :
    pair.walRange = some ⟨watermark, through⟩ := by
  simp only [DirectoryPublication.Bindings.walRange, checkpoint, visible, decoded, Except.toOption,
    Bind.bind, Option.bind]
  rw [size, Nat.mul_mod_left, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  simp only [covered, and_self, ite_true]

/-- The exact strict-v2 plan prepared by the writer produces this cut from
the reported checkpoint schedule. Every selectable manifest remains tied
to the same marker and immutable segment layout. Its exact durable run
bytes describe the covered history, and its watermark determines the
canonical WAL read suffix. This case retains the full chain from zero. -/
theorem segmentedCheckpoint_reportedCut
    {before : WalSegmentImage} {initial published : Image} {history : List WAL.Write}
    (layout : before.ReadLayout history) (chain : WalSegment.Chain history 0 before.segments)
    (settled : before.directory.crashImages = [before.directory.active])
    (marker : before.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (walFits : (WAL.encode history).size < UInt64.size)
    (projected : initial.manifest = before.directory.project .manifest)
    (previous : initial.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.directory.active.manifest)
    (strict : ∀ bytes, before.directory.active.manifest = some bytes →
      ∃ manifest, IntegrityCheckpoint.decode bytes = .ok manifest)
    {writer checkpoint : PackedTable} {model : Sequential.SnapshotTable UInt64}
    (refines : writer.Refines model) (represents : RepresentsWalHistory history model)
    (rowBounds : writer.RowBounds) (flushed : (flushForCheckpoint writer id : Except String PackedTable) = .ok checkpoint)
    (runCountFits : checkpoint.runs.length < UInt64.size) (generation : UInt64)
    (fresh : initial.UnreachableVersioned generation)
    (runBytesFit : ∀ bytes ∈ checkpoint.runs.map (·.run.bytes), bytes.size < UInt64.size)
    (report : Step → StepReport) :
    let next := VersionedRunSet.integrity ⟨checkpointHeader checkpoint generation, checkpoint.runs.map (·.run.bytes)⟩
    initial.runVersionedWithReports next report = some (.error () published) →
    let after := published.segmentedCheckpointView before
    after.ReadLayout history ∧ after.Valid history ∧
      ∀ pair, after.Selects pair →
        pair.walBoundary = before.directory.active.walBoundary ∧
        (pair.manifest = before.directory.active.manifest ∨ pair.manifest = some next.manifest.encode) ∧
        published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest ∧
        (∀ bytes, pair.manifest = some bytes → ∃ manifest files,
          IntegrityCheckpoint.decode bytes = .ok manifest ∧
          (List.range manifest.header.runCount.toNat).mapM (published.durable manifest.header.generation) = some files ∧
          manifest.validateRuns files = true) ∧
        ∃ range first, pair.walRange = some range ∧ range.through = history.length ∧
          (pair.manifest = some next.manifest.encode → range.watermark = history.length) ∧
          first ≤ range.watermark ∧
          selectWalSegmentReads (after.segments.map (·.first)) range.watermark =
            some (first, (after.readDescriptors range.watermark).map (·.first)) ∧
          WalSegment.Chain history first (after.readDescriptors range.watermark) := by
  intro next reported after
  have original : initial.manifest.active = before.directory.active.manifest := by
    rw [projected]
    rfl
  have originalCrashes : initial.manifest.crashImages = [initial.manifest.active] := by
    simp [projected, settled, DirectoryPublication.Image.project]
  have initialValid : initial.ValidVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) := by
    refine ⟨by simp [originalCrashes], original.symm ▸ previous, ?_⟩
    intro candidate survives
    rw [originalCrashes] at survives
    exact ((List.mem_singleton.mp survives).trans original).symm ▸ previous
  obtain ⟨preparedModel, written, refined, historyPrefix⟩ := WrittenCheckpoint.of_flushForCheckpoint_history
    flushed refines represents rowBounds runCountFits generation
  have watermark : checkpoint.committed.toNat = history.length := by
    have stable := (WrittenCheckpoint.of_flushForCheckpoint flushed refines runCountFits
      rowBounds.runs rowBounds.memory generation).2.1
    rw [stable, refines.committed, represents.committed_count]
  let metadata := IntegrityCheckpoint.fromRuns (checkpointHeader checkpoint generation) (checkpoint.runs.map (·.run.bytes))
  have fileCount : next.files.length = metadata.header.runCount.toNat := by
    change (checkpoint.runs.map (·.run.bytes)).length = (checkpointHeader checkpoint generation).runCount.toNat
    rw [List.length_map, written.count]
  have metadataCount : metadata.runs.length = metadata.header.runCount.toNat := by
    simpa [metadata, IntegrityCheckpoint.fromRuns] using written.count
  have decoded : IntegrityCheckpoint.decode metadata.encode = .ok metadata :=
    IntegrityCheckpoint.decode_encode metadata written.validFloor metadataCount
  have checked := IntegrityCheckpoint.validateRuns_fromRuns metadata.header next.files fileCount runBytesFit
  have count : metadata.header.committed.toNat = history.length := written.watermark ▸ watermark
  have countFits : history.length < UInt64.size := by
    have bound := walFits
    rw [WAL.encode_size] at bound
    simp only [WAL.frameSize] at bound
    omega
  have covered : next.manifest.header.committed ≤ history.length.toUInt64 := by
    change metadata.header.committed ≤ history.length.toUInt64
    apply UInt64.le_iff_toNat_le.mpr
    rw [count, UInt64.toNat_ofNat_of_lt' countFits]
    exact Nat.le_refl _
  have route := VersionedRetry.reported (expected := CheckpointRepresentsPrefix history) (.refl initial)
    next fresh (VersionedCheckpoint.decode_integrity decoded) fileCount.symm checked covered
    ⟨checkpoint, preparedModel, written, refined, historyPrefix⟩ report reported
  obtain ⟨cut, executed⟩ := initial.runVersionedWithReports_outcome next report reported
  let allowed := fun binding => binding = before.directory.active.manifest ∨ binding = some next.manifest.encode
  have initialChoice : initial.manifest.Valid allowed := by
    refine ⟨initialValid.hasCrashImage, .inl original, ?_⟩
    intro candidate survives
    rw [originalCrashes] at survives
    exact .inl ((List.mem_singleton.mp survives).trans original)
  have choices := Image.executeVersioned_manifest_valid initialChoice (.inr rfl) cut executed
  have markerSize : (WAL.encode history).size.toUInt64.toNat = history.length * frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' walFits, WAL.encode_size, Nat.mul_comm]
  have readInputs (pair : DirectoryPublication.Bindings) (chosen : after.Selects pair) :
      pair.walBoundary = before.directory.active.walBoundary ∧ allowed pair.manifest ∧
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest ∧
      (∀ bytes, pair.manifest = some bytes → ∃ manifest files,
        IntegrityCheckpoint.decode bytes = .ok manifest ∧
        (List.range manifest.header.runCount.toNat).mapM (published.durable manifest.header.generation) = some files ∧
        manifest.validateRuns files = true) ∧
      ∃ range, pair.walRange = some range ∧ range.through = history.length ∧
        (pair.manifest = some next.manifest.encode → range.watermark = history.length) := by
    obtain ⟨sameMarker, binding⟩ := Image.segmentedCheckpointView_pair chosen
    have exactMarker := sameMarker.trans marker
    have allowedBinding : allowed pair.manifest := by
      rcases binding with active | survives
      · exact active ▸ choices.activeValid
      · exact choices.crashValid _ survives
    have accepted := route.accepts initialValid binding
    have runEvidence (bytes : ByteArray) (visible : pair.manifest = some bytes) : ∃ manifest files,
        IntegrityCheckpoint.decode bytes = .ok manifest ∧
        (List.range manifest.header.runCount.toNat).mapM (published.durable manifest.header.generation) = some files ∧
        manifest.validateRuns files = true ∧ manifest.header.committed.toNat ≤ history.length := by
      have parsed : ∃ manifest, IntegrityCheckpoint.decode bytes = .ok manifest := by
        rcases allowedBinding with old | new
        · exact strict bytes (old.symm.trans visible)
        · have exactBytes : bytes = metadata.encode := Option.some.inj (visible.symm.trans new)
          exact ⟨metadata, exactBytes.symm ▸ decoded⟩
      obtain ⟨manifest, parse⟩ := parsed
      have accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
          (some bytes) := visible ▸ accepted
      obtain ⟨files, durable, _, checks, through⟩ :=
        published.acceptsVersioned_runs accepted (VersionedCheckpoint.decode_integrity parse)
      have through : manifest.header.committed.toNat ≤ history.length := by
        have nat := UInt64.le_iff_toNat_le.mp through
        rwa [UInt64.toNat_ofNat_of_lt' countFits] at nat
      exact ⟨manifest, files, parse, durable, checks, through⟩
    refine ⟨sameMarker, allowedBinding, accepted, fun bytes visible => ?_, ?_⟩
    · obtain ⟨manifest, files, parse, durable, checked, _⟩ := runEvidence bytes visible
      exact ⟨manifest, files, parse, durable, checked⟩
    · cases visible : pair.manifest with
      | none =>
        have checkpoint : selectedCheckpointWatermark pair.manifest = some 0 := by rw [visible]; rfl
        exact ⟨⟨0, history.length⟩,
          walRange_of_reports checkpoint exactMarker (WAL.Boundary.decode_encode _) markerSize (Nat.zero_le _),
          rfl, by intro impossible; contradiction⟩
      | some bytes =>
        obtain ⟨manifest, _, parse, _, _, through⟩ := runEvidence bytes visible
        have checkpoint : selectedCheckpointWatermark pair.manifest = some manifest.header.committed.toNat := by
          rw [visible]
          exact selectedCheckpointWatermark_present_iff.mpr ⟨manifest, parse, rfl⟩
        refine ⟨⟨manifest.header.committed.toNat, history.length⟩,
          walRange_of_reports checkpoint exactMarker (WAL.Boundary.decode_encode _) markerSize through, rfl, ?_⟩
        intro newBinding
        have exactBytes : bytes = metadata.encode := Option.some.inj newBinding
        rw [exactBytes, decoded] at parse
        cases parse
        exact count
  have afterLayout : after.ReadLayout history := ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩
  have afterValid : after.Valid history := WalSegmentImage.Valid.of_chain chain fun pair chosen => by
    obtain ⟨_, _, _, _, range, decoded, through, _⟩ := readInputs pair chosen
    exact ⟨range, decoded, Nat.zero_le _, Nat.le_of_eq through⟩
  refine ⟨afterLayout, afterValid, fun pair chosen => ?_⟩
  obtain ⟨sameMarker, choice, accepted, runs, range, decoded, through, newCount⟩ := readInputs pair chosen
  obtain ⟨first, starts, _, addresses, required, _⟩ := afterLayout.selects afterValid chosen decoded
  exact ⟨sameMarker, choice, accepted, runs, range, first, decoded, through, newCount, starts, addresses, required⟩

end Alvoki.Storage.CheckpointPublication
