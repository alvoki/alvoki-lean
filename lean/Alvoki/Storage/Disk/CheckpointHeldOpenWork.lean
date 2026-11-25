import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.SelectedRecoveryChunkWork
import Alvoki.Storage.Disk.SelectedRecoveryPayload

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair RecoveryRequestCount
open WAL (frameSize)

/-- Count exact-prefix requests with the same manifest, listing, metadata
and opened-file callbacks as the held cached installer. -/
noncomputable def CheckpointHeldOpen.preparationRequests {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) : Nat :=
  let reported := opened.wal.operations.reported
  reached (prepareCachedRecoveryWithChunkCount directory reported.inventory.reports.readOptional
    (checkpointRunSizeReport reported.inventory.reports) reported.list
    (fun path => .ok (reported.inventory.reports.lstat path)) opened.calls.reads 0)

/-- The one held open supplies the exact checkpoint byte vector and
selected WAL interval that bound its primitive prefix requests. -/
theorem CheckpointHeldOpen.preparationRequests_le {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical)
    {checkpoint : Option (PackedTable × UInt64)}
    (selectedCheckpoint : SelectedIntegrityCheckpoint physical.durable retry.image.directory.active.manifest checkpoint)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    opened.preparationRequests ≤
      ((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * frameSize := by
  obtain ⟨watermark, covered, marker, length, visibleMarker, decodedMarker, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  let reported := opened.wal.operations.reported
  obtain ⟨extents, required, scanned, selection, _, first⟩ :=
    reported.toCachedRetryReadInventory.scanSelected following later absolute
  have atThrough : length.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : length.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  obtain ⟨manifest, decodedManifest, clock, files, valid, exactFiles⟩ :
      ∃ (manifest : Option Manifest.IntegrityCheckpoint),
        retry.image.directory.active.manifest.mapM Manifest.IntegrityCheckpoint.decode = .ok manifest ∧
        (manifest.map (·.header.committed.toNat)).getD 0 = layout.range.watermark ∧
        ∃ (files : List ByteArray), (match manifest with | none => files = [] | some m => m.validateRuns files = true) ∧
          files = (checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes) := by
    generalize retry.image.directory.active.manifest = binding at watermark selectedCheckpoint ⊢
    cases selectedCheckpoint with
    | absent =>
      have zero : layout.range.watermark = 0 := Option.some.inj watermark.symm
      exact ⟨none, rfl, zero.symm, [], rfl, rfl⟩
    | @present bytes manifest files table decoded stored loaded =>
      have clock : manifest.header.committed.toNat = layout.range.watermark := by
        unfold selectedCheckpointWatermark at watermark
        simpa [decoded, Except.toOption, Option.bind, Functor.map, Except.map] using watermark
      obtain ⟨verified, loaded⟩ := loadIntegrityRunSet_iff.mp loaded
      obtain ⟨checked, checkedFiles, restored⟩ := loadRunSet_restored loaded
      refine ⟨some manifest, ?_, clock, files, verified, ?_⟩
      · simp [Option.mapM, decoded, Functor.map, Except.map]
      · change files = table.runs.map (·.run.bytes)
        rw [(PackedTable.restore_spec restored).1]
        exact loadedRunBytes checkedFiles
  have marked := opened.metadata.callbackMetadata.markerRead.trans (congrArg Except.ok visibleMarker)
  have budget := prepareCachedRecoveryWithChunkCount_bound directory reported.inventory.reports.readOptional
    (checkpointRunSizeReport reported.inventory.reports) reported.list
    (fun path => .ok (reported.inventory.reports.lstat path)) opened.calls.reads opened.metadata.callbackMetadata.manifestRead
    decodedManifest marked decodedMarker aligned reported.listed scanned (clock.symm ▸ selection)
    (clock.symm ▸ atThrough.symm ▸ covered) 0
  have requests := budget.2 files valid
  rw [exactFiles, first, atThrough] at requests
  simpa only [CheckpointHeldOpen.preparationRequests, List.map_map, Function.comp_def, Nat.zero_add, Option.getD_some]
    using requests

end Alvoki.Storage.DiskSession
