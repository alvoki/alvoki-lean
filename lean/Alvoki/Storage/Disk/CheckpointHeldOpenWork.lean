import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.SelectedRecoveryChunkWork
import Alvoki.Storage.Disk.SelectedRecoveryPayload

namespace Alvoki.Storage.WalSegmentRepair

open System CheckpointPublication DiskSession RecoveryRequestCount
open WAL (frameSize)

/-- Count the primitive chunk reads of the same run, seal and keeper
prefix callbacks used by the held reader. Metadata uses its separate
bounded read schedule and is outside this counter. -/
noncomputable def CachedRetryReadReports.payloadReadRequests
    {directory history image} {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout) (reads : CheckpointRunChunkReads) : Nat :=
  reached (prepareCachedRecoveryWithChunkCount directory reported.inventory.reports.readOptional
    (checkpointRunSizeReport reported.inventory.reports) reported.list
    (fun path => .ok (reported.inventory.reports.lstat path)) reads 0)

/-- The selected checkpoint byte vector and WAL interval bound the chunk
reader using this report's manifest, marker and checked extent selection. -/
theorem CachedRetryReadReports.payloadReadRequests_le
    {directory history image physical} {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout) (reads : CheckpointRunChunkReads)
    {checkpoint : Option (PackedTable × UInt64)}
    (selectedCheckpoint : SelectedIntegrityCheckpoint physical image.directory.active.manifest checkpoint)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) =
      .ok image.directory.active.walBoundary)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (later : ∀ first ∈ image.later.visible, layout.range.through < first) :
    reported.payloadReadRequests reads ≤
      ((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * frameSize := by
  obtain ⟨watermark, covered, marker, length, visibleMarker, decodedMarker, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  obtain ⟨extents, required, scanned, selection, _, first⟩ :=
    reported.toCachedRetryReadInventory.scanSelected following later absolute
  have atThrough : length.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : length.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  obtain ⟨manifest, decodedManifest, clock, files, valid, exactFiles⟩ :
      ∃ (manifest : Option Manifest.IntegrityCheckpoint),
        image.directory.active.manifest.mapM Manifest.IntegrityCheckpoint.decode = .ok manifest ∧
        (manifest.map (·.header.committed.toNat)).getD 0 = layout.range.watermark ∧
        ∃ (files : List ByteArray), (match manifest with | none => files = [] | some m => m.validateRuns files = true) ∧
          files = (checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes) := by
    generalize image.directory.active.manifest = binding at watermark selectedCheckpoint ⊢
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
  have marked := markerRead.trans (congrArg Except.ok visibleMarker)
  have budget := prepareCachedRecoveryWithChunkCount_bound directory reported.inventory.reports.readOptional
    (checkpointRunSizeReport reported.inventory.reports) reported.list
    (fun path => .ok (reported.inventory.reports.lstat path)) reads manifestRead
    decodedManifest marked decodedMarker aligned reported.listed scanned (clock.symm ▸ selection)
    (clock.symm ▸ atThrough.symm ▸ covered) 0
  have requests := budget.2 files valid
  rw [exactFiles, first, atThrough] at requests
  simpa only [CachedRetryReadReports.payloadReadRequests, List.map_map, Function.comp_def, Nat.zero_add, Option.getD_some]
    using requests

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open CheckpointPublication WalSegmentRepair
open WAL (frameSize)

/-- The held adapter and its returned session share these selected read
callbacks. The counter is proof-only. -/
noncomputable def CheckpointHeldOpen.preparationRequests {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) : Nat :=
  opened.wal.operations.reported.payloadReadRequests opened.calls.reads

theorem CheckpointHeldOpen.preparationRequests_le {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint physical.durable retry.image.directory.active.manifest checkpoint)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    opened.preparationRequests ≤
      ((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * frameSize :=
  opened.wal.operations.reported.payloadReadRequests_le opened.calls.reads selected
    opened.metadata.callbackMetadata.manifestRead opened.metadata.callbackMetadata.markerRead following later

end Alvoki.Storage.DiskSession
