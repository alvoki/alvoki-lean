import Alvoki.Storage.Disk.CheckpointHeldOpenWork
import Alvoki.Storage.Disk.NativeMarkedReadPrefix
import Alvoki.Storage.Disk.MetadataRecoveryChunkWork

namespace Alvoki.Storage.DiskSession

open System RecoveryRequestCount WalSegmentRepair WAL.Boundary
open WAL (frameSize)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

namespace CapturedMarkedReadReports

variable {admission : CensusOpenAdmissionReports input directory inventory retry}
  (reports : CapturedMarkedReadReports admission layout published)

/-- The eventual worker carries this stream directly into its checked WAL
extent inspection. Count the reported directory calls before name filtering. -/
def directoryWork : DirectoryReadWork :=
  (CheckedDirectoryReadReport.scanned reports.listing.scan).work

/-- Count primitive run and WAL chunks with the callbacks of the prepared
opener. In particular the counted keeper reads the selected prefix, while
its full observed size only selects the repair route. -/
noncomputable def payloadReadRequests : Nat :=
  reports.walReads.payloadReadRequests reports.reads

/-- Checkpoint bytes and the retained WAL interval bound the selected
payload callbacks. The cap does not include the metadata reads, directory
calls or the primitive operations inside a repair callback. -/
theorem payloadReadRequests_le
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start) :
    reports.payloadReadRequests ≤
      ((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * frameSize :=
  reports.walReads.payloadReadRequests_le reports.reads selected
    (reports.metadata.manifestRead layout.decoded) (reports.metadata.markerRead layout.decoded)
    following (prepared.newer _ List.mem_cons_self)

/-- Count the two reported metadata readers on their chosen opened
descriptions. Stat and open are outside this chunk counter. -/
def metadataReadRequests : Nat :=
  let reads := reports.reads
  recoveryCalls Prod.snd (reads.countMetadata directory (directory.file .manifest) (0, 0)) +
    recoveryCalls Prod.snd (reads.countMetadata directory (directory.file .walBoundary) (0, 0))

/-- The no-follow manifest report supplies zero work when absent, or the
exact selected manifest extent when present. The marker retains its EOF
witness in the twenty-five-call budget. -/
theorem metadataReadRequests_le :
    reports.metadataReadRequests ≤
      (retry.image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit := by
  have marker := reports.reads.countMetadata_le directory (directory.file .walBoundary) (0, 0)
  have bound := reports.reads.countMetadata_le directory (directory.file .manifest) (0, 0)
  simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_add] at marker
  have different : (directory.file .manifest == directory.file .walBoundary) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have paths := congrArg FilePath.toString same
    change (directory.path.toString ++ "/") ++ "MANIFEST" =
      (directory.path.toString ++ "/") ++ "WAL.commit" at paths
    exact (by decide : "MANIFEST" ≠ "WAL.commit") ((String.append_right_inj _).mp paths)
  simp only [different, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at bound
  have manifest : recoveryCalls Prod.snd
      (reports.reads.countMetadata directory (directory.file .manifest) (0, 0)) ≤
      (retry.image.directory.active.manifest.map ByteArray.size).getD 0 := by
    cases visible : retry.image.directory.active.manifest with
    | none =>
      obtain ⟨_, name, details, stat⟩ := reports.metadata.manifestMissing visible
      simpa [stat, Except.toOption] using bound
    | some bytes =>
      obtain ⟨⟨file⟩, _⟩ := reports.metadata.manifestFile bytes visible
      have seen := file.observesFile
      simpa [seen.stat, seen.extent, Except.toOption] using bound
  exact Nat.add_le_add manifest marker

/-- The actual checked stream reports one open and close, one read per raw
name and the terminal read. Only the resulting whole listing enters the
extent scan. -/
theorem directoryWork_exact :
    reports.directoryWork.opendirCalls = 1 ∧
    reports.directoryWork.readdirCalls = reports.listing.scan.names.length + 1 ∧
    reports.directoryWork.closedirCalls = 1 ∧
    reports.catalog.list directory.path = .ok (reports.listing.scan.entries directory.path) := by
  obtain ⟨returned, _⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    reports.listing.eof reports.listing.closed reports.listing.complete
  exact ⟨rfl, rfl, rfl, reports.listed.trans returned⟩

end CapturedMarkedReadReports

namespace MarkedReadyOpenObservations

variable (reported : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected)

abbrev directoryWork : DirectoryReadWork := reported.reads.directoryWork

noncomputable abbrev payloadReadRequests : Nat := reported.reads.payloadReadRequests

theorem payloadReadRequests_le
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start) :
    reported.payloadReadRequests ≤
      ((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * frameSize :=
  reported.reads.payloadReadRequests_le selected prepared following

abbrev metadataReadRequests : Nat := reported.reads.metadataReadRequests

theorem metadataReadRequests_le :
    reported.metadataReadRequests ≤
      (retry.image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit :=
  reported.reads.metadataReadRequests_le

theorem directoryWork_exact :
    reported.directoryWork.opendirCalls = 1 ∧
    reported.directoryWork.readdirCalls = reported.reads.listing.scan.names.length + 1 ∧
    reported.directoryWork.closedirCalls = 1 ∧
    reported.reads.catalog.list directory.path = .ok (reported.reads.listing.scan.entries directory.path) :=
  reported.reads.directoryWork_exact

/-- The shared finisher counts one unlink callback per selected later name.
The other requests depend on the observed keeper extent and on whether
the checked suffix is empty. Each grouped sync counts as one request. -/
theorem repairWork_exact (prepared : Prepared retry.image layout.target layout.plan) :
    layout.boundedPlan.newer = retry.image.later.visible ∧
    countBoundedRepairCallbacks directory layout.boundedPlan reported.reads.wal.keeper.calls.metadata.byteSize.toNat =
      .ok (if layout.boundedPlan.newer.isEmpty &&
          reported.reads.wal.keeper.calls.metadata.byteSize.toNat == layout.boundedPlan.keeperSize then 2
        else layout.boundedPlan.newer.length +
          if layout.boundedPlan.keeperSize < reported.reads.wal.keeper.calls.metadata.byteSize.toNat then 6 else 3) := by
  have names : layout.boundedPlan.newer = retry.image.later.visible := prepared.names
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have valid := layout.boundedPlan_valid (by
    rw [names]
    exact prepared.newer _ List.mem_cons_self)
  have measured : reported.reads.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    reported.reads.wal.keeper.observesFile.extent
  have fits : layout.boundedPlan.keeperSize ≤ reported.reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [measured]
    exact (Plan.valid_iff _).mp prepared.valid |>.2.1
  exact ⟨names, countBoundedRepairCallbacks_exact directory _ _ valid size fits⟩

/-- One reported healthy marked open returns its installed session and
reached files. The same packet bounds the selected primitive chunk reads,
raw directory calls and grouped repair requests for this one attempt. -/
theorem installsWithWork
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ session final repairs,
      reported.finish.run reported.chronology = .ok session (reported.finish.census, final) ∧
      final.image.directory.active = retry.image.directory.active ∧
      CachedRetryInstalled (before := retry) reported.reads.walReads reported.admission.reached
        reported.admission.owner reported.reads.bindings published reported.callbacks.liveRefs (.ok session final) ∧
      reported.metadataReadRequests + reported.payloadReadRequests ≤
        (retry.image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit +
          (((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
            (layout.range.through - layout.first) * frameSize) ∧
      reported.directoryWork.opendirCalls + reported.directoryWork.readdirCalls + reported.directoryWork.closedirCalls =
        reported.reads.listing.scan.names.length + 3 ∧
      countBoundedRepairCallbacks directory layout.boundedPlan reported.reads.wal.keeper.calls.metadata.byteSize.toNat =
        .ok repairs ∧ repairs ≤ retry.image.later.visible.length + 6 := by
  obtain ⟨session, final, returned, pair, _, _, installed⟩ := reported.finish.installsFromCensus reported.chronology
    reported.markerFound prepared.newer following accepted ordered
  obtain ⟨opened, read, closed, _⟩ := reported.directoryWork_exact
  obtain ⟨names, repairs⟩ := reported.repairWork_exact prepared
  refine ⟨session, final, _, returned, pair, installed,
    Nat.add_le_add reported.metadataReadRequests_le (reported.payloadReadRequests_le prepared following),
    by omega, repairs, ?_⟩
  rw [← names]
  split
  · omega
  · split <;> omega

end MarkedReadyOpenObservations

end Alvoki.Storage.DiskSession
