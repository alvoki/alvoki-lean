import Alvoki.Storage.Disk.WalSegmentBoundedOpenReports

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- Checkpoint publication leaves an exactly sized keeper. -/
abbrev HealthyCheckpointCutReports (directory : DiskDirectory) (owners : DiskSession.LockOwners)
    (descriptor : Nat) (wal : WalSegmentImage) (pair : DirectoryPublication.Bindings) (watermark : Nat)
    (durable : CheckpointPublication.RunFiles) :=
  HealthyBoundedWalReports directory owners descriptor wal pair watermark durable ByteArray.empty

theorem HealthyCheckpointCutReports.readCheckpoint {directory owners descriptor wal pair watermark durable}
    (raw : HealthyCheckpointCutReports directory owners descriptor wal pair watermark durable)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint) :
    readIntegrityCheckpoint (raw.reports.readOptional (directory.file .manifest))
      (fun generation index => raw.reports.readBin (directory.file (.run generation index)))
      (fun result => result.mapError IO.userError) = .ok checkpoint :=
  HealthyBoundedWalReports.readCheckpoint raw selected

theorem HealthyCheckpointCutReports.scan {directory owners descriptor wal pair watermark durable}
    (raw : HealthyCheckpointCutReports directory owners descriptor wal pair watermark durable)
    {history : List WAL.Write} (layout : wal.ReadLayout history) :
    raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName)) =
      .ok (wal.segments.map WalSegment.first) :=
  HealthyBoundedWalReports.scan raw layout

theorem HealthyCheckpointCutReports.readSelectedBounded {directory owners descriptor wal pair watermark durable}
    (raw : HealthyCheckpointCutReports directory owners descriptor wal pair watermark durable)
    {history : List WAL.Write} (layout : wal.ReadLayout history)
    {through : Nat} (atEnd : through = history.length) (covered : watermark ≤ through)
    {count : UInt64} (absolute : count.toNat = through * frameSize)
    {first : Nat}
    (selected : selectWalSegmentReads (wal.segments.map WalSegment.first) watermark =
      some (first, (wal.readDescriptors watermark).map WalSegment.first)) :
    readSelectedWithPrefix directory watermark count raw.list (fun path => .ok (raw.reports.lstat path))
      raw.reports.readBin raw.readPrefix =
      .ok (⟨(wal.readDescriptors watermark).map (fun segment => (segment.first, segment.bytes)), []⟩,
        wal.active.bytes.size) := by
  simpa only [ByteArray.append_empty] using HealthyBoundedWalReports.readSelectedBounded
    raw layout atEnd covered absolute selected

end Alvoki.Storage.WalSegmentRepair
