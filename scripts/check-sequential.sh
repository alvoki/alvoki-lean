#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cd lean
lake build Alvoki.Checks.AxiomPolicy RunMergeProofs CodecVariants Alvoki.Storage
lake env lean Alvoki/Checks/ProofRoadmapAudit.lean
lake env lean Alvoki/Checks/SequentialAudit.lean

# This standard declaration serves as a negative control outside the allowlist.
printf 'import Alvoki.Checks.AxiomPolicy\nnoncomputable def unexpectedDependency := @sorryAx\n#check_axioms unexpectedDependency\n' > "$scratch/Reject.lean"
if lake env lean "$scratch/Reject.lean" > "$scratch/rejection.log" 2>&1; then
  echo "Axiom policy accepted its negative control" >&2
  exit 1
fi
if ! grep -q "unexpected axiom dependencies for 'unexpectedDependency':.*sorryAx" "$scratch/rejection.log"; then
  cat "$scratch/rejection.log" >&2
  exit 1
fi
echo "Axiom policy accepted the audited proofs and rejected its negative control."
lake env leanchecker Alvoki.Storage.Table.SequentialModel
lake env leanchecker Alvoki.Storage.Table.SequentialPurge
lake env leanchecker Alvoki.Storage.Table.SnapshotTable
lake env leanchecker Alvoki.Storage.Table.CompactionRead
lake env leanchecker Alvoki.Storage.Table.MemTableContract
lake env leanchecker Alvoki.Storage.Table.MemTableTree
lake env leanchecker Alvoki.Storage.Table.MemTable
lake env leanchecker Alvoki.Storage.Table.PackedTable
lake env leanchecker Alvoki.Storage.Disk.WriteAheadLog
lake env leanchecker Alvoki.Storage.Disk.Recovery
lake env leanchecker Alvoki.Storage.Disk.Manifest
lake env leanchecker Alvoki.Storage.Disk.LegacyManifest
lake env leanchecker Alvoki.Storage.Disk.VersionedManifest
lake env leanchecker Alvoki.Storage.Disk.StagingFile
lake env leanchecker Alvoki.Storage.Disk.DiskTable
lake env leanchecker Alvoki.Storage.Disk.DiskPaths
lake env leanchecker Alvoki.Storage.Disk.CheckpointRead
lake env leanchecker Alvoki.Storage.Disk.LegacyCheckpointRead
lake env leanchecker Alvoki.Storage.Disk.DiskRecoveryModel
lake env leanchecker Alvoki.Storage.Disk.FullWatermarkReopen
lake env leanchecker Alvoki.Storage.Disk.MarkedAdapterRefinement
lake env leanchecker Alvoki.Storage.Disk.MarkedWriteTrace
lake env leanchecker Alvoki.Storage.Disk.MarkedReopenStability
lake env leanchecker Alvoki.Storage.Disk.MarkedSessionTrace
lake env leanchecker Alvoki.Storage.Disk.MarkedCheckpointPublication
lake env leanchecker Alvoki.Storage.Disk.MarkedCheckpointReady
lake env leanchecker Alvoki.Storage.Disk.MarkedCheckpointReopenReady
lake env leanchecker Alvoki.Storage.Disk.MarkedSessionHistory
lake env leanchecker Alvoki.Storage.Disk.MarkedDatabaseState
lake env leanchecker Alvoki.Storage.Disk.ObservedMarkedState
lake env leanchecker Alvoki.Storage.Disk.MarkedDatabaseCheckpoint
lake env leanchecker Alvoki.Storage.Disk.MarkedDatabaseTrace
lake env leanchecker Alvoki.Storage.Disk.MarkedWriteReopenProgress
lake env leanchecker Alvoki.Storage.Disk.OptionalFileRead
lake env leanchecker Alvoki.Storage.Disk.CheckpointFileDispatch
lake env leanchecker Alvoki.Storage.Disk.CheckpointObservedDispatch
lake env leanchecker Alvoki.Storage.Disk.CheckpointLockHandoff
lake env leanchecker Alvoki.Storage.Disk.CheckpointCutSession
lake env leanchecker Alvoki.Storage.Disk.CheckpointSuccessSession
lake env leanchecker Alvoki.Storage.Disk.SegmentedCheckpointStep
lake env leanchecker Alvoki.Storage.Disk.SegmentedBootstrapReady
lake env leanchecker Alvoki.Storage.Disk.SegmentedWriterState
lake env leanchecker Alvoki.Storage.Disk.SegmentedWriterEntry
lake env leanchecker Alvoki.Storage.Disk.SegmentedAppendTrace
lake env leanchecker Alvoki.Storage.Disk.SegmentedWriterTrace
lake env leanchecker Alvoki.Storage.Disk.SegmentedWriterMaintenance
lake env leanchecker Alvoki.Storage.Disk.SegmentedDatabaseTrace
lake env leanchecker Alvoki.Storage.Disk.SegmentedBatchAppend
lake env leanchecker Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
lake env leanchecker Alvoki.Storage.Disk.SegmentedAppendRecovery
lake env leanchecker Alvoki.Storage.Disk.SegmentedCleanReopen
lake env leanchecker Alvoki.Storage.Disk.UncheckpointedCachedReopen
lake env leanchecker Alvoki.Storage.Disk.SegmentedReadyPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedFailureRelease
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionReadPlan
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionInventory
lake env leanchecker Alvoki.Storage.Disk.SegmentedRetainedWriter
lake env leanchecker Alvoki.Storage.Disk.AppendLockHandoff
lake env leanchecker Alvoki.Storage.Disk.AppendCutSession
lake env leanchecker Alvoki.Storage.Disk.ReopenedSegmentAppend
lake env leanchecker Alvoki.Storage.Disk.AppendCutContinuation
lake env leanchecker Alvoki.Storage.Disk.AppendRetrySession
lake env leanchecker Alvoki.Storage.Disk.WalSegmentAppendPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentMarkerPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedMarkerPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedAppendPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRotationPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointPowerLoss
lake env leanchecker Alvoki.Storage.Disk.CheckpointRetrySession
lake env leanchecker Alvoki.Storage.Disk.SegmentedCheckpointRecovery
lake env leanchecker Alvoki.Storage.Disk.SegmentedCheckpointPowerLoss
lake env leanchecker Alvoki.Storage.Disk.RetainedAppendReports
lake env leanchecker Alvoki.Storage.Disk.RetainedAppendRecovery
lake env leanchecker Alvoki.Storage.Disk.RetainedWriterState
lake env leanchecker Alvoki.Storage.Disk.RetainedWriterReopen
lake env leanchecker Alvoki.Storage.Disk.RetainedCollectionPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionStep
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionRetry
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionLockHandoff
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionLiveReopen
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionCachedReopen
lake env leanchecker Alvoki.Storage.Disk.SegmentedRunRetentionReopen
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionBarrierError
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionKeeperError
lake env leanchecker Alvoki.Storage.Disk.SegmentedCollectionRetryPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointRetained
lake env leanchecker Alvoki.Storage.Disk.WalSegmentUnlinkSchedule
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCollectionPlan
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCollectionMetadata
lake env leanchecker Alvoki.Storage.Disk.WalSealedUnlinkSurvivors
lake env leanchecker Alvoki.Storage.Disk.SegmentedRetryTrace
lake env leanchecker Alvoki.Storage.Disk.BoundedOpenReadFailure
lake env leanchecker Alvoki.Storage.Disk.BoundedReopenFailure
lake env leanchecker Alvoki.Storage.Disk.WalSegmentBoundedRetry
lake env leanchecker Alvoki.Storage.Disk.DiskSession
lake env leanchecker Alvoki.Storage.Disk.SessionReadGuards
lake env leanchecker Alvoki.Storage.Disk.MarkedOpenControl
lake env leanchecker Alvoki.Storage.Disk.DiskLockLifecycle
lake env leanchecker Alvoki.Storage.Disk.LockDescriptionLifetime
lake env leanchecker Alvoki.Storage.Disk.LockedSegmentReopenEffects
lake env leanchecker Alvoki.Storage.Disk.SegmentedSessionInstall
lake env leanchecker Alvoki.Storage.Disk.BoundedSegmentSession
lake env leanchecker Alvoki.Storage.Disk.RotationSessionHandoff
lake env leanchecker Alvoki.Storage.Disk.RotationLockHandoff
lake env leanchecker Alvoki.Storage.Disk.RotationAuthorityRetry
lake env leanchecker Alvoki.Storage.Disk.RotationReopenTrace
lake env leanchecker Alvoki.Storage.Disk.RotationRetrySession
lake env leanchecker Alvoki.Storage.Disk.SegmentedRotationRecovery
lake env leanchecker Alvoki.Storage.Disk.SegmentedRotationPowerLoss
lake env leanchecker Alvoki.Storage.Disk.SegmentedRotationStep
lake env leanchecker Alvoki.Storage.Disk.BootstrapAdmissionEffects
lake env leanchecker Alvoki.Storage.Disk.FirstMarkedSession
lake env leanchecker Alvoki.Storage.Disk.RunGenerationCollection
lake env leanchecker Alvoki.Storage.Disk.RunFileName
lake env leanchecker Alvoki.Storage.Disk.RunFileSelection
lake env leanchecker Alvoki.Storage.Disk.RunFileInventory
lake env leanchecker Alvoki.Storage.Disk.RunUnlinkEffects
lake env leanchecker Alvoki.Storage.Publication.RunCollection
lake env leanchecker Alvoki.Storage.Disk.RunUnlinkSchedule
lake env leanchecker Alvoki.Storage.Disk.LockedRunCollection
lake env leanchecker Alvoki.Storage.Disk.VersionedRunCollection
lake env leanchecker Alvoki.Storage.Disk.RecoveryProgress
lake env leanchecker Alvoki.Storage.Disk.LockedOpenFileReads
lake env leanchecker Alvoki.Storage.Disk.LockedMarkedRead
lake env leanchecker Alvoki.Storage.Disk.LockedRecoveryReads
lake env leanchecker Alvoki.Storage.Disk.LockedRecoveryCompletion
lake env leanchecker Alvoki.Storage.Disk.UncertainWriteTraceEntry
lake env leanchecker Alvoki.Storage.Disk.LockedInterruptedCheckpoint
lake env leanchecker Alvoki.Storage.Disk.ManifestIntegrity
lake env leanchecker Alvoki.Storage.Disk.IntegrityCheckpointRead
lake env leanchecker Alvoki.Storage.Disk.ManifestIntegritySingleByte
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointRead
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointLineage
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointPublication
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointRetry
lake env leanchecker Alvoki.Storage.Disk.VersionedMarkedRecovery
lake env leanchecker Alvoki.Storage.Disk.LockedVersionedCheckpointRead
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointReopen
lake env leanchecker Alvoki.Storage.Disk.VersionedReadyWriter
lake env leanchecker Alvoki.Storage.Disk.VersionedReadyMaintenance
lake env leanchecker Alvoki.Storage.Disk.VersionedUncertainWrite
lake env leanchecker Alvoki.Storage.Disk.IntegrityBootstrap
lake env leanchecker Alvoki.Storage.Disk.StrictCheckpointReopen
lake env leanchecker Alvoki.Storage.Disk.IntegrityDatabaseTrace
lake env leanchecker Alvoki.Storage.Disk.IntegrityTraceReads
lake env leanchecker Alvoki.Storage.Disk.VersionedReadyRunCollection
lake env leanchecker Alvoki.Storage.Disk.LockedMarkedReopenEffects
lake env leanchecker Alvoki.Storage.Disk.LockedMarkedReopenFailureTrace
lake env leanchecker Alvoki.Storage.Disk.IntegrityRunCollectionProgress
lake env leanchecker Alvoki.Storage.Disk.IntegrityRunCollectionSpace
lake env leanchecker Alvoki.Storage.Disk.RetainedWalSuffix
lake env leanchecker Alvoki.Storage.Disk.RetainedWalReplay
lake env leanchecker Alvoki.Storage.Disk.RetainedWalBoundary
lake env leanchecker Alvoki.Storage.Disk.WalSegmentFileName
lake env leanchecker Alvoki.Storage.Disk.WalSegmentPathIdentity
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCollection
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRecovery
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRotationIO
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRotation
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRotationCommit
lake env leanchecker Alvoki.Storage.Disk.WalSegmentInventory
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReadPlan
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRepair
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReadIO
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReplay
lake env leanchecker Alvoki.Storage.Disk.WalSegmentMarkerRead
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRepairIO
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRepairOpen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRepairEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReopenEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReplayStability
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRetryReads
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRetryReadEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentOpenFast
lake env leanchecker Alvoki.Storage.Disk.WalSegmentOpenFastEffects
lake env leanchecker Alvoki.Storage.Disk.WalBatch
lake env leanchecker Alvoki.Storage.Disk.WalBatchCommitEffects
lake env leanchecker Alvoki.Storage.Disk.WalBatchMarkerPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalBatchCommitReports
lake env leanchecker Alvoki.Storage.Disk.WalBatchSession
lake env leanchecker Alvoki.Storage.Disk.WalBatchRecovery
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCommit
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCommitEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentAppendRepair
lake env leanchecker Alvoki.Storage.Disk.WalSegmentAppendLayout
lake env leanchecker Alvoki.Storage.Disk.WalSegmentFirstReplay
lake env leanchecker Alvoki.Storage.Disk.WalSegmentFirstOpen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRotationReopen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentBootstrapEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentBoundedOpenEffects
lake env leanchecker Alvoki.Storage.Disk.WalSegmentBoundedOpen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentSizedCheckpointOpen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentSizedCheckpointReports
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedExtentOpen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedExtentInstall
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedExtentOpenEffects
lake env leanchecker Alvoki.Storage.Disk.SizedCheckpointOpenFailure
lake env leanchecker Alvoki.Storage.Disk.CachedWalOpenFailure
lake env leanchecker Alvoki.Storage.Disk.CachedWalKeeperOpenFailure
lake env leanchecker Alvoki.Storage.Disk.CachedWalMarkerOpenFailure
lake env leanchecker Alvoki.Storage.Disk.CachedOpenRejection
lake env leanchecker Alvoki.Storage.Disk.CachedWalExtentRetry
lake env leanchecker Alvoki.Storage.Disk.CachedCheckpointExtentRetry
lake env leanchecker Alvoki.Storage.Disk.RecoveryRequestCount
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedOpenWork
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCollectionSpace
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedExtentReports
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCachedAppendPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentRecoveryWork
lake env leanchecker Alvoki.Storage.Disk.WalSegmentReadWork
lake env leanchecker Alvoki.Storage.Disk.RecoverySizedReads
lake env leanchecker Alvoki.Storage.Disk.ReadRecoveryPrefix
lake env leanchecker Alvoki.Storage.Disk.WalSegmentSizedOpen
lake env leanchecker Alvoki.Storage.Disk.IntegrityCheckpointSizedRead
lake env leanchecker Alvoki.Storage.Disk.WalGroupSyncSchedule
lake env leanchecker Alvoki.Storage.Disk.SyncHandleRouting
lake env leanchecker Alvoki.Storage.Disk.SyncHandleCustody
lake env leanchecker Alvoki.Storage.Disk.StagedHandleCustody
lake env leanchecker Alvoki.Storage.Disk.SyncHandleEffects
lake env leanchecker Alvoki.Storage.Disk.DescriptorInventory
lake env leanchecker Alvoki.Storage.Disk.DescriptorFork
lake env leanchecker Alvoki.Storage.Disk.DelayedKeeperInventory
lake env leanchecker Alvoki.Storage.Disk.AppendHandleCustody
lake env leanchecker Alvoki.Storage.Disk.KeeperReadCustody
lake env leanchecker Alvoki.Storage.Disk.WriteGroupFsync
lake env leanchecker Alvoki.Storage.Disk.AppendGroupedReports
lake env leanchecker Alvoki.Storage.Disk.SegmentedKeeperDescriptor
lake env leanchecker Alvoki.Storage.Disk.SegmentedDelayedDirectorySync
lake env leanchecker Alvoki.Storage.Disk.SegmentedDelayedAppendReopen
lake env leanchecker Alvoki.Storage.Disk.SegmentedKeeperSyncBeforeBarrier
lake env leanchecker Alvoki.Storage.Disk.SegmentedKeeperReachedReplacement
lake env leanchecker Alvoki.Storage.Disk.SegmentedDelayedKeeperPowerLoss
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointPublication
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointReopen
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointRetryLayout
lake env leanchecker Alvoki.Storage.Disk.WalSegmentCheckpointOpenReports
lake env leanchecker Alvoki.Storage.Disk.WalSegmentBoundedOpenReports
lake env leanchecker Alvoki.Storage.Disk.WalSegmentSerialReplay
lake env leanchecker Alvoki.Storage.Disk.FreshMarkedBootstrap
lake env leanchecker Alvoki.Storage.Disk.MarkedCheckpointReopenProgress
lake env leanchecker Alvoki.Storage.Disk.RecoveredPinRefinement
lake env leanchecker Alvoki.Storage.Disk.WalReplayAgreement
lake env leanchecker Alvoki.Storage.Disk.WalReplayProvenance
lake env leanchecker Alvoki.Storage.Disk.CheckpointHistory
lake env leanchecker Alvoki.Storage.Publication.DiskPublication
lake env leanchecker Alvoki.Storage.Publication.DiskPublicationModel
lake env leanchecker Alvoki.Storage.Disk.WalBoundary
lake env leanchecker Alvoki.Storage.Disk.WalBoundaryModel
lake env leanchecker Alvoki.Storage.Disk.WalWritePublicationModel
lake env leanchecker Alvoki.Storage.Disk.MarkedWalReopenModel
lake env leanchecker Alvoki.Storage.Disk.ReplacedWalDescriptor
lake env leanchecker Alvoki.Storage.Publication.CheckpointPublicationModel
lake env leanchecker Alvoki.Storage.Publication.DirectoryPublicationModel
lake env lean --run Alvoki/Checks/SequentialChecks.lean
lake env lean --run Alvoki/Checks/PackedTableChecks.lean
lake env lean --run Alvoki/Checks/ManifestIntegrityChecks.lean
lake env lean --run Alvoki/Checks/VersionedCheckpointReadChecks.lean
lake env lean --run Alvoki/Checks/WalSegmentMarkerReadChecks.lean
lake exe alvoki-disk-checks
python3 ../scripts/check-disk-process-death.py .lake/build/bin/alvoki-disk-checks
lake build alvoki-disk-replay
python3 ../benchmarks/disk_replay.py --sizes 3 --segments 1 3 --trials 1 --out "$scratch/replay.csv"
python3 ../benchmarks/disk_replay.py --sizes 3 --segments 1 3 --trials 1 --repair-tail --out "$scratch/replay-repair.csv"
