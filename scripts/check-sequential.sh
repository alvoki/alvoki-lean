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
{
  printf 'import Alvoki.Checks.AxiomPolicy\n'
  sed 's/^#print axioms /#check_axioms /' Alvoki/Checks/ProofRoadmapAudit.lean
} > "$scratch/Audit.lean"
lake env lean "$scratch/Audit.lean"
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
lake env leanchecker Alvoki.Storage.Table.PackedTable
lake env leanchecker Alvoki.Storage.Disk.WriteAheadLog
lake env leanchecker Alvoki.Storage.Disk.Recovery
lake env leanchecker Alvoki.Storage.Disk.Manifest
lake env leanchecker Alvoki.Storage.Disk.DiskTable
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
lake env leanchecker Alvoki.Storage.Disk.DiskSession
lake env leanchecker Alvoki.Storage.Disk.SessionReadGuards
lake env leanchecker Alvoki.Storage.Disk.MarkedOpenControl
lake env leanchecker Alvoki.Storage.Disk.DiskLockLifecycle
lake env leanchecker Alvoki.Storage.Disk.RunGenerationCollection
lake env leanchecker Alvoki.Storage.Disk.RunFileName
lake env leanchecker Alvoki.Storage.Disk.RunFileInventory
lake env leanchecker Alvoki.Storage.Disk.RunUnlinkEffects
lake env leanchecker Alvoki.Storage.Publication.RunCollection
lake env leanchecker Alvoki.Storage.Disk.RunUnlinkSchedule
lake env leanchecker Alvoki.Storage.Disk.RecoveryProgress
lake env leanchecker Alvoki.Storage.Disk.LockedOpenFileReads
lake env leanchecker Alvoki.Storage.Disk.LockedMarkedRead
lake env leanchecker Alvoki.Storage.Disk.LockedRecoveryReads
lake env leanchecker Alvoki.Storage.Disk.LegacyTraceEntry
lake env leanchecker Alvoki.Storage.Disk.LockedRecoveryCompletion
lake env leanchecker Alvoki.Storage.Disk.UncertainWriteTraceEntry
lake env leanchecker Alvoki.Storage.Disk.LockedInterruptedCheckpoint
lake env leanchecker Alvoki.Storage.Disk.ManifestIntegrity
lake env leanchecker Alvoki.Storage.Disk.ManifestIntegritySingleByte
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointRead
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointLineage
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointPublication
lake env leanchecker Alvoki.Storage.Disk.VersionedCheckpointRetry
lake env leanchecker Alvoki.Storage.Disk.VersionedMarkedRecovery
lake env leanchecker Alvoki.Storage.Disk.LegacyBootstrapRetry
lake env leanchecker Alvoki.Storage.Disk.FreshMarkedBootstrap
lake env leanchecker Alvoki.Storage.Disk.LegacyWalRecovery
lake env leanchecker Alvoki.Storage.Disk.LegacyMarkedBootstrap
lake env leanchecker Alvoki.Storage.Disk.LegacyBootstrapCuts
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
lake exe alvoki-disk-checks
python3 ../scripts/check-disk-process-death.py .lake/build/bin/alvoki-disk-checks
