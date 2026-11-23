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
lake env leanchecker Alvoki.Storage.Disk.MarkedAdapterRefinement
lake env leanchecker Alvoki.Storage.Publication.DiskPublication
lake env leanchecker Alvoki.Storage.Publication.DiskPublicationModel
lake env leanchecker Alvoki.Storage.Disk.WalBoundary
lake env leanchecker Alvoki.Storage.Disk.WalBoundaryModel
lake env leanchecker Alvoki.Storage.Disk.WalWritePublicationModel
lake env leanchecker Alvoki.Storage.Disk.MarkedWalReopenModel
lake env leanchecker Alvoki.Storage.Publication.CheckpointPublicationModel
lake env leanchecker Alvoki.Storage.Publication.DirectoryPublicationModel
lake env lean --run Alvoki/Checks/SequentialChecks.lean
lake env lean --run Alvoki/Checks/PackedTableChecks.lean
lake exe alvoki-disk-checks
