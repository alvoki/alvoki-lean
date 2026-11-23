#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cd lean
lake build AxiomPolicy RunMergeProofs CodecVariants DiskTable DiskPublicationModel WalBoundaryModel
{
  printf 'import AxiomPolicy\n'
  sed 's/^#print axioms /#check_axioms /' ProofRoadmapAudit.lean
} > "$scratch/Audit.lean"
lake env lean "$scratch/Audit.lean"
lake env lean SequentialAudit.lean

# This standard declaration serves as a negative control outside the allowlist.
printf 'import AxiomPolicy\nnoncomputable def unexpectedDependency := @sorryAx\n#check_axioms unexpectedDependency\n' > "$scratch/Reject.lean"
if lake env lean "$scratch/Reject.lean" > "$scratch/rejection.log" 2>&1; then
  echo "Axiom policy accepted its negative control" >&2
  exit 1
fi
if ! grep -q "unexpected axiom dependencies for 'unexpectedDependency':.*sorryAx" "$scratch/rejection.log"; then
  cat "$scratch/rejection.log" >&2
  exit 1
fi
echo "Axiom policy accepted the audited proofs and rejected its negative control."
lake env leanchecker SequentialModel
lake env leanchecker SequentialPurge
lake env leanchecker SnapshotTable
lake env leanchecker CompactionRead
lake env leanchecker PackedTable
lake env leanchecker Recovery
lake env leanchecker Manifest
lake env leanchecker DiskTable
lake env leanchecker DiskPublicationModel
lake env leanchecker WalBoundary
lake env leanchecker WalBoundaryModel
lake env lean --run SequentialChecks.lean
lake env lean --run PackedTableChecks.lean
lake exe alvoki-disk-checks
