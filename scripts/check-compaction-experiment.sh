#!/usr/bin/env bash
# Check the research proofs against the main-branch component interfaces.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  lean -o "$out/$module.olean" "$module.lean"
}

for module in Codec/{Block,WordChecksum} Kernel/BlockContracts Codec/ByteWords \
  Experiments/DurableBlob/{Contract,Protocol,Native,Trace,Proofs} \
  Experiments/Manifest/{Basic,Proofs} Experiments/WAL/Segmented/Contract \
  Experiments/L0/{Basic,Proofs,ComponentContract,Refinement,RecoveryChoices} \
  Checks/Audit/AxiomPolicy; do
  compile "Alvoki/$module"
done

lean --root=../tests/compaction -o "$out/CompactionProof.olean" \
  ../tests/compaction/CompactionProof.lean
leanchecker CompactionProof
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import CompactionProof

open ExperimentalL0.CompactionExperiment
#check_axioms mergeReference_ordered
#check_axioms mergeReference_lookup
#check_axioms overlay_replace
#check_axioms publicationChoices
#check_axioms install_compacted
#check_axioms merge_recovery
#check_axioms manifest_effect_recovery
LEAN
