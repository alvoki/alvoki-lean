#!/usr/bin/env bash
# Kernel-check the L0 interpreter and audit its client refinement.
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
  leanchecker "${module//\//.}"
}
compile Alvoki/Codec/Block
compile Alvoki/Codec/WordChecksum
compile Alvoki/Kernel/BlockContracts
compile Alvoki/Codec/ByteWords
compile Alvoki/Experiments/DurableBlob/Contract
compile Alvoki/Experiments/Manifest/Basic
compile Alvoki/Experiments/WAL/Segmented/Contract
l0=Alvoki/Experiments/L0
for module in Basic ComponentContract Model Client Proofs ComponentProofs Refinement ModelRefinement ReadErrors RecoveryChoices Execution; do
  compile "$l0/$module"
done
compile Alvoki/Checks/Audit/AxiomPolicy
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.L0.Execution
import Alvoki.Experiments.L0.ReadErrors
import Alvoki.Experiments.L0.RecoveryChoices
open ExperimentalL0
#check_axioms decode_encode
#check_axioms encode_size
#check_axioms Model.table_create_refines
#check_axioms Model.table_read_refines
#check_axioms Model.componentLaws
#check_axioms write_refines
#check_axioms flush_refines
#check_axioms recover_refines
#check_axioms get_refines
#check_axioms get_required_error
#check_axioms recover_required_table_error
#check_axioms RecoveryChoices.Retry.opened
#check_axioms RecoveryChoices.Retry.preservesDurability
#check_axioms RecoveryChoices.Retry.afterAppend
#check_axioms RecoveryChoices.Retry.afterPublish
#check_axioms Model.Run.refines
#check_axioms Model.Run.healthy_open
LEAN
lean --run "$l0/Tests.lean"
