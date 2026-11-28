#!/usr/bin/env bash
# Kernel and axiom checks, plus an end-to-end Linux adapter fixture.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
modules=(
  Alvoki.Codec.{Block,WordChecksum,ByteWords}
  Alvoki.Kernel.BlockContracts
  Alvoki.Experiments.DurableBlob.{Contract,Protocol,Native,Proofs,Trace}
  Alvoki.Experiments.Manifest.{Basic,Proofs,NativeTests}
  Alvoki.Checks.Audit.AxiomPolicy
)
lake build "${modules[@]}"
for module in "${modules[@]}"; do
  lake env leanchecker "$module"
done
lake env lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.Manifest.Proofs
#check_axioms DurableBlob.Run.refines
#check_axioms DurableBlob.Run.refinesReady
#check_axioms DurableBlob.Run.healthy_open
#check_axioms DurableBlob.LinuxEffects.reopen
#check_axioms DurableBlob.LinuxEffects.reopenBinding
#check_axioms DurableBlob.LinuxEffects.reopenHealthy
#check_axioms DurableBlob.LinuxEffects.reopenSettles
#check_axioms DurableBlob.LinuxEffects.reopenInterrupted
#check_axioms DurableBlob.LinuxEffects.publish
#check_axioms DurableBlob.LinuxEffects.publishActive
#check_axioms DurableBlob.LinuxEffects.publishUncertain
#check_axioms DurableBlob.LinuxEffects.publishUncertainAdmits
#check_axioms DurableBlob.LinuxEffects.reopenFailedAdmits
#check_axioms DurableBlob.LinuxEffects.reopenAgain
#check_axioms L0Manifest.decode_encode
#check_axioms L0Manifest.publish_valid
#check_axioms L0Manifest.reopen_encoded
#check_axioms L0Manifest.trace_refines
#check_axioms L0Manifest.decode_rejects_checksum
LEAN
lake exe manifestNativeCheck
