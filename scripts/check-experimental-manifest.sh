#!/usr/bin/env bash
# Kernel and axiom checks, plus an end-to-end Linux adapter fixture.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  if [[ ${2:-} == native ]]; then
    lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
    sources+=("$out/$module.c")
  else
    lean -o "$out/$module.olean" "$module.lean"
  fi
  leanchecker "${module//\//.}"
}
blob=Alvoki/Experiments/DurableBlob
manifest=Alvoki/Experiments/Manifest
compile Alvoki/Codec/Block native
compile Alvoki/Codec/WordChecksum native
compile Alvoki/Kernel/BlockContracts
compile Alvoki/Codec/ByteWords
for module in Contract Protocol Native; do
  compile "$blob/$module" native
done
compile "$blob/Proofs"
compile "$blob/WPComparison"
compile "$blob/Trace"
compile "$manifest/Basic" native
compile "$manifest/Proofs"
compile "$manifest/RefinementExperiment"
compile "$manifest/NativeTests" native
compile Alvoki/Checks/Audit/AxiomPolicy
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.DurableBlob.WPComparison
import Alvoki.Experiments.Manifest.RefinementExperiment
#check_axioms DurableBlob.WPComparison.legacy
#check_axioms DurableBlob.WPComparison.current
#check_axioms DurableBlob.WPComparison.nested_result
#check_axioms DurableBlob.WPComparison.nested_stop
#check_axioms DurableBlob.publish_stable
#check_axioms DurableBlob.reopen_binding
#check_axioms DurableBlob.Run.refines
#check_axioms DurableBlob.Run.healthy_open
#check_axioms DurableBlob.LinuxEffects.reopen
#check_axioms DurableBlob.LinuxEffects.reopenSettles
#check_axioms DurableBlob.LinuxEffects.reopenInterrupted
#check_axioms DurableBlob.LinuxEffects.publish
#check_axioms DurableBlob.LinuxEffects.publishUncertain
#check_axioms DurableBlob.LinuxEffects.publishUncertainAdmits
#check_axioms DurableBlob.LinuxEffects.reopenFailedAdmits
#check_axioms DurableBlob.LinuxEffects.reopenAgain
#check_axioms L0Manifest.RefinementExperiment.typedRetry
#check_axioms L0Manifest.RefinementExperiment.typedRetry_same
#check_axioms L0Manifest.RefinementExperiment.lostSuccess
#check_axioms L0Manifest.decode_encode
#check_axioms L0Manifest.publish_valid
#check_axioms L0Manifest.reopen_encoded
#check_axioms L0Manifest.trace_refines
#check_axioms L0Manifest.decode_rejects_checksum
LEAN
cc -O2 -fPIC -I"$prefix/include" "${sources[@]}" native/fsync.c \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/test-manifest"
"$out/test-manifest"
