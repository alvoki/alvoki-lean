#!/usr/bin/env bash
# Check the review-only modules against an isolated export of the pinned candidate.
set -euo pipefail
review=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$review" rev-parse --show-toplevel)
candidate=335bbff012b09d70847b9caef3dbf7be13a53296
tree=867325cb266c85371af7b5b21463f3a974d85ca3
test "$(git -C "$repo" rev-parse "$candidate^{tree}")" = "$tree"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
git -C "$repo" archive "$candidate" lean | tar -x -C "$out"
cd "$out/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} ]]; then
  export ELAN_HOME="$ALVOKI_TOOLCHAINS/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
export PATH="$prefix/bin:$PATH"
"$prefix/bin/lean" --version
lake build Alvoki.Experiments.WAL.Segmented.Native Alvoki.Checks.Audit.AxiomPolicy
mkdir "$out/proofs"
export LEAN_PATH="$out/proofs:$out/lean/.lake/build/lib/lean"
cd "$review"
for module in PhaseMemoryCounterexample PremiseExperiments; do
  "$prefix/bin/lean" -o "$out/proofs/$module.olean" "$module.lean"
  "$prefix/bin/leanchecker" "$module"
  echo "$module passed elaboration, axiom policy and kernel check"
done
