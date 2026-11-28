#!/usr/bin/env bash
# Reproduce the pinned counterexample and check the proposed role model.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} ]]; then
  export ELAN_HOME="$(cd "$ALVOKI_TOOLCHAINS/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
lake build Alvoki.Experiments.WAL.Segmented.Native Alvoki.Checks.Audit.AxiomPolicy
audit=../tests/l0-audit
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:$PWD/.lake/build/lib/lean"
for module in PhaseMemoryCounterexample OwnedRoleModel; do
  lean --root="$audit" -o "$out/$module.olean" "$audit/$module.lean"
  leanchecker "$module"
done

lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import OwnedRoleModel
open L0Audit.OwnedRoleModel
#check_axioms realized
#check_axioms reached
#check_axioms mutexFailure
#check_axioms reuse
LEAN

lean --run "$audit/PhaseInstallProbe.lean"
