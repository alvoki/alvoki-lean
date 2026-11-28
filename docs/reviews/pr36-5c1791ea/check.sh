#!/usr/bin/env bash
# Rebuild the input modules from the reviewed commit in a scratch directory.
set -euo pipefail
review=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$review" rev-parse --show-toplevel)
pin=5c1791eaaf0aa4a7ec3c5778fbf0d7265ecdb032
test "$(git -C "$repo" rev-parse "$pin^{tree}")" = 8273f35cc46e9333f0098ac66270284063f6bfb1
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
git -C "$repo" archive "$pin" lean tests/l0-audit | tar -x -C "$out"
cd "$out/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} ]]; then
  export ELAN_HOME="$ALVOKI_TOOLCHAINS/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
export PATH="$prefix/bin:$PATH"
lean --version
lake build Alvoki.Experiments.WAL.Segmented.Native Alvoki.Checks.Audit.AxiomPolicy
inputs="$out/tests/l0-audit"
export LEAN_PATH="$out:$PWD/.lake/build/lib/lean"
lean --root="$inputs" -o "$out/OwnedRoleModel.olean" "$inputs/OwnedRoleModel.lean"
leanchecker OwnedRoleModel
lean --root="$review" -o "$out/Adversarial.olean" "$review/Adversarial.lean"
leanchecker Adversarial
echo "Adversarial.lean: elaboration, axiom checks and kernel replay passed"
lean --run "$inputs/PhaseInstallProbe.lean"
# Change just the mutex delivered to consume in the successful retry case.
python3 - "$inputs/PhaseInstallProbe.lean" "$out/ForeignMutex.lean" "$out/CopiedPhase.lean" <<'PY'
from pathlib import Path
import sys

original = Path(sys.argv[1]).read_text()
site = 'unless ← consume slot retried do'
assert original.count(site) == 1
Path(sys.argv[2]).write_text(original.replace(site,
    'let otherMutex ← Std.BaseMutex.new\n  unless ← consume slot (retried.1, otherMutex) do'))
Path(sys.argv[3]).write_text(original.replace(site,
    'let copiedPhase ← IO.mkRef (← retried.1.get)\n  unless ← consume slot (copiedPhase, retried.2) do'))
PY
lean --run "$out/ForeignMutex.lean"
lean --run "$out/CopiedPhase.lean"
echo "Native probe: original, foreign mutex and copied phase all exited successfully"
