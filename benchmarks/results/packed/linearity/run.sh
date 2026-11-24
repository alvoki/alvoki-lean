#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../../.."
repo=$(pwd)
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LC_ALL=C

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
ref=${ALVOKI_LINEAR_REF:-HEAD}
git archive "$ref" lean | tar -x -C "$scratch"
git -C "$scratch" apply "$here/mark-output.patch"

printf 'Source %s\n' "$(git rev-parse "$ref")"
uname -srmo
printf 'CPU affinity %s\n' "$(taskset -pc $$ | cut -d : -f 2-)"
(
  cd "$scratch/lean"
  lean --version
  lake build alvoki-merge-phases alvoki-compaction alvoki-native
  cp "$here/control.lean" LinearControl.lean
  lean --c=LinearControl.c LinearControl.lean
  leanc -O3 -o linear-control LinearControl.c
  for module in MergePhases Compaction NativeTune; do
    markers=$(rg -c '= lean_sarray_mark_linear\(' ".lake/build/ir/$module.c")
    printf 'Native destination markers in %s: %s\n' "$module" "$markers"
  done
)
python3 "$here/check.py" "$repo" "$scratch/lean" "$@"
