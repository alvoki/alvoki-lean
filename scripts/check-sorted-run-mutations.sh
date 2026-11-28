#!/usr/bin/env bash
# Reject three deliberate violations in the executable code of HEAD.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-$repo/../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
git -C "$repo" archive HEAD lean | tar -xf - -C "$scratch"
cd "$scratch/lean"

reject() {
  local label=$1 file=$2 old=$3 new=$4 target=$5 proof=$6
  cp "$file" "$scratch/original"
  python3 - "$file" "$old" "$new" <<'PY'
import sys
from pathlib import Path

path, old, new = sys.argv[1:]
file = Path(path)
source = file.read_text()
if source.count(old) != 1:
    raise SystemExit("Mutation must match exactly once")
file.write_text(source.replace(old, new))
PY
  if lake build "$target" >"$scratch/build.log" 2>&1; then
    echo "Unexpectedly accepted: $label" >&2
    exit 1
  fi
  if ! rg -m 1 "^error: $proof:[0-9]+:[0-9]+:" "$scratch/build.log"; then
    cat "$scratch/build.log" >&2
    exit 1
  fi
  echo "Rejected: $label"
  cp "$scratch/original" "$file"
}

run=Alvoki/Experiments/SortedRun
reject 'older row wins on equal keys' "$run/Merge.lean" \
  'else (some a, ⟨.unread nextA, .unread nextB⟩)' \
  'else (some b, ⟨.unread nextA, .unread nextB⟩)' \
  Alvoki.Experiments.SortedRun.Proofs "$run/Proofs.lean"

reject 'EOF with a nonempty newer run' "$run/Merge.lean" \
  '| some (a, next), none => (some a, ⟨.unread next, .buffered none⟩)' \
  '| some (_, next), none => (none, ⟨.unread next, .buffered none⟩)' \
  Alvoki.Experiments.SortedRun.Proofs "$run/Proofs.lean"

table=Alvoki/Experiments/SSTable
reject 'writer masks the required input failure as success' "$table/Native.lean" \
  '    throwThe ε error' '    pure 0' \
  Alvoki.Checks.Tests.SortedRunEffects "$table/Proofs/NativeWrite.lean"
