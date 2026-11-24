#!/usr/bin/env bash
set -euo pipefail
archive=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$archive/../../../.." && pwd)
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-$repo/../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export PYTHONPATH="$repo/benchmarks"
export PYTHONDONTWRITEBYTECODE=1 LC_ALL=C

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cp "$repo/lean/lean-toolchain" "$archive/ReplayLifetimes.lean" "$scratch/"
python3 - "$scratch/lakefile.toml" "$repo/lean" <<'PY'
import json
from pathlib import Path
import sys

Path(sys.argv[1]).write_text(
    'name = "alvoki_replay_lifetimes"\n'
    '[[require]]\nname = "alvoki"\npath = ' + json.dumps(sys.argv[2]) + '\n'
    '[[lean_exe]]\nname = "replay-lifetimes"\nroot = "ReplayLifetimes"\n'
)
PY
(cd "$scratch" && lake build replay-lifetimes) >&2
python3 "$archive/compare.py" "$scratch/.lake/build/bin/replay-lifetimes" "$@"
