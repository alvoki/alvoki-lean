#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
    printf 'Usage: %s NEW_RESULTS_DIR [WRITES [TRIALS]]\n' "$0" >&2
    exit 2
fi

experiment=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$experiment/../.." && pwd)
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-$repo/../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export RUSTUP_HOME="$toolchains/rustup"
export CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
export LC_ALL=C

base=097d8b5
writes=${2:-64}
trials=${3:-7}
if [[ -e $1 || -L $1 ]]; then
    printf 'Results path already exists: %s\n' "$1" >&2
    exit 2
fi
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT

git -C "$repo" archive "$base" lean | tar -x -C "$build"
git -C "$build" apply --unidiff-zero "$experiment/lean-adapter.patch"
cp "$experiment/"{LatencyFixture.lean,LatencyMicro.lean} "$build/lean/"
cat >> "$build/lean/lakefile.toml" <<'TOML'

[[lean_exe]]
name = "latency-fixture"
root = "LatencyFixture"

[[lean_exe]]
name = "latency-micro"
root = "LatencyMicro"
TOML

rustc +1.95.0 -O --edition=2024 "$experiment/helper.rs" -o "$build/helper"
(cd "$build/lean" && lake build alvoki-disk-write latency-fixture latency-micro) >&2
python3 "$experiment/check_helper.py" "$build" | tee "$build/failure-report.txt"
python3 "$experiment/time_experiment.py" "$build" "$writes" "$trials" | tee "$build/report.txt"

{
    printf 'Baseline commit %s\n' "$(git -C "$repo" rev-parse "$base")"
    date -u '+Run completed %Y-%m-%d %H:%M:%S UTC'
    printf 'Affinity %s\n' "$(head -n 1 "$build/report.txt")"
    uname -srmo
    if command -v lscpu >/dev/null; then
        lscpu | awk '/^CPU\(s\)|^Model name|^Hypervisor vendor/'
    fi
    printf 'Temporary filesystem %s\n' "$(stat -f -c '%T' "$build")"
    (cd "$build/lean" && lean --version)
    rustc +1.95.0 -V
    sync --version | sed -n '1p'
    python3 --version
    printf 'Trials %s\nTimed writes per trial %s\n' "$trials" "$writes"
} > "$build/environment.txt"

mkdir -- "$1"
cp "$build/"{latency-raw.csv,micro-raw.csv,rust-stages.csv,failure-report.txt,report.txt,environment.txt} "$1/"
