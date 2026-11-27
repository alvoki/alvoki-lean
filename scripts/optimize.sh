#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
(cd rust && cargo build --release)
(cd lean && lake build alvoki-opt OptProofs && lake env leanchecker Alvoki.Kernel.PackedSearchContracts)
python3 benchmarks/optimize.py "$@"
