#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
tools=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$tools/elan" RUSTUP_HOME="$tools/rustup" CARGO_HOME="$tools/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
(cd rust && cargo build --release --bin alvoki-merge-phases)
(
  cd lean
  lake build alvoki-merge-phases ScopedBytesProofs
  lake env leanchecker ScopedBytesProofs
)
python3 benchmarks/stock_builder.py "$@"
