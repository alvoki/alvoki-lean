#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

(cd lean && lake build alvoki-compaction alvoki-compaction-cursor)
(cd rust && cargo build --release --bin alvoki-compaction)
python3 benchmarks/stock_v3_cursor.py "$@"
