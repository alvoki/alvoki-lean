#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
(
  cd rust
  cargo build --release --bin alvoki-native --bin alvoki-packed
  cargo rustc --release --bin alvoki-native --target-dir target/scalar -- -C no-vectorize-loops -C no-vectorize-slp
)
(cd lean && lake -v build alvoki-native)
python3 benchmarks/native.py "$@"
