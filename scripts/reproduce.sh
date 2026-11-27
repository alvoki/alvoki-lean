#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
export LC_ALL=C

(cd rust && time cargo build --release)
(cd lean && time lake build && time lake build Proofs && time lake env lean Alvoki/Checks/Audit/Audit.lean && time lake env leanchecker Alvoki.Kernel.BlockContracts)
time "$toolchains/verus-x86-linux/verus" verus/search.rs
python3 benchmarks/run.py "$@"
