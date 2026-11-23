#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

case "${1:-}" in
  "")
    for suite in reproduce optimize native merge-phases stock-builder fused-merge compaction; do
      bash "scripts/$suite.sh"
    done
    toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
    export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
    export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
    (cd rust && cargo test --release --lib)
    (cd lean && lake build MergeProofs BlockCodec && lake env leanchecker PackedViewProofs &&
      lake env leanchecker MergeProofs && lake env leanchecker BlockCodec &&
      lake env lean --run CoreChecks.lean)
    ;;
  --runtime)
    bash scripts/packed.sh
    # The scoped suite also runs the fixed-copy fixture checks.
    bash scripts/scoped-builder.sh
    bash scripts/compaction.sh --fixed-copy
    ;;
  *)
    echo "Usage: bash scripts/check.sh [--runtime]" >&2
    exit 2
    ;;
esac
