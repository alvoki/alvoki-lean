#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

(cd lean && lake build alvoki-compaction)
(cd rust && cargo build --release --bin alvoki-compaction)
for arg in "$@"; do
  [[ "$arg" == --fixed-copy ]] || continue
  (
    cd lean
    output=.lake/compaction-inline
    python3 runtime-experiment/inline.py alvoki-compaction "$output" Compaction
    lake env leanc -O3 -DNDEBUG -DLEAN_EXPORTING -ffunction-sections -fdata-sections \
      -fPIC -fvisibility=hidden -fstack-clash-protection -ffp-contract=off \
      -c "$output/Compaction.c" -o "$output/Compaction.o"
    lake env leanc "@$output/link.rsp" -o .lake/build/bin/alvoki-compaction-fixed
  )
  break
done
python3 benchmarks/compaction.py "$@"
