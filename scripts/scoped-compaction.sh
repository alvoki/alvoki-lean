#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Build and check the unchanged stock, Rust and guarded fixed-copy controls.
bash scripts/compaction.sh --fixed-copy
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
(
  cd lean
  python3 runtime-experiment/check-compaction-abi.py
  for variant in scoped scoped-branchless; do
    flags=()
    if [[ "$variant" == scoped-branchless ]]; then flags=(-DCOMPACTION_BRANCHLESS); fi
    lake env leanc -O3 -DNDEBUG "${flags[@]}" -c runtime-experiment/scoped-compaction.c \
      -o ".lake/compaction-$variant.o"
    lake env leanc @.lake/build/bin/alvoki-compaction.rsp ".lake/compaction-$variant.o" \
      -Wl,--wrap=lp_alvoki_Alvoki_Compaction_compact \
      -Wl,--wrap=lp_alvoki_Alvoki_Compaction_compactSpans \
      -o ".lake/build/bin/alvoki-compaction-$variant"
  done
)
python3 benchmarks/scoped_compaction.py "$@"
