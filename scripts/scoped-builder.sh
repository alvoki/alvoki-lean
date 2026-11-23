#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Also builds the stock and previous guarded-inline controls.
bash scripts/fixed-copy.sh
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
(
  cd lean
  # Fail closed when the generated representation no longer matches the lowering.
  python3 runtime-experiment/check-builder-abi.py
  for variant in scoped scoped-branchless; do
    extra=()
    if [[ "$variant" == scoped-branchless ]]; then extra=(-DBUILDER_BRANCHLESS -DBUILDER_FUSED_DENSE); fi
    lake env leanc -O3 -DNDEBUG "${extra[@]}" -c runtime-experiment/scoped-builder.c -o ".lake/$variant.o"
    lake env leanc @.lake/build/bin/alvoki-merge-phases.rsp ".lake/$variant.o"       -Wl,--wrap=lp_alvoki_Alvoki_MergePhases_ReplayPlan_write       -Wl,--wrap=lp_alvoki_Alvoki_Packed_merge       -Wl,--wrap=lp_alvoki_Alvoki_MergePhases_denseRewrite       -o ".lake/build/bin/alvoki-merge-phases-$variant"
  done
)
python3 benchmarks/scoped_builder.py "$@"
