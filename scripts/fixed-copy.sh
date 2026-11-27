#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
(cd rust && cargo build --release --bin alvoki-merge-phases)
(
  cd lean
  lake build alvoki-merge-phases
  lake env leanc -O3 -DNDEBUG -c runtime-experiment/fixed-copy.c -o .lake/fixed-copy.o
  lake env leanc @.lake/build/bin/alvoki-merge-phases.rsp .lake/fixed-copy.o \
    -Wl,--wrap=lean_byte_array_copy_slice -o .lake/build/bin/alvoki-merge-phases-fixed
  python3 runtime-experiment/inline.py
  for module in Alvoki/Experiments/Merge/MergePhases Alvoki/Codec/PackedRun; do
    lake env leanc -O3 -DNDEBUG -DLEAN_EXPORTING -ffunction-sections -fdata-sections -fPIC -fvisibility=hidden -fstack-clash-protection -ffp-contract=off       -c ".lake/fixed-inline/$module.c" -o ".lake/fixed-inline/$module.o"
  done
  lake env leanc @.lake/fixed-inline/link.rsp -o .lake/build/bin/alvoki-merge-phases-inline
)
python3 benchmarks/fixed_copy.py "$@"
