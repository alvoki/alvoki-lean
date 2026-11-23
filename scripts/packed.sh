#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
(cd rust && cargo build --release)
(
  cd lean
  mkdir -p .lake
  lake env leanc -O3 -DNDEBUG -c native/packed.c -o .lake/alvoki-packed.next.o
  if ! cmp -s .lake/alvoki-packed.next.o .lake/alvoki-packed.o; then
    mv .lake/alvoki-packed.next.o .lake/alvoki-packed.o
    rm -f .lake/build/bin/alvoki-packed
  else
    rm .lake/alvoki-packed.next.o
  fi
  lake build alvoki-packed
)
python3 benchmarks/packed.py "$@"
