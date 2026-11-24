#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan" RUSTUP_HOME="$toolchains/rustup" CARGO_HOME="$toolchains/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
export LC_ALL=C

(
    cd lean
    lake build alvoki-wide-accessors
    build=.lake/wide-accessors
    mkdir -p "$build"
    experiment=runtime-experiment/wide-accessors
    source=.lake/build/ir/WideAccessorBench.c
    response=.lake/build/bin/alvoki-wide-accessors.rsp
    original='^".*/WideAccessorBench\.c\.o\.export"$'
    if [[ $(grep -c "$original" "$response" || true) != 1 ]]; then
        echo "expected exactly one WideAccessorBench object in $response" >&2
        exit 1
    fi
    for variant in shifts shifts-assume memcpy memcpy-assume; do
        wide_memcpy=0
        wide_assume=0
        [[ "$variant" == memcpy* ]] && wide_memcpy=1
        [[ "$variant" == *-assume ]] && wide_assume=1
        object="$build/$variant.o"
        lake env leanc -O3 -DNDEBUG -DLEAN_EXPORTING -ffunction-sections -fdata-sections \
            -fPIC -fvisibility=hidden -fstack-clash-protection -ffp-contract=off \
            -include "$experiment/accessors.h" -DALVOKI_WIDE_MEMCPY="$wide_memcpy" \
            -DALVOKI_WIDE_ASSUME="$wide_assume" -c "$source" -o "$object"
        link="$build/link.rsp"
        sed "s@$original@\"$object\"@" "$response" > "$link"
        lake env leanc "@$link" -o "$build/$variant"
    done
)
(
    cd rust
    rustc --edition=2024 -C opt-level=3 ../lean/runtime-experiment/wide-accessors/control.rs \
        -o ../lean/.lake/wide-accessors/rust
)
python3 benchmarks/wide_accessors.py "$@"
