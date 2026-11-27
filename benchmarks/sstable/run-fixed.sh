#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export LC_ALL=C
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
  sources+=("$out/$module.c")
}
compile Alvoki/Codec/Block
table=Alvoki/Experiments/SSTable
for module in Contract Search Core Builder Native FixedFormat FixedReader FixedBuilder FixedNative FixedBench; do
  compile "$table/$module"
done
cc -O2 -DNDEBUG -fPIC -I"$prefix/include" "${sources[@]}" native/sstable.c native/fsync.c \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/fixed-sstable-bench"
"$out/fixed-sstable-bench" "${1:-8193}" "${2:-512}" "${3:-3}"
