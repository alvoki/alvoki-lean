#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$root/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export LC_ALL=C LEAN_PATH="$out"
prefix=$(lean --print-prefix)
lean_bin="$prefix/bin/lean"
lake build crc32cArchive >&2
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  "$lean_bin" -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
  sources+=("$out/$module.c")
}
compile Alvoki/Codec/Block
compile Alvoki/Codec/CRC32C
table=Alvoki/Experiments/SSTable
for module in Contract Search Core UnifiedIntegrity UnifiedNativeIntegrity; do
  compile "$table/$module"
done
"$lean_bin" --root="$root" -c "$out/checksums.c" "$root/benchmarks/sstable/Checksums.lean"
cc -O3 -DNDEBUG -fPIC -I"$prefix/include" "${sources[@]}" "$out/checksums.c" \
  ".lake/build/native/libalvoki_crc32c.a" -lstdc++ \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/checksums"
affinity=$(taskset -pc "$$")
affinity=${affinity##*: }
first_cpu=${affinity%%[-,]*}
taskset -c "${BENCH_CPU:-$first_cpu}" "$out/checksums"
