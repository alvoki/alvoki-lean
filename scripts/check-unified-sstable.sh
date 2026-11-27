#!/usr/bin/env bash
# Build the opt-in unified SSTable prototype and exercise the native reader.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
bash "$repo/benchmarks/sstable/build-crc32c.sh" "$out" "$prefix"
table=Alvoki/Experiments/SSTable
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
  leanchecker "${module//\//.}"
  sources+=("$out/$module.c")
}
compile Alvoki/Codec/Block
for module in Contract Search Core Builder Native FixedFormat FixedBuilder \
    UnifiedFormat UnifiedIntegrity UnifiedNativeIntegrity UnifiedBuilder UnifiedReader UnifiedNative UnifiedFixtures; do
  compile "$table/$module"
done
cc -O2 -DNDEBUG -fPIC -I"$prefix/include" "${sources[@]}" native/sstable.c native/fsync.c \
  "$out/libalvoki_crc32c.a" -lstdc++ -L"$prefix/lib/lean" \
  -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/test-unified-sstable"
"$out/test-unified-sstable" "$@"
