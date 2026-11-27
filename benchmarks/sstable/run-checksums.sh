#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
revision=270c2daedb55d6c756080254e8a17ae95319790e
if [[ -n ${LEAN_ZLIB_DIR:-} ]]; then
  zlib_dir=$(cd "$LEAN_ZLIB_DIR" && pwd)
else
  zlib_dir="$out/lean-zlib"
  git init --quiet "$zlib_dir"
  git -C "$zlib_dir" fetch --quiet --depth 1 https://github.com/kim-em/lean-zlib.git "$revision"
  git -C "$zlib_dir" checkout --quiet --detach FETCH_HEAD
fi
if [[ $(git -C "$zlib_dir" rev-parse HEAD) != "$revision" ]] ||
    ! git -C "$zlib_dir" diff --quiet HEAD -- Zlib/Checksum.lean c/zlib_ffi.c; then
  echo "Expected clean lean-zlib sources at $revision." >&2
  exit 1
fi
if [[ -n ${CRC32C_DIR:-} ]]; then
  CRC32C_DIR=$(cd "$CRC32C_DIR" && pwd)
  export CRC32C_DIR
fi

cd "$root/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export LC_ALL=C LEAN_PATH="$out"
prefix=$(lean --print-prefix)
lean_bin="$prefix/bin/lean"
bash "$root/benchmarks/sstable/build-crc32c.sh" "$out" "$prefix"
sources=()
compile() {
  local module=$1
  local source_root=${2:-$root/lean}
  mkdir -p "$out/$(dirname "$module")"
  "$lean_bin" --root="$source_root" -o "$out/$module.olean" -c "$out/$module.c" \
    "$source_root/$module.lean"
  sources+=("$out/$module.c")
}
compile Zlib/Checksum "$zlib_dir"
compile Alvoki/Codec/Block
table=Alvoki/Experiments/SSTable
for module in Contract Search Core UnifiedIntegrity UnifiedNativeIntegrity; do
  compile "$table/$module"
done
"$lean_bin" --root="$root" -c "$out/checksums.c" "$root/benchmarks/sstable/Checksums.lean"
cc -O3 -DNDEBUG -fPIC -I"$prefix/include" "${sources[@]}" "$out/checksums.c" \
  "$zlib_dir/c/zlib_ffi.c" "$out/libalvoki_crc32c.a" -lstdc++ -lz \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/checksums"
affinity=$(taskset -pc "$$")
affinity=${affinity##*: }
first_cpu=${affinity%%[-,]*}
taskset -c "${BENCH_CPU:-$first_cpu}" "$out/checksums"
