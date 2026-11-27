#!/usr/bin/env bash
# Build the pinned Google CRC32C archive on Linux x86-64.
set -euo pipefail

build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT

if [[ $(uname -s) != Linux || $(uname -m) != x86_64 ]]; then
  echo "The CRC32C build helper requires Linux x86-64." >&2
  exit 1
fi
archive=$1
out=$build_dir
include=$2
bridge=$3
revision=02e65f4fd3065d27b2e29324800ca6d04df16126
mkdir -p "$out"
source_dir="$out/google-crc32c"
git init --quiet "$source_dir"
git -C "$source_dir" fetch --quiet --depth 1 https://github.com/google/crc32c.git "$revision"
git -C "$source_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$source_dir" rev-parse HEAD)" = "$revision"

# Compile the accelerated translation unit separately so that upstream's CPU
# dispatch can safely choose its portable implementation on older processors.
config="$out/crc32c"
mkdir -p "$config"
cat > "$config/crc32c_config.h" <<'HEADER'
#define BYTE_ORDER_BIG_ENDIAN 0
#define HAVE_BUILTIN_PREFETCH 1
#define HAVE_MM_PREFETCH 1
#define HAVE_SSE42 1
#define HAVE_ARM64_CRC32C 0
#define HAVE_STRONG_GETAUXVAL 1
#define HAVE_WEAK_GETAUXVAL 0
HEADER

flags=(-O3 -DNDEBUG -fPIC -std=c++11 -I"$source_dir/include" -I"$out")
c++ "${flags[@]}" -c "$source_dir/src/crc32c.cc" -o "$out/crc32c.o"
c++ "${flags[@]}" -c "$source_dir/src/crc32c_portable.cc" -o "$out/crc32c_portable.o"
c++ "${flags[@]}" -msse4.2 -c "$source_dir/src/crc32c_sse42.cc" -o "$out/crc32c_sse42.o"
cc -O3 -DNDEBUG -fPIC -I"$include" -I"$source_dir/include" \
  -c "$bridge" -o "$out/alvoki_crc32c.o"
ar rcs "$out/libalvoki_crc32c.a" "$out/alvoki_crc32c.o" "$out/crc32c.o" \
  "$out/crc32c_portable.o" "$out/crc32c_sse42.o"
mv "$out/libalvoki_crc32c.a" "$archive"
