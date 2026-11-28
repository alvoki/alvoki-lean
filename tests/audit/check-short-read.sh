#!/usr/bin/env bash
# Run on Linux with the pinned lean and lake on PATH. Pass either leaf or baseline.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../lean"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
prefix=$(lean --print-prefix)
lake build +Alvoki.Experiments.WAL.SingleFile:c
lake env lean --root="$here" -c "$scratch/probe.c" "$here/PublicProbe.lean"
cc -O1 -fPIC -I"$prefix/include" "$scratch/probe.c" \
  .lake/build/ir/Alvoki/Experiments/WAL/{SingleFile,Recovery}.c \
  native/{fsync,read_dir_checked}.c -L"$prefix/lib/lean" \
  -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$scratch/probe"
cc -shared -fPIC "$here/short.c" -ldl -o "$scratch/short.so"
mkdir "$scratch/db"
probe="$scratch/probe"
dir="$scratch/db"
"$probe" create "$dir"
cp "$dir/segment" "$scratch/before"
result=$(AUDIT_INODE="$dir/segment" LD_PRELOAD="$scratch/short.so" "$probe" open "$dir")
echo "$result"
case "$1" in
  leaf) test "$result" = 'reopen error hardware fault (error code: 5)'
        cmp "$scratch/before" "$dir/segment" ;;
  baseline) test "$result" = 'reopen success [[7]]'
            test "$(stat -c %s "$dir/segment")" = 21 ;;
  *) exit 2 ;;
esac
for i in 1 2; do test "$("$probe" open "$dir")" = 'reopen success [[7]]'; done
