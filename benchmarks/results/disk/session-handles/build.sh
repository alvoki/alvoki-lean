#!/usr/bin/env bash
set -euo pipefail
suite_dir=$(cd "$(dirname "$0")" && pwd)
checkout=$(cd "$1" && pwd)
name=$2
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-$checkout/../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$checkout/lean"
lake build alvoki-disk-checks >&2
lake env lean --root="$suite_dir" -c "$suite_dir/$name.c" "$suite_dir/Bench.lean"
lake env leanc -O3 -DNDEBUG -c "$suite_dir/$name.c" -o "$suite_dir/$name.o"
{
  printf '"%s"\n' "$suite_dir/$name.o"
  tail -n +2 .lake/build/bin/alvoki-disk-checks.rsp
} > "$suite_dir/$name.rsp"
lake env leanc -o "$suite_dir/$name" @"$suite_dir/$name.rsp"
