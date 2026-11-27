#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export LEAN_PATH="$scratch${LEAN_PATH:+:$LEAN_PATH}"
module=Alvoki/Experiments/WAL/Recovery
mkdir -p "$scratch/$(dirname "$module")"
lean -o "$scratch/$module.olean" -c "$scratch/recovery.c" "$module.lean"
leanchecker Alvoki.Experiments.WAL.Recovery
lean --run Alvoki/Checks/Tests/WalRecoverySlice.lean
lean -c "$scratch/files.c" Alvoki/Checks/Tests/WalRecoveryFiles.lean
# PIC keeps Lean's initialized runtime globals shared with libleanshared.
cc -O1 -fPIC -I"$prefix/include" "$scratch/recovery.c" "$scratch/files.c" \
  native/fsync.c -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared \
  -o "$scratch/files"
"$scratch/files"
