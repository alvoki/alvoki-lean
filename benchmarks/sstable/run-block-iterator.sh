#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d "$repo/../work/toolchains/elan" ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-"$repo/../work/toolchains"}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

# Use the actual generic merge contract without adding a production dependency.
pin=11543b2b6246dac7fba2789080fdbbe7dc47a174
sorted=lean/Alvoki/Experiments/SortedRun
if ! git -C "$repo" cat-file -e "$pin:$sorted/Merge.lean"; then
  printf 'Fetch PR #33 at %s into the local repository first.\n' "$pin" >&2
  exit 1
fi
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
tar -C "$repo/lean" --exclude=.lake -cf - . | tar -C "$scratch" -xf -
mkdir -p "$scratch/Alvoki/Experiments/SortedRun"
for module in Merge Proofs; do
  git -C "$repo" show "$pin:$sorted/$module.lean" > "$scratch/Alvoki/Experiments/SortedRun/$module.lean"
done
cp "$repo/benchmarks/sstable/BlockIterator.lean" "$scratch/BlockIteratorBenchmark.lean"
if ! grep -Fq 'Alvoki.Experiments.SortedRun.+' "$scratch/lakefile.lean"; then
  cat >> "$scratch/lakefile.lean" <<'LAKE'

lean_lib SortedRunBenchmarkContract where
  globs := #[`Alvoki.Experiments.SortedRun.+]
LAKE
fi
cat >> "$scratch/lakefile.lean" <<'LAKE'

lean_exe blockIteratorBenchmark where
  root := `BlockIteratorBenchmark
LAKE
cd "$scratch"
lake build blockIteratorBenchmark >&2
lake env leanchecker BlockIteratorBenchmark >&2
if (($# == 0)); then
  set -- 50000
fi
for rows in "$@"; do
  .lake/build/bin/blockIteratorBenchmark "$rows"
done
