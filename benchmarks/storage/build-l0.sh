#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
worktree=${1:?usage: build-l0.sh NEW_WORKTREE [COMMIT]}
pin=${2:-791940352e0068a9e303236c8b50b22d638fa139}
[[ $pin =~ ^[0-9a-f]{40}$ ]] || { echo "Pass a full commit SHA." >&2; exit 1; }
git -C "$repo" worktree add --detach "$worktree" "$pin"
cd "$worktree"
mkdir -p lean/Alvoki/Bench/Storage
cp "$repo"/lean/Alvoki/Bench/Storage/{Support,L0}.lean lean/Alvoki/Bench/Storage/
cp "$repo/lean/native/storage_bench_metrics.c" lean/native/
sed -n '/^target storageBenchMetricsO /,/^lean_exe storageBench /p' "$repo/lean/lakefile.lean" |
  sed '$d' >> lean/lakefile.lean
cat >> lean/lakefile.lean <<'LAKE'

lean_lib StorageBenchL0Candidate where
  globs := #[`Alvoki.Experiments.L0.+]

lean_exe storageL0Bench where
  root := `Alvoki.Bench.Storage.L0
LAKE
cd lean
lake -v build storageL0Bench
