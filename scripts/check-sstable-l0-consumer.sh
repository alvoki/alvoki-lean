#!/usr/bin/env bash
# Check the SSTable boundary against the selected PR #5 consumer.
set -euo pipefail

repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo"
l0_ref=${1:-69b65a9d6bdcbe37acb44c28b13dffe8499cbb41}
if ! git cat-file -e "$l0_ref^{commit}" 2>/dev/null; then
  echo "Fetch the PR #5 branch (experiments/l0-slice) before running this check." >&2
  exit 1
fi

toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
git archive HEAD lean | tar -xf - -C "$scratch"
modules=lean/Alvoki/Experiments/L0
mkdir -p "$scratch/$modules"
for module in Basic Codecs TableRows TableSchedule CodecProofs ComponentContract ReadErrors; do
  git show "$l0_ref:$modules/$module.lean" > "$scratch/$modules/$module.lean"
done
cp tests/sstable-l0/*.lean "$scratch/$modules/"

# Adapt the two open entry points to the checked SSTable API. Keep PR #5's
# real scoped acquisition, codec, row supplier and lookup loop.
python3 - "$scratch/$modules/TableSchedule.lean" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
schedule = path.read_text()
for old, new in [
    ("import Alvoki.Experiments.SSTable.Native",
     "import Alvoki.Experiments.SSTable.UnifiedNative"),
    ("(source : ImmutableSSTable.Source m)",
     "(source : ImmutableSSTable.Source m) (expectedId : UInt64)"),
    ("ImmutableSSTable.openTable source",
     "ImmutableSSTable.Unified.openTableChecked source "
     "Alvoki.CRC32C.extend expectedId"),
    ("nativeTableAction (handle : IO.FS.Handle)",
     "nativeTableAction (handle : IO.FS.Handle) (expectedId : UInt64)"),
    ("(ImmutableSSTable.handleSource handle) use",
     "(ImmutableSSTable.handleSource handle) expectedId use"),
]:
    if schedule.count(old) != 1:
        raise SystemExit(f"Unexpected PR #5 adapter source: {old}")
    schedule = schedule.replace(old, new)
path.write_text(schedule)
PY

cd "$scratch/lean"
cat >> lakefile.lean <<'LEAN'


lean_lib L0ConsumerCheck where
  globs := #[`Alvoki.Experiments.L0.+]

lean_exe l0ConsumerCheck where
  root := `Alvoki.Experiments.L0.SSTableConsumerCheck
LEAN
lake build Alvoki.Experiments.L0.SSTableConsumerProof
lake env leanchecker Alvoki.Experiments.L0.SSTableConsumerProof
lake exe l0ConsumerCheck
