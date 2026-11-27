#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LC_ALL=C

cd lean
lake build
cd ..

bash scripts/check-experimental-manifest.sh
bash scripts/check-wal-recovery-slice.sh
bash scripts/check-segmented-wal.sh
bash scripts/check-immutable-sstable.sh
if [[ -f scripts/check-native-l0.sh ]]; then
  bash scripts/check-native-l0.sh
fi
if [[ -f scripts/check-experimental-l0.sh ]]; then
  bash scripts/check-experimental-l0.sh
fi
python3 scripts/check-markdown-links.py
