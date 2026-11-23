#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
toolchains=$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)
export ELAN_HOME="$toolchains/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LC_ALL=C

(cd lean && lake build alvoki-disk-write) >&2
python3 -c 'import os, sys; os.sched_setaffinity(0, {min(os.sched_getaffinity(0))}); os.execv(sys.argv[1], sys.argv[1:])' \
  lean/.lake/build/bin/alvoki-disk-write "$@"
