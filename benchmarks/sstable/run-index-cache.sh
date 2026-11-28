#!/usr/bin/env bash
# Capture all rows of the ALVSST05 and ALVSST06 index cache experiment.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LC_ALL=C

(cd lean && lake build sstableIndexCacheBench) >&2
sample=$(mktemp)
trap 'rm -f "$sample"' EXIT
first=true
for replicate in 1 2; do
  for rows in 65537 1000000 4000000; do
    for target in 4096:1024 4096:4096 16384:16384; do
      data=${target%:*}
      index=${target#*:}
      lean/.lake/build/bin/sstableIndexCacheBench "$rows" "$data" "$index" 65536 > "$sample"
      if "$first"; then
        head -n 1 "$sample" | sed 's/^/replicate,/'
        first=false
      fi
      tail -n +2 "$sample" | sed "s/^/${replicate},/"
    done
  done
done
