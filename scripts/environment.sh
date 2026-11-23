#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

date -u '+UTC %Y-%m-%d %H:%M:%S'
uname -srmo
lscpu | awk '/^CPU\(s\)|^Model name|^Hypervisor vendor|^Virtualization type|^L[1-3]/'
for file in cpu.max memory.max; do
  if [[ -r "/sys/fs/cgroup/$file" ]]; then
    printf '%s = ' "$file"
    cat "/sys/fs/cgroup/$file"
  fi
done
python3 --version
