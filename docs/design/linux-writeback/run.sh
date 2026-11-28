#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 && ! ( $# == 3 && $3 == --compare ) ]]; then
  echo "Usage: bash run.sh {ext4|xfs} {buffered|dsync|direct|direct-dsync} [--compare]" >&2
  exit 2
fi
fs=$1
mode=$2
case "$fs" in ext4|xfs) ;; *) exit 2;; esac
case "$mode" in buffered|dsync|direct|direct-dsync) ;; *) exit 2;; esac

scratch=$(mktemp -d)
container="alvoki-writeback-${scratch##*.}"
cleanup() {
  docker rm -f "$container" >/dev/null 2>&1 || true
  rm -r -- "$scratch"
}
trap cleanup EXIT
truncate -s 1G "$scratch/disk.img"

status=0
timeout 120s docker run --rm --name "$container" --network none \
  -v "$scratch:/experiment" alvoki-writeback-research:local qemu-system-x86_64 \
  -machine q35,accel=tcg -m 768 -smp 2 -display none -serial stdio -monitor none -no-reboot \
  -kernel /guest/kernel -initrd /guest/initramfs \
  -append "console=ttyS0 rdinit=/init panic=1 alvoki.writeback=1 fs=$fs io=$mode loglevel=4" \
  -drive file=/experiment/disk.img,if=virtio,format=raw,cache=none > "$scratch/serial.log" 2>&1 || status=$?
tr -d '\r' < "$scratch/serial.log" > "$scratch/serial.txt"
cat "$scratch/serial.txt"
if [[ $status != 0 ]] || ! grep -qx 'PROBE_COMPLETE' "$scratch/serial.txt"; then
  exit 1
fi

if [[ ${3:-} == --compare ]]; then
  reference="$(dirname -- "${BASH_SOURCE[0]}")/reference/$mode.txt"
  # Compare the measurements and leave variable kernel diagnostics and offsets in the full log.
  grep -E '^(IO_MODE=|(baseline backing|writer pwrite|writer first fsync|cached after failure|page after failed I/O|backing after failure|writer retry fsync|fresh description fsync|peer opened before fault fsync|cached after retry|backing after retry|after page eviction|backing after rewrite):)'     "$scratch/serial.txt" > "$scratch/observed.txt" || true
  if ! diff -u --label "reference ($mode)" --label "observed ($fs $mode)"       "$reference" "$scratch/observed.txt" >&2; then
    echo "Probe completed with different observations. The full serial log is on stdout." >&2
    exit 3
  fi
  echo "Probe observations match the reference ($fs $mode)." >&2
fi
