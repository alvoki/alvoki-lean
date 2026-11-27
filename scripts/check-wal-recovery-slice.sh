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
wal=Alvoki/Experiments/WAL
mkdir -p "$scratch/$wal/Proofs" "$scratch/Alvoki/Checks/Audit"
lean -o "$scratch/$wal/SingleFile.olean" -c "$scratch/single.c" "$wal/SingleFile.lean"
leanchecker Alvoki.Experiments.WAL.Recovery Alvoki.Experiments.WAL.SingleFile
lean -o "$scratch/$wal/CrashModel.olean" "$wal/CrashModel.lean"
leanchecker Alvoki.Experiments.WAL.CrashModel
for proof in Marker Scan Append Persistence Client; do
  lean -o "$scratch/$wal/Proofs/$proof.olean" "$wal/Proofs/$proof.lean"
  leanchecker "Alvoki.Experiments.WAL.Proofs.$proof"
done
audit=Alvoki/Checks/Audit/AxiomPolicy
lean -o "$scratch/$audit.olean" "$audit.lean"
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.WAL.Proofs.Scan
import Alvoki.Experiments.WAL.Proofs.Marker
import Alvoki.Experiments.WAL.Proofs.Client
open WalRecoverySlice
#check_axioms Persistence.Confirmed.recover
#check_axioms Persistence.Confirmed.settled
#check_axioms Persistence.repeats_healthyReopen
#check_axioms Persistence.appendBatch_effects
#check_axioms decodeMarker_bad_check
#check_axioms scan_encodeFrames
#check_axioms scan_preserves_encoded_prefix
#check_axioms scan_torn_encodeFrames
#check_axioms decodeMarker_encode
#check_axioms selectMarker_one
#check_axioms selectMarker_both
LEAN
lean --run Alvoki/Checks/Tests/WalRecoverySlice.lean
lean -c "$scratch/files.c" Alvoki/Checks/Tests/WalRecoveryFiles.lean
# PIC keeps Lean's initialized runtime globals shared with libleanshared.
cc -O1 -fPIC -I"$prefix/include" "$scratch/recovery.c" "$scratch/single.c" "$scratch/files.c" \
  native/fsync.c -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared \
  -o "$scratch/files"
"$scratch/files"
# Bash counts 1024-byte blocks outside POSIX mode. Convert SIGXFSZ into EFBIG.
( set +o posix; trap '' XFSZ; ulimit -f 1; "$scratch/files" --partial-write )
