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
lean -o "$scratch/$wal/Contract.olean" "$wal/Contract.lean"
leanchecker Alvoki.Experiments.WAL.Contract
lean -o "$scratch/$wal/Writeback.olean" "$wal/Writeback.lean"
leanchecker Alvoki.Experiments.WAL.Writeback
for proof in AppendWriteback Marker Scan ScanRepair Append Persistence Client ProcessExit Retry DirtyRetry DirtyAppend TornAppend Execution ReopenWriteback ScheduledExecution Policy NativeRecovery NativeOpen NativeAppend; do
  lean -o "$scratch/$wal/Proofs/$proof.olean" "$wal/Proofs/$proof.lean"
  leanchecker "Alvoki.Experiments.WAL.Proofs.$proof"
done
audit=Alvoki/Checks/Audit/AxiomPolicy
lean -o "$scratch/$audit.olean" "$audit.lean"
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.WAL.Proofs.Scan
import Alvoki.Experiments.WAL.Proofs.Marker
import Alvoki.Experiments.WAL.Proofs.Execution
import Alvoki.Experiments.WAL.Proofs.Policy
import Alvoki.Experiments.WAL.Proofs.TornAppend
import Alvoki.Experiments.WAL.Proofs.ScheduledExecution
import Alvoki.Experiments.WAL.Proofs.ReopenWriteback
import Alvoki.Experiments.WAL.Proofs.NativeAppend
open WalRecoverySlice
#check_axioms scan_damaged_encodeFrames
#check_axioms Persistence.reopen_published_scan_error
#check_axioms Persistence.reopen_substituted_batch
#check_axioms Persistence.reopen_unpublished_suffix
#check_axioms Persistence.reopen_unpublished_batch
#check_axioms Persistence.reopen_missing_published_batch
#check_axioms Persistence.tornAppend_stops
#check_axioms Persistence.tornAppend_dirty
#check_axioms Persistence.Dirty.writeback
#check_axioms Persistence.Run.appendWithWritebacks
#check_axioms Persistence.Run.tornAppendWithWritebacks
#check_axioms Persistence.Run.reopenWithWritebacks
#check_axioms Persistence.reopen_writeback_normalizes
#check_axioms Persistence.appendBatch_withWritebacks
#check_axioms Persistence.Run.refines
#check_axioms Persistence.Run.healthy_open
#check_axioms Persistence.reopen_live_retry
#check_axioms Persistence.repeats_healthyReopen
#check_axioms SingleFile.recover_eq
#check_axioms SingleFile.recover_refines
#check_axioms SingleFile.recoverScheduled_eq
#check_axioms SingleFile.openLocations
#check_axioms SingleFile.openExisting_refines
#check_axioms SingleFile.openExisting_healthy
#check_axioms SingleFile.openExisting_worker
#check_axioms SingleFile.storedPhase_eq
#check_axioms SingleFile.scan_opened
#check_axioms SingleFile.close_opened
#check_axioms SingleFile.appendWorker_eq
#check_axioms SingleFile.openedAppendPhase
#check_axioms SingleFile.append_refines
#check_axioms SingleFile.AppendGuarantee.lostReply
#check_axioms SingleFile.append_rejected
#check_axioms SingleFile.append_closed
#check_axioms SingleFile.append_poisoned
#check_axioms SingleFile.close_poisoned
#check_axioms Persistence.appendPrimitive_refines
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
  native/fsync.c native/read_dir_checked.c native/wal_recovery_fixture.c \
  -Wl,--wrap=alvoki_fsync -Wl,--wrap=readdir \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared \
  -o "$scratch/files"
"$scratch/files"
# Bash counts 1024-byte blocks outside POSIX mode. Convert SIGXFSZ into EFBIG.
( set +o posix; trap '' XFSZ; ulimit -f 1; "$scratch/files" --partial-write )
