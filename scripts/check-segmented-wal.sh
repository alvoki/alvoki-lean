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
blob=Alvoki/Experiments/DurableBlob
wal=Alvoki/Experiments/WAL
seg="$wal/Segmented"
mkdir -p "$scratch/$blob" "$scratch/$wal/Proofs" "$scratch/$seg/Proofs" "$scratch/Alvoki/Checks/Audit"
lean -o "$scratch/$wal/Recovery.olean" -c "$scratch/recovery.c" "$wal/Recovery.lean"
lean -o "$scratch/$wal/SingleFile.olean" -c "$scratch/single.c" "$wal/SingleFile.lean"
lean -o "$scratch/$seg/Contract.olean" -c "$scratch/contract.c" "$seg/Contract.lean"
lean -o "$scratch/$blob/Contract.olean" -c "$scratch/blob_contract.c" "$blob/Contract.lean"
lean -o "$scratch/$blob/Protocol.olean" -c "$scratch/blob_protocol.c" "$blob/Protocol.lean"
lean -o "$scratch/$seg/Protocol.olean" -c "$scratch/protocol.c" "$seg/Protocol.lean"
lean -o "$scratch/$seg/ControlCodec.olean" -c "$scratch/control_codec.c" "$seg/ControlCodec.lean"
lean -o "$scratch/$seg/Native.olean" -c "$scratch/native.c" "$seg/Native.lean"
leanchecker Alvoki.Experiments.WAL.Segmented.Contract
leanchecker Alvoki.Experiments.WAL.Segmented.Protocol
leanchecker Alvoki.Experiments.WAL.Segmented.ControlCodec
leanchecker Alvoki.Experiments.WAL.Segmented.Native
lean --run "$seg/Tests.lean"
lean -c "$scratch/native_tests.c" "$seg/NativeTests.lean"
cc -O1 -fPIC -I"$prefix/include" "$scratch/recovery.c" "$scratch/single.c" \
  "$scratch/blob_contract.c" "$scratch/blob_protocol.c" \
  "$scratch/contract.c" "$scratch/protocol.c" "$scratch/control_codec.c" "$scratch/native.c" "$scratch/native_tests.c" \
  native/fsync.c native/read_dir_checked.c native/wal_recovery_fixture.c \
  -Wl,--wrap=alvoki_fsync -Wl,--wrap=readdir -Wl,--wrap=alvoki_wal_read_installed -Wl,--wrap=fread -Wl,--wrap=ferror \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared \
  -o "$scratch/native_tests"
"$scratch/native_tests"
# Proofs compose the segmented directory protocol with the existing per-segment model.
lean -o "$scratch/$wal/CrashModel.olean" "$wal/CrashModel.lean"
lean -o "$scratch/$wal/Contract.olean" "$wal/Contract.lean"
lean -o "$scratch/$wal/Writeback.olean" "$wal/Writeback.lean"
for proof in Marker Scan ScanRepair Append Persistence Client ProcessExit Retry DirtyRetry BoundedRead LinuxBoundedRead DirtyAppend TornAppend Execution AppendWriteback ReopenWriteback ScheduledExecution NativeRecovery NativeOpen NativeAppend; do
  lean -o "$scratch/$wal/Proofs/$proof.olean" "$wal/Proofs/$proof.lean"
done
for proof in ControlCodec Layout Model SegmentRecovery ScheduledAppend Child Publication Collect Invariant Artifacts Writeback Bootstrap Rotation Append Reopen Retention Discard Execution NativeReopen NativeControl NativeAppend CompactScan CompactOpen; do
  lean -o "$scratch/$seg/Proofs/$proof.olean" "$seg/Proofs/$proof.lean"
  leanchecker "Alvoki.Experiments.WAL.Segmented.Proofs.$proof"
done
lean --run "$seg/ModelTests.lean"
lean -o "$scratch/Alvoki/Checks/Audit/AxiomPolicy.olean" Alvoki/Checks/Audit/AxiomPolicy.lean
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.WAL.Segmented.Proofs.Artifacts
import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCodec
import Alvoki.Experiments.WAL.Segmented.Proofs.Layout
import Alvoki.Experiments.WAL.Segmented.Proofs.SegmentRecovery
import Alvoki.Experiments.WAL.Segmented.Proofs.ScheduledAppend
import Alvoki.Experiments.WAL.Segmented.Proofs.Child
import Alvoki.Experiments.WAL.Segmented.Proofs.Publication
import Alvoki.Experiments.WAL.Segmented.Proofs.Collect
import Alvoki.Experiments.WAL.Segmented.Proofs.Bootstrap
import Alvoki.Experiments.WAL.Segmented.Proofs.Rotation
import Alvoki.Experiments.WAL.Segmented.Proofs.Append
import Alvoki.Experiments.WAL.Segmented.Proofs.Reopen
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback
import Alvoki.Experiments.WAL.Segmented.Proofs.Retention
import Alvoki.Experiments.WAL.Segmented.Proofs.Discard
import Alvoki.Experiments.WAL.Segmented.Proofs.Execution
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeReopen
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeControl
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeAppend
import Alvoki.Experiments.WAL.Segmented.Proofs.CompactScan
import Alvoki.Experiments.WAL.Segmented.Proofs.CompactOpen
open WalRecoverySlice.Segmented
#check_axioms Recoverable.withUnselectedArtifact
#check_axioms ControlCodec.decode_encode
#check_axioms ControlCodec.canonical_of_decode
#check_axioms ControlCodec.encoded_size
#check_axioms selectedHistory_eq
#check_axioms readSealed_spec
#check_axioms reopen_spec
#check_axioms Child.Recoverable.nativeRecovery
#check_axioms Child.Recoverable.nativeOpen
#check_axioms Child.Recoverable.nativeAppendAfterOpen
#check_axioms Child.Recoverable.nativeReopenTwice
#check_axioms Child.Recoverable.compactReopenTwice
#check_axioms Child.nativeRetryAfterAppend
#check_axioms Child.Installed.nativeRetryAfterRejected
#check_axioms reopensSettledSegment
#check_axioms scheduledReopen_selected
#check_axioms reopensSettledSegmentScheduled
#check_axioms reopensDirtySegmentScheduled
#check_axioms Model.Effects.appendRun_refines
#check_axioms Model.openSegment_settled
#check_axioms Model.openSegment_dirty
#check_axioms Model.appendSegment_dirty
#check_axioms Model.publish_cases
#check_axioms Model.rotateIfFull_cases
#check_axioms Model.collect_cases
#check_axioms Model.collect_healthy
#check_axioms Model.create_returns_ready
#check_axioms Model.create_healthy
#check_axioms rotateIfFull_refines
#check_axioms appendActive_refines
#check_axioms append_refines
#check_axioms append_exhausted
#check_axioms append_returned_representable
#check_axioms append_returned_position
#check_axioms Model.reopen_refines
#check_axioms Model.reopen_healthy
#check_axioms Recoverable.powerLoss
#check_axioms Recoverable.writeback
#check_axioms Contract.acknowledged_retained
#check_axioms Contract.acknowledged_discard_persists
#check_axioms discard_refines
#check_axioms Run.refines
#check_axioms Run.refinesOnline
#check_axioms Run.acknowledged_retained
#check_axioms Run.acknowledged_discard_persists
#check_axioms Run.healthy_open
#check_axioms Native.readControl_canonical
#check_axioms Native.acquireRoot_selects
#check_axioms Child.Recoverable.nativeCloseAfterOpen
#check_axioms Native.acquireStore_bind
#check_axioms Native.openWithStore_reached
#check_axioms Native.withActiveChild_reached
#check_axioms Model.nativeAcquireBinding_ok
#check_axioms Native.scan_ready
#check_axioms Native.close_ready
#check_axioms Native.release_reached
#check_axioms Native.closeChild_reached
#check_axioms Native.closePhase_reached
#check_axioms Native.openRootDirectory_usesCanonicalPath
#check_axioms Native.segmentId_sound
#check_axioms Native.segmentId_canonical
#check_axioms Native.listedIds_exact
#check_axioms Native.installPhase_reached
#check_axioms Model.nativeRemoveSegment
#check_axioms Model.nativeRootBarrier
#check_axioms Model.reopen_nativeRoot
#check_axioms Model.reopen_nativeHealthy
#check_axioms Model.reopenScopedModel_refines
#check_axioms Model.reopenScopedModel_healthy
#check_axioms Model.nativeAppendAfterTransfer
#check_axioms Model.installScopedModel_healthy
#check_axioms Model.publicOpenModel_refines
#check_axioms Model.nativeControl_cuts
#check_axioms Model.nativeControl_healthy
#check_axioms Model.appendAfterNativeReopen
#check_axioms Model.publicAppendAfterReopen
#check_axioms Model.initializeChild_writes
#check_axioms Model.appendActiveModel_childPhase
#check_axioms Model.appendActiveModel_rejected
#check_axioms Model.repeatOpenAfterAppend
#check_axioms Model.nativeControl_bootstrap
#check_axioms Model.nativeControl_bootstrap_ready
#check_axioms Model.nativeRotation_beforeAppend
#check_axioms Model.nativeCreatedChild
#check_axioms Model.prepareNativeChild_authority
#check_axioms Model.prepareNativeChild_frames
#check_axioms Model.publishPreparedChild
#check_axioms Model.readyAfterPublishingSuccessor
#check_axioms Model.settlePreparedChild
#check_axioms Model.nativeAppendModel_active
#check_axioms Model.nativeAppendModel_refines
#check_axioms Model.nativeAppendModel_rejected
#check_axioms Model.nativeAppendModel_healthy
#check_axioms Model.nativeBootstrap_ready
#check_axioms Model.publicNativeAppend_refines
#check_axioms Model.publicNativeAppend_position
#check_axioms Model.appendFailure_childClose
#check_axioms Model.publicAppendClose_releases
#check_axioms Model.publicAppendClose_afterReported
#check_axioms Model.publicNativeAppend_reportedClose
#check_axioms Model.publicAppendClose_afterRejection
#check_axioms Model.publicAppendClose_repeated
#check_axioms Model.publicNativeAppend_rejected
#check_axioms Model.publicBootstrap_installs
#check_axioms Model.publicBootstrap_healthy
#check_axioms Model.publicNativeCreate_healthy
#check_axioms Model.publicBootstrap_failed_releases
#check_axioms Model.reopensWithAppendAuthority
#check_axioms Model.appendRecovery_representable
#check_axioms Model.nativeAppendModel_rotation_refines
#check_axioms Model.publicAppendRecovery
#check_axioms Model.appendLostAck
#check_axioms WalRecoverySlice.SingleFile.createModel_opened
#check_axioms WalRecoverySlice.SingleFile.createModel_healthy
#check_axioms Model.successor_controlRepresentable
#check_axioms Model.nativeControl_rejected
#check_axioms Model.nativeDiscard_recoverable
#check_axioms Model.repeatOpenAfterNativeFailedDiscard
#check_axioms Model.sealedChildReport
#check_axioms Model.publicOpenModel_append
#check_axioms Model.publicOpenModel_healthy
#check_axioms Model.repeatOpenAfterFailedDiscard
#check_axioms Model.nativeChild_recoverable
#check_axioms Model.nativeChild_sealed
#check_axioms Model.nativeChild_selected
#check_axioms Native.compactBounds_eq
#check_axioms Native.scanReadyWith_read
#check_axioms Native.activeScanWith_read
#check_axioms Native.sealedScanWith_reads
#check_axioms Native.scanReadyWith_fileReads
#check_axioms Native.recoverCompactWith_delivers
#check_axioms Native.withActiveChild_reportedFailure
#check_axioms Native.scanReadyWith_selected
#check_axioms Native.ReadOutcome.healthy
LEAN
