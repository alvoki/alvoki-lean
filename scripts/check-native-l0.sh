#!/usr/bin/env bash
# Compile the native L0 fixture with precisely its local Lean dependencies.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
lake build crc32cArchive >&2
declare -A compiled
sources=()
compile() {
  local module=$1 mode=$2 dependency
  if [[ ! -f $module.lean || -n ${compiled[$module]:-} ]]; then
    return
  fi
  while read -r dependency; do
    compile "${dependency//./\/}" "$mode"
  done < <(awk '$1 == "import" { for (i = 2; i <= NF && $i !~ /^--/; i++) print $i }' "$module.lean")
  mkdir -p "$out/$(dirname "$module")"
  if [[ $mode == native ]]; then
    lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
    sources+=("$out/$module.c")
  else
    lean -o "$out/$module.olean" "$module.lean"
  fi
  compiled[$module]=1
}
l0=Alvoki/Experiments/L0
compile "$l0/NativeTests" native
cc -O1 -fPIC -I"$prefix/include" "${sources[@]}" native/{fsync,read_dir_checked,sstable}.c \
  .lake/build/native/libalvoki_crc32c.a -lstdc++ -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/native-l0"
cc -shared -fPIC native/l0_interrupt_fixture.c -ldl -o "$out/l0_interrupt_fixture.so"
"$out/native-l0" "$out/l0_interrupt_fixture.so"
compile "$l0/NativeFacts" proof
compile "$l0/NativeBridge" proof
compile "$l0/WalProducerHandoff" proof
leanchecker Alvoki.Experiments.L0.WalProducerHandoff
compile "$l0/LifecycleRefinement" proof
compile "$l0/RestartRefinement" proof
compile "$l0/ScheduleSteps" proof
compile "$l0/TableProofs" proof
compile "$l0/TableAllocationProofs" proof
for module in NativeManifest NativeRead NativeReadClient NativeRecovery NativeTableCheck PublicationCut WithOpenReads HealthyReads; do
  compile "$l0/$module" proof
done
compile Alvoki/Experiments/WAL/Segmented/Proofs/RuntimeChild proof
for module in NativeMutation HealthyMutation InterruptedWorker; do
  compile "$l0/$module" proof
done
for module in PreparedFile ControlCutIO PrepareCutIO ChildCutIO CutSchedule; do
  compile "Alvoki/Experiments/WAL/Segmented/Proofs/$module" proof
done
compile Alvoki/Checks/Audit/AxiomPolicy proof
for module in Codecs CodecProofs Lifecycle Native NativeFacts NativeTableReads WalRecovery ManifestComposition ManifestRecovery DurableCatalog RestartRefinement NativeBridge LifecycleRefinement ScheduleSteps TableSchedule TableProofs TableAllocation TableAllocationProofs TableRows TableRowProofs NativeManifest NativeRead NativeReadClient NativeRecovery NativeTableCheck PublicationCut WithOpenReads HealthyReads HealthyClose HealthyRootAcquisition AppendRecovery NativeWrite NativeWriteRelease NativeMutation HealthyMutation NativeMutationScope NativeMutationReopens NativeAppendCut InterruptedMutation InterruptedWorker NativeRecoverSelected PendingReadScope NativeScope NativeReadScope NativeReadRelease NativeRecoverAt NativeCleanup NativePublish; do
  leanchecker "Alvoki.Experiments.L0.$module"
done
for module in DurableBlob.FileRead SSTable.Proofs.UnifiedReadSafety WAL.Proofs.NativePost WAL.Proofs.ConcreteRecovery WAL.Proofs.ConcreteOpen WAL.Segmented.Proofs.NativeRootIO WAL.Segmented.Proofs.NativeChildIO WAL.Segmented.Proofs.StoreAcquisition WAL.Segmented.Proofs.RuntimeStoreOpen WAL.Segmented.Proofs.RuntimeChild WAL.Segmented.Proofs.RuntimeDisk WAL.Segmented.Proofs.HealthyEmpty WAL.Proofs.ConcreteAppend WAL.Proofs.ConcreteCreate WAL.Segmented.Proofs.AppendIngress WAL.Segmented.Proofs.AppendRotationIO WAL.Segmented.Proofs.ControlCutIO WAL.Segmented.Proofs.PrepareCutIO WAL.Segmented.Proofs.PreparedFile WAL.Segmented.Proofs.AppendRuntime WAL.Segmented.Proofs.CutSchedule WAL.Segmented.Proofs.ChildCutIO WAL.Proofs.ConcreteAppendCut WAL.Segmented.Proofs.CreateCutIO WAL.Segmented.Proofs.AppendPrefixLayout WAL.Segmented.Proofs.ChildHeapCut WAL.Segmented.Proofs.AppendCutBody WAL.Segmented.Proofs.CutRuntime; do
  leanchecker "Alvoki.Experiments.$module"
done
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.L0.NativeFacts
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.L0.RestartRefinement
import Alvoki.Experiments.L0.ScheduleSteps
import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.LifecycleRefinement
import Alvoki.Experiments.L0.TableProofs
import Alvoki.Experiments.L0.TableAllocationProofs
import Alvoki.Experiments.L0.NativeManifest
import Alvoki.Experiments.L0.NativeRecovery
import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.L0.InterruptedWorker
import Alvoki.Experiments.WAL.Segmented.Proofs.ChildCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.PreparedFile
import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRotationIO
import Alvoki.Experiments.L0.HealthyReads
import Alvoki.Experiments.L0.HealthyMutation
import Alvoki.Experiments.L0.NativeTableCheck
import Alvoki.Experiments.L0.PublicationCut
import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeChild
import Alvoki.Experiments.L0.WalProducerHandoff
open ExperimentalL0 ExperimentalL0.NativeBridge
#check_axioms WalProducerHandoff.reopenAuthority
#check_axioms WalProducerHandoff.reportedWrite
#check_axioms WalProducerHandoff.retry
#check_axioms WalRecoverySlice.SingleFile.ConcreteRecovery.openExisting
#check_axioms WalRecoverySlice.Segmented.Native.acquireStore_io
#check_axioms WalRecoverySlice.Segmented.Native.ChildPrimitives.access
#check_axioms WalRecoverySlice.Segmented.Native.StoreIO.recoverChild_disk
#check_axioms WalRecoverySlice.Segmented.Native.openExisting_registered_diskPost
#check_axioms NativeRecoverAt.recoverAt_checks
#check_axioms NativeRecoverAt.recoverAt
#check_axioms NativeRead.publishOnline
#check_axioms NativeReadRelease.onlineTo
#check_axioms NativeReadRelease.failedTo
#check_axioms FileRead.readBinFile
#check_axioms FileRead.readBinFile_atEOF
#check_axioms WalRecoverySlice.Segmented.Native.Store.readControl_fromFile
#check_axioms WalRecoverySlice.Segmented.Native.Store.syncRoot_io
#check_axioms WalRecoverySlice.Segmented.Native.CollectionIO.collect
#check_axioms ImmutableSSTable.Unified.checkedOpen_frame
#check_axioms ImmutableSSTable.Unified.Image.checkedOpen_healthy
#check_axioms ImmutableSSTable.Unified.checkedTypedLookup_scoped
#check_axioms ExperimentalL0.Native.get_atRoot
#check_axioms table_lookup_scoped
#check_axioms NativeManifest.reopen
#check_axioms NativeManifest.reopen_atSync
#check_axioms NativeRecovery.reopenWal
#check_axioms NativeRecovery.recover
#check_axioms PublicationCut.renameCut
#check_axioms PublicationCut.cutRecovery
#check_axioms NativeRead.Call.Balanced.released
#check_axioms NativeRead.tableAction
#check_axioms NativeRead.checkTables_frame
#check_axioms NativeRead.checkTables_balanced
#check_axioms NativeRead.checkTables_healthy
#check_axioms NativeRead.firstSizeError
#check_axioms WalRecoverySlice.Segmented.Writebacks.installed
#check_axioms NativeRead.Online.frame
#check_axioms NativeRead.onlineGet
#check_axioms NativeRead.onlineGetTwice
#check_axioms NativeRead.erasesGet
#check_axioms NativeRead.publicGet
#check_axioms NativeRead.readTwice_run
#check_axioms NativeRead.readMany_run
#check_axioms NativeRead.readMany_length
#check_axioms NativeRead.readEvents_eq_zip
#check_axioms NativeRead.caughtSizeError_thenHit
#check_axioms WalRecoverySlice.Segmented.Native.acquireStore_rootLockAt
#check_axioms WalRecoverySlice.Segmented.Native.close_registered
#check_axioms NativeReadRelease.Laws.separate
#check_axioms NativeReadRelease.root_released
#check_axioms NativeRecoverAt.withOpen_manifestStatError
#check_axioms NativeReadRelease.RootCall.released
#check_axioms WithOpenReads.Failure.rootReleased
#check_axioms NativeWrite.dispatch
#check_axioms NativeWriteRelease.afterError
#check_axioms NativeWriteRelease.outerOffline
#check_axioms NativeMutationScope.withOpen_of_append
#check_axioms NativeMutationScope.mutationThenReadTwice
#check_axioms NativeReadRelease.mutation_released
#check_axioms NativeAppendCut.Restarted.uncertain
#check_axioms InterruptedMutation.Prefix.beforeAppend
#check_axioms InterruptedMutation.Worker.interrupted
#check_axioms WalRecoverySlice.Segmented.Native.AppendCut.recoverBody
#check_axioms WalRecoverySlice.Segmented.Native.CreateCutIO.program_run
#check_axioms WalRecoverySlice.Segmented.Native.PrepareCutIO.Prefix.continuation
#check_axioms WalRecoverySlice.Segmented.Native.AppendIO.LocalIO.healthy
#check_axioms WalRecoverySlice.Segmented.Native.PrepareIO.selectedOnly_counterexample
#check_axioms WalRecoverySlice.Segmented.Native.PrepareIO.Successor.healthy
#check_axioms PendingReadScope.twice
#check_axioms NativeRecoverAt.recoverAt_selected_checks
#check_axioms WalRecoverySlice.Segmented.Native.AppendIO.Active.ofRecovered
#check_axioms WalRecoverySlice.Segmented.Native.AppendIO.append_rejected
#check_axioms WalRecoverySlice.Segmented.Native.AppendIO.LocalRotation.assemble
#check_axioms WalRecoverySlice.Segmented.Native.ControlCutIO.survivor
#check_axioms HealthyMutation.withOpen
#check_axioms HealthyReads.withOpen
#check_axioms HealthyRootAcquisition.walClose
#check_axioms WalRecoverySlice.SingleFile.ConcreteRecovery.reopen_shrinks
#check_axioms WalRecoverySlice.SingleFile.ConcreteRecovery.stampRead_notReusable
#check_axioms WalRecoverySlice.SingleFile.ConcreteRecovery.stampSync_notReusable
#check_axioms WithOpenReads.withOpen
#check_axioms WithOpenReads.Failure.refines
#check_axioms WithOpenReads.readMany_two
#check_axioms WithOpenReads.caught_then_got
#check_axioms keyCodec_roundtrips
#check_axioms keyCodec_preservesOrder
#check_axioms mutationCodec_roundtrips
#check_axioms wal_append
#check_axioms WalRecovery.Interpretation.reopenReached
#check_axioms WalRecovery.Interpretation.scanAfterReopen
#check_axioms WalRecovery.Interpretation.reportedFailure
#check_axioms WalRecovery.Interpretation.reopenHealthy
#check_axioms WalRecovery.Interpretation.scanEffect
#check_axioms DurableBlob.LinuxEffects.reopenBinding
#check_axioms DurableBlob.LinuxEffects.reopenHealthy
#check_axioms DurableBlob.LinuxEffects.publishActive
#check_axioms ManifestComposition.reopen
#check_axioms ManifestComposition.publish
#check_axioms ManifestComposition.healthyInitialOpenPublish
#check_axioms ManifestComposition.reopenSelected
#check_axioms ManifestComposition.publishSelected
#check_axioms ManifestComposition.retryAfterPublication
#check_axioms ManifestComposition.Interpretation.reopenEffect
#check_axioms ManifestComposition.Interpretation.reopenHealthy
#check_axioms ManifestComposition.Interpretation.publishEffect
#check_axioms CallbackEvidence.recoveryEffects
#check_axioms CallbackEvidence.flushEffects
#check_axioms CallbackEvidence.flushCatalog
#check_axioms get_refines_from
#check_axioms Execution.Run.flushObserved
#check_axioms Execution.Run.refines
#check_axioms Execution.Run.recoverOk
#check_axioms Execution.Run.recoverError
#check_axioms Lifecycle.Phase.online_owns_wal
#check_axioms Lifecycle.Phase.publish_owns_wal
#check_axioms Lifecycle.Phase.beginUpdate_hides_session
#check_axioms Lifecycle.Phase.attachWal_keeps_session_private
#check_axioms Lifecycle.Phase.offline_closed
#check_axioms Lifecycle.Proof.withSession_closes
#check_axioms Lifecycle.Proof.failed_recovery_closes
#check_axioms Lifecycle.Proof.successful_recovery_publishes
#check_axioms Lifecycle.Proof.update_success
#check_axioms Lifecycle.Proof.update_error
#check_axioms Lifecycle.Proof.reopen_attaches_before_scan
#check_axioms Lifecycle.Proof.reopen_open_failure
#check_axioms Lifecycle.Proof.recover_attached
#check_axioms Lifecycle.Proof.write_keepsPhase
#check_axioms Lifecycle.Proof.flush_keepsPhase
#check_axioms Lifecycle.Proof.get_keepsPhase
#check_axioms Lifecycle.initialCatalog
#check_axioms Lifecycle.recovery_progress
#check_axioms Lifecycle.scope_refines
#check_axioms ExperimentalL0.Native.get_afterPhaseRead
#check_axioms retainRecoverySelection
#check_axioms Lifecycle.recovery_online
#check_axioms Lifecycle.recovery_offline
#check_axioms Lifecycle.flush_online
#check_axioms Lifecycle.flush_offline
#check_axioms Lifecycle.Proof.useSession_offline
#check_axioms native_table_check
#check_axioms nativeTableAt_afterStat
#check_axioms nativeTableAt_acquired
#check_axioms table_descriptor_acquired
#check_axioms table_descriptor_stat_error
#check_axioms table_descriptor_rejected
#check_axioms table_descriptor_open_error
#check_axioms table_lookup_success
#check_axioms freeTableId_spec
#check_axioms createTableAt_success
#check_axioms createTableAt_bindings
#check_axioms TableCreationEvidence.published
#check_axioms TableCreationEvidence.catalogAfter
#check_axioms TableCreationEvidence.catalogInserted
#check_axioms TableCreationEvidence.failureCatalog
#check_axioms rowSupply_step
#check_axioms nextTableRow_cons
#check_axioms nextTableRow_nil
#check_axioms supplied_builder_input
#check_axioms TableCreationEvidence.effect
#check_axioms table_open_published_inode
#check_axioms nextTableRow_writerEffect
#check_axioms flushPublicationChoices
#check_axioms ManifestComposition.StateWithImage.interpretation
#check_axioms ManifestComposition.recoverPublication
#check_axioms ManifestComposition.reopenAfterRestart
#check_axioms TableNamespace.scopedLookup
#check_axioms nativeTableAt_success
#check_axioms nativeTableAt_reached
#check_axioms TableNamespace.scopedCheck
#check_axioms NativeTableReads.product
#check_axioms NativeTableReads.productFrame
#check_axioms NativeTableReads.Interpretation.checkHealthy
#check_axioms RestartLookup.get
#check_axioms TableNamespace.Represents.frame
#check_axioms recoverKeepsCatalog
#check_axioms recoverCatalog
#check_axioms recover_progress
#check_axioms recoverReachedFlush
LEAN
