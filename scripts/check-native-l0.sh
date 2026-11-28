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
compile "$l0/NativeBridge" proof
compile "$l0/WalProducerHandoff" proof
leanchecker Alvoki.Experiments.L0.WalProducerHandoff
compile "$l0/LifecycleRefinement" proof
compile "$l0/RestartRefinement" proof
compile "$l0/ScheduleSteps" proof
compile "$l0/TableProofs" proof
compile "$l0/TableAllocationProofs" proof
for module in NativeManifest NativeRead NativeRecovery NativeTableCheck PublicationCut; do
  compile "$l0/$module" proof
done
compile Alvoki/Experiments/WAL/Segmented/Proofs/NativeRootIO proof
compile Alvoki/Checks/Audit/AxiomPolicy proof
for module in Codecs CodecProofs Lifecycle Native NativeFacts NativeTableReads WalRecovery ManifestComposition ManifestRecovery DurableCatalog RestartRefinement NativeBridge LifecycleRefinement ScheduleSteps TableSchedule TableProofs TableAllocation TableAllocationProofs TableRows TableRowProofs NativeManifest NativeRead NativeRecovery NativeTableCheck PublicationCut; do
  leanchecker "Alvoki.Experiments.L0.$module"
done
for module in DurableBlob.FileRead SSTable.Proofs.UnifiedReadSafety WAL.Proofs.NativePost WAL.Segmented.Proofs.NativeRootIO; do
  leanchecker "Alvoki.Experiments.$module"
done
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
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
import Alvoki.Experiments.L0.NativeTableCheck
import Alvoki.Experiments.L0.PublicationCut
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeRootIO
open ExperimentalL0 ExperimentalL0.NativeBridge
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
#check_axioms NativeRead.Writebacks.installed
#check_axioms NativeRead.Online.frame
#check_axioms NativeRead.onlineGet
#check_axioms NativeRead.onlineGetTwice
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
#check_axioms CallbackEvidence.effects
#check_axioms CallbackEvidence.writeCatalog
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
#check_axioms Lifecycle.getList_online
#check_axioms Lifecycle.getScope_refines
#check_axioms ExperimentalL0.Native.get_afterPhaseRead
#check_axioms retainRecoverySelection
#check_axioms Lifecycle.recovery_online
#check_axioms Lifecycle.recovery_offline
#check_axioms Lifecycle.write_online
#check_axioms Lifecycle.flush_online
#check_axioms Lifecycle.write_offline
#check_axioms Lifecycle.flush_offline
#check_axioms Lifecycle.Proof.useSession_offline
#check_axioms Lifecycle.get_online
#check_axioms Lifecycle.get_online_error
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
#check_axioms NativeTableReads.Interpretation.lookupEffect
#check_axioms NativeTableReads.Interpretation.checkHealthy
#check_axioms ExperimentalL0.NativeTableReads.Interpretation.get
#check_axioms TableNamespace.Represents.frame
#check_axioms recoverKeepsCatalog
#check_axioms recoverCatalog
#check_axioms recover_progress
#check_axioms recoverReachedFlush
LEAN
