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
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/native-l0"
cc -shared -fPIC native/l0_interrupt_fixture.c -ldl -o "$out/l0_interrupt_fixture.so"
"$out/native-l0" "$out/l0_interrupt_fixture.so"
compile "$l0/NativeBridge" proof
compile "$l0/LifecycleRefinement" proof
compile "$l0/ScheduleSteps" proof
compile "$l0/TableProofs" proof
compile "$l0/TableAllocationProofs" proof
compile Alvoki/Checks/Audit/AxiomPolicy proof
for module in Codecs CodecProofs Lifecycle Native NativeFacts ManifestComposition NativeBridge LifecycleRefinement ScheduleSteps TableSchedule TableProofs TableAllocation TableAllocationProofs TableRows TableRowProofs; do
  leanchecker "Alvoki.Experiments.L0.$module"
done
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.ScheduleSteps
import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.LifecycleRefinement
import Alvoki.Experiments.L0.TableProofs
import Alvoki.Experiments.L0.TableAllocationProofs
open ExperimentalL0 ExperimentalL0.NativeBridge
#check_axioms keyCodec_roundtrips
#check_axioms keyCodec_preservesOrder
#check_axioms mutationCodec_roundtrips
#check_axioms wal_append
#check_axioms wal_scan
#check_axioms wal_open
#check_axioms ManifestComposition.reopen
#check_axioms ManifestComposition.publish
#check_axioms ManifestComposition.initialOpenPublish
#check_axioms ManifestComposition.reopenSelected
#check_axioms ManifestComposition.publishSelected
#check_axioms ManifestComposition.retryAfterPublication
#check_axioms CallbackEvidence.laws
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
#check_axioms native_table_descriptor_checked
#check_axioms table_descriptor_acquired
#check_axioms table_descriptor_stat_error
#check_axioms table_descriptor_rejected
#check_axioms table_descriptor_open_error
#check_axioms native_table_lookup
#check_axioms freeTableId_spec
#check_axioms createTableAt_success
#check_axioms createTableAt_bindings
#check_axioms createTableUnder_image
#check_axioms rowSupply_step
#check_axioms nextTableRow_cons
#check_axioms nextTableRow_nil
#check_axioms supplied_builder_input
#check_axioms TableCreationEvidence.effect
#check_axioms TableOpen.represents
#check_axioms tableOpenAt
#check_axioms TableRead.effect
LEAN
