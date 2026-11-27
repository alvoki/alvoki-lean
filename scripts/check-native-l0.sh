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
"$out/native-l0"
compile "$l0/NativeBridge" proof
compile Alvoki/Checks/Audit/AxiomPolicy proof
for module in Codecs CodecProofs Lifecycle Native NativeFacts NativeBridge; do
  leanchecker "Alvoki.Experiments.L0.$module"
done
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.Lifecycle
open ExperimentalL0 ExperimentalL0.NativeBridge
#check_axioms keyCodec_roundtrips
#check_axioms keyCodec_preservesOrder
#check_axioms mutationCodec_roundtrips
#check_axioms wal_append
#check_axioms manifest_trace
#check_axioms built_lookup
#check_axioms manifest_publish
#check_axioms CallbackEvidence.laws
#check_axioms ObservedRun.refines
#check_axioms Lifecycle.Phase.online_owns_wal
#check_axioms Lifecycle.Phase.publish_owns_wal
#check_axioms Lifecycle.Phase.beginUpdate_hides_session
#check_axioms Lifecycle.Phase.attachWal_keeps_session_private
#check_axioms Lifecycle.Phase.offline_closed
LEAN
