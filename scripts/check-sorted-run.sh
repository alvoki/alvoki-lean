#!/usr/bin/env bash
# Check the real merge schedule, the writer composition and native fixtures.
set -euo pipefail
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

merge=Alvoki.Experiments.SortedRun
modules=(
  "$merge".{Merge,Proofs,SSTable,SSTableProofs,IOEffects,Refinement,NativeRefinement}
  Alvoki.Experiments.SSTable.Proofs.{NativeWrite,UnifiedReadSafety}
  Alvoki.Checks.{Tests.SortedRunEffects,Audit.AxiomPolicy}
)
lake build "${modules[@]}" Alvoki.Experiments.Manifest.Basic Alvoki.Experiments.WAL.Segmented.Contract
for module in "${modules[@]}"; do
  lake env leanchecker "$module"
done
lake env lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Checks.Tests.SortedRunEffects
import Alvoki.Experiments.SortedRun.NativeRefinement

open SortedRun ImmutableSSTable.Unified
#check_axioms merge_ordered
#check_axioms Ordered.unique_keys
#check_axioms merge_keys
#check_axioms merge_lookup
#check_axioms next_effect
#check_axioms next_exact
#check_axioms table_next_exact
#check_axioms typed_next_exact
#check_axioms next_typed_value_error
#check_axioms buildFileWith_refines_on
#check_axioms buildFileWith_eof
#check_axioms buildFileWith_writeError
#check_axioms buildMergedWith_refines
#check_axioms checkedInputs_merge_checkedOutput
#check_axioms Image.checkedOpenTable_next_scoped
#check_axioms InputPrimitives.scopedSource
#check_axioms CheckedInput.ofOpen
#check_axioms effect_buildFileWith
#check_axioms nativeNext_refines
#check_axioms nativeNext_newerError
#check_axioms nativeNext_olderError
#check_axioms buildFileWith_inputError
#check_axioms buildMergedFileSynced_success
#check_axioms buildMergedFileSynced_inputError
#check_axioms EffectsCheck.first_row
#check_axioms EffectsCheck.read_error_after_row
LEAN

# Keep the L0 consumer out of the component's import graph and Lake targets.
(
  out=$(mktemp -d)
  trap 'rm -rf "$out"' EXIT
  cp -as "$PWD/.lake/build/lib/lean/Alvoki" "$out/Alvoki"
  export LEAN_PATH="$out"
  l0=Alvoki/Experiments/L0
  rm -rf "$out/$l0"
  mkdir -p "$out/$l0"
  for module in Basic Proofs; do
    lean -o "$out/$l0/$module.olean" "$l0/$module.lean"
  done
  lean --root=../tests/sorted-run -o "$out/L0Consumer.olean" ../tests/sorted-run/L0Consumer.lean
  leanchecker L0Consumer
  lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import L0Consumer
#check_axioms ExperimentalL0.sortedRun_matches_compaction_reference
LEAN
)

lake exe sortedRunNativeCheck
