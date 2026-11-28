#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

root=Alvoki.Experiments.SSTable.Recursive
modules=("$root".{Invariants,Image,WriterHeight,WriterProgress,WriterProofs,NativeReadProofs,NativeWriteProofs,WriterStreamingProgress,WriterFinalProgress,WriterEffectsProgress,WriterHealthy}
  Alvoki.Checks.Tests.RecursiveSSTableProducer)
lake build "${modules[@]}" Alvoki.Checks.Audit.AxiomPolicy
for module in "${modules[@]}"; do
  lake env leanchecker "$module"
done

lake env lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Checks.Tests.RecursiveSSTableProducer
import Alvoki.Experiments.SSTable.Recursive.Invariants
import Alvoki.Experiments.SSTable.Recursive.WriterHealthy
open ImmutableSSTable.Recursive
#check_axioms checkedChild_bounds
#check_axioms checkedChild_chunks
#check_axioms Page.flush_has_two
#check_axioms Page.pair_fits
#check_axioms fringe_shrinks
#check_axioms decodePage_encode
#check_axioms decodeFooter_encode
#check_axioms IndexPacketAt.read
#check_axioms TreeInImage.descend
#check_axioms Image.open_represents
#check_axioms descend_framed
#check_axioms checkedNativeLookup
#check_axioms Writer.push_ranked
#check_axioms Writer.finishPages_height
#check_axioms Writer.writePage_progress
#check_axioms Writer.push_progress
#check_axioms Writer.flushData_progress
#check_axioms Writer.finishRoot_progress
#check_axioms streamRows_progress
#check_axioms Writer.finishPages_progress
#check_axioms modelBuild_progress
#check_axioms buildFileWith_progress
#check_axioms modelBuild_ok
#check_axioms modelBuild_ne_heightError
#check_axioms buildFileWith_exact
#check_axioms buildFileWith_refines
#check_axioms freshOutput_result
#check_axioms buildFileWith_createError
#check_axioms buildFileWith_writeError
#check_axioms buildFileWith_syncError
#check_axioms buildFileWith_of_modelBuild_ok
#check_axioms buildFileWith_healthy
#check_axioms buildFileWith_open_represents
#check_axioms buildFileWith_open_typed_represents
#check_axioms buildFileWith_lookup_framed
#check_axioms buildFileWith_lookup_footerError
#check_axioms Vertical.durableMultiLevelOpens
#check_axioms Vertical.durableMultiLevelLookup
#check_axioms Vertical.durableMultiLevelFooterError
LEAN

lake exe recursiveSSTableCheck
