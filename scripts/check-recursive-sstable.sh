#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

root=Alvoki.Experiments.SSTable.Recursive
modules=("$root".{Invariants,Image,FilterWriteProofs,NativeReadProofs})
lake build "${modules[@]}" Alvoki.Checks.Audit.AxiomPolicy
for module in "${modules[@]}"; do
  lake env leanchecker "$module"
done

lake env lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.SSTable.Recursive.Invariants
import Alvoki.Experiments.SSTable.Recursive.FilterWriteProofs
import Alvoki.Experiments.SSTable.Recursive.NativeReadProofs
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
#check_axioms ImmutableSSTable.Bloom.build_covers
#check_axioms Writer.writeFilter_appends
#check_axioms Writer.writeFilter_packetAt
#check_axioms FilterAt.accepts
#check_axioms Image.open_filtered_represents
#check_axioms checkedNativeFilteredLookup
LEAN

lake exe recursiveSSTableCheck
