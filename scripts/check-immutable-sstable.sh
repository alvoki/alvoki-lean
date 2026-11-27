#!/usr/bin/env bash
# Fresh build of the immutable SSTable, including its native positional reader.
set -euo pipefail
ulimit -s unlimited
cd "$(dirname "$0")/../lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
table=Alvoki/Experiments/SSTable
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  if [[ ${2:-} == native ]]; then
    lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
    sources+=("$out/$module.c")
  else
    lean -o "$out/$module.olean" "$module.lean"
  fi
  leanchecker "${module//\//.}"
}
compile Alvoki/Codec/Block native
for module in Contract Search Core Builder Native NativeTests; do
  compile "$table/$module" native
done
compile Alvoki/Kernel/BlockContracts
compile Alvoki/Codec/ByteWords
for proof in Search Format Builder Reader; do
  compile "$table/Proofs/$proof"
done
compile Alvoki/Checks/Audit/AxiomPolicy
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.SSTable.Proofs.Builder
import Alvoki.Experiments.SSTable.Proofs.Reader
open ImmutableSSTable
#check_axioms open_built_table
#check_axioms builder_accepts_only_ordered
#check_axioms builder_constructs_image
#check_axioms push_rejects_key
#check_axioms openTable_encoded
#check_axioms open_lookup_encoded
#check_axioms decodeHeader_encodeHeader
#check_axioms decodeEntry_encodeEntry
#check_axioms Table.readEntry_encoded
#check_axioms Table.next_encoded
#check_axioms Table.lookup_encoded
#check_axioms Table.seek_encoded
#check_axioms fileSize_bound
#check_axioms rowSpan
#check_axioms seekBetween_correct
#check_axioms seekBetween_probes
LEAN
lean --run "$table/Tests.lean"
cc -O2 -fPIC -I"$prefix/include" "${sources[@]}" native/sstable.c \
  -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/test-sstable"
"$out/test-sstable"
