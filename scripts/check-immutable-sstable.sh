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
compile Alvoki/Codec/WordChecksum native
for module in Contract Search Core Builder Native FixedFormat FixedBuilder FixedReader FixedNative; do
  compile "$table/$module" native
done
compile "$table/Representation"
compile Alvoki/Kernel/BlockContracts
compile Alvoki/Codec/ByteWords
for proof in Search Format Builder Reader ReadErrors Typed FixedFormat FixedBuilder FixedGeometry FixedReader; do
  compile "$table/Proofs/$proof"
done
compile Alvoki/Checks/Audit/AxiomPolicy
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.SSTable.Proofs.Builder
import Alvoki.Experiments.SSTable.Proofs.Reader
import Alvoki.Experiments.SSTable.Proofs.ReadErrors
import Alvoki.Experiments.SSTable.Proofs.Typed
import Alvoki.Experiments.SSTable.Proofs.FixedReader
open ImmutableSSTable
#check_axioms Fixed.open_built_table
#check_axioms Fixed.readEntry_source_error
#check_axioms Fixed.decodeBlock_rejects_checksum
#check_axioms Fixed.decodeFooter_rejects_checksum
#check_axioms open_built_table
#check_axioms TypedTable.represents_of_bytes
#check_axioms decodeEntry_rejects_checksum
#check_axioms RequiredProbeError.propagates
#check_axioms Table.readEntry_index_error
#check_axioms Table.readEntry_index_decode_error
#check_axioms Table.readEntry_source_error
#check_axioms Table.readEntry_decode_error
#check_axioms Table.seek_read_error
#check_axioms Table.next_read_error
#check_axioms Table.lookup_search_error
#check_axioms Table.lookup_final_read_error
#check_axioms modelBuild_ok_iff
#check_axioms push_rejects_key
#check_axioms openTable_encoded
#check_axioms decodeFooter_encodeFooter
#check_axioms decodeEntry_encodeEntry
#check_axioms Table.readEntry_encoded
#check_axioms Table.next_encoded
#check_axioms Table.lookup_encoded
#check_axioms Table.seek_encoded
#check_axioms encodeImage_size
#check_axioms decodeImage_offsets
#check_axioms encodeImage_extract_row
#check_axioms seekBetween_correct
#check_axioms seekBetween_probes
LEAN
lean --run "$table/Tests.lean"
for fixture in NativeTests FixedNativeTests; do
  entry="$out/$table/$fixture"
  lean -o "$entry.olean" -c "$entry.c" "$table/$fixture.lean"
  leanchecker "${table//\//.}.$fixture"
  cc -O2 -fPIC -I"$prefix/include" "${sources[@]}" "$entry.c" native/sstable.c native/fsync.c \
    -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/test-sstable"
  "$out/test-sstable"
done
