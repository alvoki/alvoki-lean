#!/usr/bin/env bash
# Kernel-check the immutable SSTable and exercise the native reader.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
prefix=$(lean --print-prefix)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out"
lake build crc32cArchive >&2
table=Alvoki/Experiments/SSTable
sources=()
compile() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  lean -o "$out/$module.olean" -c "$out/$module.c" "$module.lean"
  leanchecker "${module//\//.}"
  sources+=("$out/$module.c")
}
compile Alvoki/Codec/Block
compile Alvoki/Codec/CRC32C
for module in Contract Search Core Native \
    UnifiedFormat UnifiedIntegrity UnifiedNativeIntegrity UnifiedBuilder UnifiedReader UnifiedNative UnifiedFixtures; do
  compile "$table/$module"
done
compile_proof() {
  local module=$1
  mkdir -p "$out/$(dirname "$module")"
  lean -o "$out/$module.olean" "$module.lean"
  leanchecker "${module//\//.}"
}
compile_proof Alvoki/Kernel/BlockContracts
compile_proof Alvoki/Codec/WordChecksum
compile_proof Alvoki/Codec/ByteWords
compile_proof "$table/Representation"
for module in Reader Search Typed UnifiedMetadata UnifiedData UnifiedImage UnifiedSearch \
    UnifiedGroups UnifiedReads UnifiedOpen UnifiedBuilder UnifiedEndToEnd \
    UnifiedNativeReader UnifiedReadErrors NativeWrite UnifiedNativeEndToEnd; do
  compile_proof "$table/Proofs/$module"
done
compile_proof Alvoki/Checks/Audit/AxiomPolicy
lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadErrors
import Alvoki.Experiments.SSTable.Proofs.Typed
open ImmutableSSTable
#check_axioms Unified.buildFileWith_refines
#check_axioms Unified.buildFileWith_syncError
#check_axioms Unified.buildFileWith_open_represents
#check_axioms Unified.open_built_table
#check_axioms Unified.openCheckedWith_built_table_at
#check_axioms ReadSnapshot.readsExactly
#check_axioms Unified.openCheckedWith_acquire_error
#check_axioms Unified.openCheckedWith_size_error
#check_axioms ReadPrimitives.source_pread_error
#check_axioms RequiredProbeError.propagates
#check_axioms Unified.readPacket_source_error
#check_axioms Unified.readPacket_short_error
#check_axioms Unified.readPacket_decode_error
#check_axioms Unified.readFooter_size_error
#check_axioms Unified.readFooter_extent_error
#check_axioms Unified.readFooter_source_error
#check_axioms Unified.readFooter_short_error
#check_axioms Unified.readFooter_packet_error
#check_axioms Unified.readFooter_decode_error
#check_axioms Unified.openTableChecked_footer_error
#check_axioms Unified.openTableChecked_identity_error
#check_axioms Unified.openTableChecked_root_error
#check_axioms Unified.openTableChecked_root_decode_error
#check_axioms Unified.Handle.readLeaf_packet_error
#check_axioms Unified.Handle.readLeaf_decode_error
#check_axioms Unified.Handle.readData_packet_error
#check_axioms Unified.Handle.readData_decode_error
#check_axioms Unified.Handle.locate_leaf_error
#check_axioms Unified.Handle.locate_data_error
#check_axioms Unified.Handle.locate_row_probe_error
#check_axioms Unified.Handle.table_lookup_seek_error
#check_axioms Unified.Handle.table_lookup_row_error
#check_axioms Unified.Handle.table_next_leaf_error
#check_axioms Unified.Handle.table_next_data_error
#check_axioms Unified.Handle.table_next_row_error
#check_axioms Unified.Handle.lookup_leaf_error
#check_axioms TypedTable.seek_read_error
#check_axioms TypedTable.lookup_read_error
#check_axioms TypedTable.lookup_decode_error
#check_axioms TypedTable.next_read_error
#check_axioms TypedTable.next_key_decode_error
#check_axioms TypedTable.next_value_decode_error
#check_axioms TypedTable.represents_of_bytes
LEAN
cc -O2 -DNDEBUG -fPIC -I"$prefix/include" "${sources[@]}" native/sstable.c native/fsync.c \
  ".lake/build/native/libalvoki_crc32c.a" -lstdc++ -L"$prefix/lib/lean" \
  -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/test-unified-sstable"
"$out/test-unified-sstable" "$@"
