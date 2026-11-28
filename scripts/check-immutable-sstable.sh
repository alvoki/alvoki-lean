#!/usr/bin/env bash
# Kernel-check the immutable SSTable and exercise the native reader.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} || -d ../../work/toolchains/elan ]]; then
  export ELAN_HOME="$(cd "${ALVOKI_TOOLCHAINS:-../../work/toolchains}/elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
table=Alvoki.Experiments.SSTable
modules=(
  Alvoki.Codec.{Block,CRC32C,WordChecksum,ByteWords}
  Alvoki.Kernel.BlockContracts
  "$table".{Contract,Search,Core,Native,Representation}
  "$table".{UnifiedFormat,UnifiedIntegrity,UnifiedBuilder,UnifiedReader,UnifiedNative,UnifiedFixtures}
  "$table".Proofs.{Reader,Search,Typed,UnifiedMetadata,UnifiedData,UnifiedImage,UnifiedSearch}
  "$table".Proofs.{UnifiedGroups,UnifiedReads,UnifiedOpen,UnifiedBuilder,UnifiedEndToEnd}
  "$table".Proofs.{UnifiedNativeReader,UnifiedReadErrors,UnifiedReadSafety,NativeWrite,UnifiedNativeEndToEnd}
  Alvoki.Checks.Tests.SSTableProducer
  Alvoki.Checks.Audit.AxiomPolicy
)
lake build "${modules[@]}"
for module in "${modules[@]}"; do
  lake env leanchecker "$module"
done
lake env lean --stdin <<'LEAN'
import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadErrors
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadSafety
import Alvoki.Checks.Tests.SSTableProducer
import Alvoki.Experiments.SSTable.Proofs.Typed
open ImmutableSSTable
#check_axioms Alvoki.lowerBound_partition
#check_axioms Alvoki.pushWordFast_roundtrip
#check_axioms Alvoki.splitByte_joinBytes
#check_axioms Unified.buildFileWith_refines
#check_axioms Unified.buildFileWith_syncError
#check_axioms Unified.buildFileWith_open_represents
#check_axioms SSTableProducerCheck.checkedLookup
#check_axioms SSTableProducerCheck.uncertainResult
#check_axioms Unified.open_built_table
#check_axioms Unified.Image.checkedLookup_sound
#check_axioms Unified.checkedTypedLookup_success
#check_axioms Unified.Image.openCheckedWith_represents_at
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
lake exe immutableSSTableCheck "$@"
