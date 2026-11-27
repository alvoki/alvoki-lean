import Alvoki.Experiments.SSTable.UnifiedIntegrity

namespace ImmutableSSTable.Unified

/-- Same logical CRC32C definition, compiled to Google CRC32C over the borrowed
    bytes. Native agreement with the logical definition is a runtime assumption. -/
@[extern "alvoki_crc32c_extend"]
def nativeCRC32C (previous : UInt32) (bytes : @& ByteArray) : UInt32 :=
  crc32c previous bytes

end ImmutableSSTable.Unified
