import CompactionCodec
import Alvoki.Storage.Table.SequentialModel

namespace Alvoki.Compaction
open Alvoki.Opt

theorem Run.decoded_valid {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    Model.Ordered run.decodeV3 ∧ ∀ r ∈ run.decodeV3, CanonicalRow r := by
  have h := parse_spec accepted
  simpa only [Run.decodeV3, h.1, h.2.1] using h.2.2.2.2.2

def isPut (payload : UInt64 × UInt64) : Bool := payload.1 == 0

def decodedValue (payload : UInt64 × UInt64) : Option UInt64 :=
  if isPut payload then some payload.2 else none

/-- Turn an accepted v3 block into a sequential history with typed tombstones. -/
def Run.history {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    Sequential.History UInt64 :=
  ⟨run.decodeV3.map (Model.Entry.mapPayload decodedValue),
    List.pairwise_map.mpr ((Run.decoded_valid accepted).1.imp fun before => before)⟩

end Alvoki.Compaction
