import MergePhases
import ScopedBytesProofs

namespace Alvoki.ScopedBytes

theorem prepared_payload_size (prepared : Alvoki.MergePhases.PreparedReplay) :
    (sliceBytes prepared.slices.toList).size = prepared.count * 16 := by
  have complete := prepared.complete
  rw [Slice.totalLength, ← Array.foldl_toList, sliceBytes_size, Nat.zero_add] at complete
  exact complete

theorem prepared_write_refines (prepared : Alvoki.MergePhases.PreparedReplay) :
    prepared.write =
      Alvoki.pushWordFast (Alvoki.pushWordFast
        (ByteArray.emptyWithCapacity (16 + prepared.count * 16)) prepared.count.toUInt64) 1 ++
      sliceBytes prepared.slices.toList := by
  unfold Alvoki.MergePhases.PreparedReplay.write
  dsimp only
  rw [appendAll_refines]
  rfl

#print axioms Alvoki.ScopedBytes.prepared_write_refines
#print axioms Alvoki.ScopedBytes.prepared_payload_size

end Alvoki.ScopedBytes

#print axioms Alvoki.MergePhases.replayWrite_refines
