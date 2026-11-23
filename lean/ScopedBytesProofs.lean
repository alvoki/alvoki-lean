import MergePhases

namespace Alvoki.ScopedBytes

theorem Slice.model_size (slice : Slice) :
    slice.model.size = slice.length := by
  simp [Slice.model, Nat.min_eq_left slice.inBounds]

/-- The copied bytes are precisely the source extent, preceded by the existing prefix. -/
theorem append_size (builder : Builder) (slice : Slice) :
    (builder.append slice).finish.size = builder.finish.size + slice.length := by
  rw [append_refines, ByteArray.size_append, Slice.model_size]

/-- Specification for a batch of source extents, in output order. -/
def sliceBytes : List Slice → ByteArray
  | [] => ByteArray.empty
  | slice :: rest => slice.model ++ sliceBytes rest

private theorem foldl_refines (slices : List Slice) (builder : Builder) :
    (slices.foldl Builder.append builder).finish = builder.finish ++ sliceBytes slices := by
  induction slices generalizing builder with
  | nil => simp [sliceBytes]
  | cons slice rest ih =>
    rw [List.foldl_cons, ih, append_refines, ByteArray.append_assoc, sliceBytes]

theorem appendAll_refines (builder : Builder) (slices : Array Slice) :
    (builder.appendAll slices).finish = builder.finish ++ sliceBytes slices.toList := by
  rw [Builder.appendAll, ← Array.foldl_toList, foldl_refines]

theorem append_keeps_byte (builder : Builder) (slice : Slice) (i : Nat)
    (h : i < builder.finish.size) :
    (builder.append slice).finish[i]'(by rw [append_size]; omega) = builder.finish[i] := by
  simp only [append_refines, ByteArray.getElem_append_left h]

theorem append_source_byte (builder : Builder) (slice : Slice) (i : Nat)
    (h : i < slice.length) :
    (builder.append slice).finish[builder.finish.size + i]'(by rw [append_size]; omega) =
      slice.source[slice.start + i]'(by have bound := slice.inBounds; omega) := by
  simp only [append_refines, ByteArray.getElem_append_right (Nat.le_add_right ..),
    Nat.add_sub_cancel_left, Slice.model, ByteArray.getElem_extract, Nat.add_comm slice.start i]

/-- Combining two adjacent extents is byte-for-byte equivalent to emitting each. -/
theorem adjacent_model (src : ByteArray) (start len₁ len₂ : Nat)
    (bound : start + (len₁ + len₂) ≤ src.size) :
    (Slice.mk src start (len₁ + len₂) bound).model =
      (Slice.mk src start len₁ (by omega)).model ++
      (Slice.mk src (start + len₁) len₂ (by omega)).model := by
  simp only [Slice.model, ← Nat.add_assoc]
  exact ByteArray.extract_eq_extract_append_extract (start + len₁) (by omega) (by omega)

private theorem sliceBytes_size (slices : List Slice) (initial : Nat) :
    slices.foldl (fun n slice => n + slice.length) initial =
      initial + (sliceBytes slices).size := by
  induction slices generalizing initial with
  | nil => simp [sliceBytes]
  | cons slice rest ih =>
    simp [List.foldl_cons, ih, sliceBytes, Slice.model_size, Nat.add_assoc]

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

#print axioms Alvoki.ScopedBytes.appendAll_refines
#print axioms Alvoki.ScopedBytes.adjacent_model
#print axioms Alvoki.ScopedBytes.prepared_write_refines
#print axioms Alvoki.ScopedBytes.prepared_payload_size

end Alvoki.ScopedBytes

#print axioms Alvoki.MergePhases.replayWrite_refines
