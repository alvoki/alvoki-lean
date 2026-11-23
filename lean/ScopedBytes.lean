import Std

namespace Alvoki.ScopedBytes

/-- A borrowed source extent. Validation evidence is erased in native code. -/
structure Slice where
  source : ByteArray
  start : Nat
  length : Nat
  inBounds : start + length ≤ source.size

/-- An append-only output. Capacity is a hint supplied to the stock allocator. -/
structure Builder where
  private mk ::
  private bytes : ByteArray

@[inline] def Builder.withCapacity (capacity : Nat) : Builder :=
  ⟨ByteArray.emptyWithCapacity capacity⟩

/-- Start appending after an existing prefix, preserving ordinary ByteArray value semantics. -/
@[inline] def Builder.ofPrefix (initial : ByteArray) : Builder :=
  ⟨initial⟩

@[inline] def Builder.finish (builder : Builder) : ByteArray :=
  builder.bytes

/-- Stock copy semantics, including clipping for callers using raw offsets. -/
@[inline] def Builder.copyToTail (builder : Builder) (source : @& ByteArray)
    (start length : Nat) : Builder :=
  ⟨source.copySlice start builder.bytes builder.bytes.size length false⟩

/-- Appends the entire validated extent in one call to the standard runtime. -/
@[inline] def Builder.append (builder : Builder) (slice : @& Slice) : Builder :=
  builder.copyToTail slice.source slice.start slice.length

def Builder.appendAll (builder : Builder) (slices : @& Array Slice) : Builder :=
  slices.foldl Builder.append builder

def Slice.totalLength (slices : @& Array Slice) : Nat :=
  slices.foldl (fun total slice => total + slice.length) 0

@[inline] def Slice.model (slice : Slice) : ByteArray :=
  slice.source.extract slice.start (slice.start + slice.length)

theorem finish_withCapacity (capacity : Nat) :
    (Builder.withCapacity capacity).finish = ByteArray.empty := rfl

theorem copyToTail_refines (builder : Builder) (source : ByteArray) (start length : Nat) :
    (builder.copyToTail source start length).finish =
      builder.finish ++ source.extract start (start + length) := by
  unfold Builder.copyToTail Builder.finish
  dsimp only
  rw [ByteArray.copySlice_eq_append, ByteArray.extract_zero_size]
  have empty : builder.bytes.extract
      (builder.bytes.size + min length (source.data.size - start)) builder.bytes.data.size =
      ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff, ← ByteArray.size_data]
    exact Nat.le_trans (Nat.min_le_right ..) (Nat.le_add_right ..)
  rw [empty, ByteArray.append_empty]

theorem append_refines (builder : Builder) (slice : Slice) :
    (builder.append slice).finish = builder.finish ++ slice.model :=
  copyToTail_refines builder slice.source slice.start slice.length

end Alvoki.ScopedBytes
