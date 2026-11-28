import Alvoki.Experiments.SSTable.Recursive.FilterImageProofs

namespace ImmutableSSTable.Recursive

open Unified (Layout Ref Checksum checksumSize encodePacket encodePacket_size)

/-- The append transition used by the actual streaming writer emits the exact
filter for the rows it will pass to encodeData. The theorem concerns the
append at this program point. The completed image must retain this slice. -/
theorem Writer.writeFilter_appends
    (writer : Writer (EStateM String world) String) (bytesFor : world → ByteArray)
    (write : ∀ start payload reached, writer.sink.write payload start = .ok () reached →
      bytesFor reached = bytesFor start ++ payload)
    (enabled : writer.options.membershipFilter = true) (active : useFilter rows.size = true)
    (observed : writer.writeFilter offset rows start = .ok next reached) :
    next = offset + filterPacketSize rows.size ∧
    bytesFor reached = bytesFor start ++ encodePacket writer.crc writer.layout.tableId
      filterKind offset (Bloom.build rows) := by
  have length : (Bloom.build rows).size + checksumSize = filterPacketSize rows.size := by
    rw [Bloom.build_size, filterPacketSize]
  have bounded : filterPacketSize rows.size ≤ maxRowSize := by
    unfold useFilter at active
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp active).2
  let payload := encodePacket writer.crc writer.layout.tableId filterKind offset (Bloom.build rows)
  unfold Writer.writeFilter Writer.writePacket at observed
  simp only [enabled, active, Bool.and_self, ↓reduceIte, length, bounded] at observed
  by_cases fits : offset + filterPacketSize rows.size + footerPacketSize ≤ maxFileSize
  · simp only [fits, ↓reduceIte, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at observed
    cases sent : writer.sink.write payload start with
    | error err after =>
      change writer.sink.write payload start = .error err after at sent
      unfold payload at sent
      simp [sent] at observed
    | ok result after =>
      cases result
      have appended := write start payload after sent
      unfold payload at sent
      rw [sent] at observed
      cases observed
      exact ⟨rfl, appended⟩
  · simp only [fits, ↓reduceIte, Bind.bind, EStateM.bind] at observed
    cases observed

/-- With a sink at its exact append cursor, the bytes just emitted are the
filter slice for the following data reference. Later append proofs can
retain this slice through the root and footer writes. -/
theorem Writer.writeFilter_packetAt
    (writer : Writer (EStateM String world) String) (bytesFor : world → ByteArray)
    (write : ∀ start payload reached, writer.sink.write payload start = .ok () reached →
      bytesFor reached = bytesFor start ++ payload)
    (enabled : writer.options.membershipFilter = true)
    (active : useFilter rows.size = true)
    (run : writer.writeFilter (bytesFor start).size rows start = .ok ref.offset reached)
    (count : ref.count = rows.size) :
    FilterAt writer.layout writer.crc (bytesFor reached) ref rows := by
  obtain ⟨position, appended⟩ := writer.writeFilter_appends bytesFor write enabled active run
  let filterStart := (bytesFor start).size
  let filterSize := filterPacketSize ref.count
  have offset : ref.offset = filterStart + filterSize := by simpa [filterStart, filterSize, count] using position
  have bound : filterSize ≤ maxRowSize := by
    unfold useFilter at active
    simpa [filterSize, count] using (of_decide_eq_true (Bool.and_eq_true_iff.mp active).2 :
      filterPacketSize rows.size ≤ maxRowSize)
  have length : filterSize = (Bloom.build rows).size + checksumSize := by
    simp [filterSize, filterPacketSize, count, Bloom.build_size]
  have ends : ref.offset - filterSize = filterStart := by omega
  refine ⟨by change filterSize ≤ ref.offset; omega, ⟨length, bound, ?_, ?_⟩⟩
  · change ref.offset - filterSize + filterSize ≤ (bytesFor reached).size
    rw [ends, appended, ByteArray.size_append, encodePacket_size, length]
    exact Nat.le_refl _
  · change (bytesFor reached).extract (ref.offset - filterSize)
      (ref.offset - filterSize + filterSize) = _
    rw [ends, appended]
    exact ByteArray.extract_append_eq_right rfl (by rw [encodePacket_size, length])

end ImmutableSSTable.Recursive
