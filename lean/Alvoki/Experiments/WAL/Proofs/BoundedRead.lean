import Alvoki.Experiments.WAL.Proofs.DirtyRetry

namespace WalRecoverySlice

/-- One byte beyond a valid marker is enough to preserve oversized-slot rejection. -/
theorem boundedMarker_decode (slot : Nat) (bytes : Bytes) :
    decodeMarker slot (bytes.take (markerSize + 1)) = decodeMarker slot bytes := by
  by_cases fits : bytes.length ≤ markerSize + 1
  · rw [List.take_of_length_le fits]
  · have tooLarge : markerSize < bytes.length := by omega
    have width : (bytes.take (markerSize + 1)).length = markerSize + 1 := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    simp only [decodeMarker, width, ite_eq_left tooLarge, ite_eq_left (show markerSize + 1 > markerSize by omega)]
    rfl

/-- The selected prefix is identical, including a missing-bytes outcome. -/
theorem boundedData_scan (bytes : Bytes) (limit : Nat) (policy : Policy) (fits : limit ≤ 65535) :
    scan (bytes.take 65536) limit policy = scan bytes limit policy := by
  simp only [scan, List.take_take, Nat.min_eq_left (by omega : limit ≤ 65536)]

/-- The spare byte preserves the decision to repair a suffix beyond the cursor. -/
theorem boundedData_needsRepair (bytes : Bytes) (pos : Nat) (fits : pos ≤ 65535) :
    pos < (bytes.take 65536).length ↔ pos < bytes.length := by
  rw [List.length_take]
  omega

namespace Persistence

/-- A log-only observation still fits in the buffer after an uncertain append.
Boundary recovery instead uses the marker-selected prefix equation above. -/
theorem Dirty.logOnly_liveFits {known : List Bytes} {pending : Option Bytes} {image : Image}
    (dirty : Dirty .logOnly known pending image) : image.data.live.length ≤ 65536 := by
  obtain ⟨tail, possible, physical⟩ := dirty.live
  change image.data.live = encodeFrames 1 known ++ tail at physical
  have confirmed := encoded_history_size known 1
    (fun b mem => dirty.bounded b (List.mem_append_left _ mem))
  have count := dirty.fits
  simp only [List.length_append] at count
  have submitted {b : Bytes} (eqn : pending = some b) : b.length ≤ 32 := by
    exact dirty.bounded b (by simp [eqn])
  have tailFits : tail.length ≤ 52 := by
    cases possible with
    | cut takeCount =>
      cases eqn : pending with
      | none => simp [pendingFrame]
      | some b =>
        have size := submitted eqn
        simp only [pendingFrame, Option.map_some, Option.getD_some, List.length_take, frame_length]
        omega
    | damaged eqn sameSize size _ =>
      have bound := submitted eqn
      simp only [frameWithTrailer, List.length_append, checksumBytes_length,
        List.length_cons, List.length_nil, size]
      omega
  rw [physical, List.length_append]
  omega

end Persistence
end WalRecoverySlice
