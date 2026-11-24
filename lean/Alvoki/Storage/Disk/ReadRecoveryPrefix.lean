import Init.Data.ByteArray.Lemmas
import Init.System.IO

namespace Alvoki.Storage

/-- Read exactly the requested prefix, tolerating positive short reads.
A zero or oversized chunk stops at the reached descriptor cursor. -/
@[specialize] def readExactPrefixWith [Monad m] [MonadExceptOf IO.Error m]
    (mismatch : IO.Error) (read : USize → m ByteArray) (remaining : Nat)
    (bytes : ByteArray) : m ByteArray := do
  if remaining = 0 then return bytes
  let chunk ← read remaining.toUSize
  if _valid : 0 < chunk.size ∧ chunk.size ≤ remaining then
    let bytes := if bytes.isEmpty then chunk else bytes ++ chunk
    readExactPrefixWith mismatch read (remaining - chunk.size) bytes
  else throw mismatch
termination_by remaining

/-- Interpret successful reads on one open file description. The state is
the cursor of that description. The binding and immutability of the file
are supplied by the caller. Error reports may advance the cursor. -/
def PrefixChunkObserves (source : ByteArray) (read : USize → EStateM IO.Error Nat ByteArray) : Prop :=
  ∀ requested offset next chunk, read requested offset = .ok chunk next →
    next = offset + chunk.size ∧ chunk = source.extract offset next

private theorem appendPrefixChunk (bytes chunk : ByteArray) :
    (if bytes.isEmpty then chunk else bytes ++ chunk) = bytes ++ chunk := by
  split
  · rename_i empty
    have zero : bytes.size = 0 := by simpa [ByteArray.isEmpty] using empty
    rw [ByteArray.size_eq_zero_iff.mp zero, ByteArray.empty_append]
  · rfl

theorem readExactPrefixWith_readError (mismatch : IO.Error)
    (read : USize → EStateM IO.Error Nat ByteArray) {remaining offset next : Nat} {bytes : ByteArray}
    {cause : IO.Error} (pending : remaining ≠ 0)
    (reported : read remaining.toUSize offset = .error cause next) :
    readExactPrefixWith mismatch read remaining bytes offset = .error cause next := by
  rw [readExactPrefixWith]
  simp only [pending, ↓reduceIte, Bind.bind, EStateM.bind, reported]

theorem readExactPrefixWith_badChunk (mismatch : IO.Error)
    (read : USize → EStateM IO.Error Nat ByteArray) {remaining offset next : Nat} {bytes chunk : ByteArray}
    (pending : remaining ≠ 0) (reported : read remaining.toUSize offset = .ok chunk next)
    (invalid : ¬ (0 < chunk.size ∧ chunk.size ≤ remaining)) :
    readExactPrefixWith mismatch read remaining bytes offset = .error mismatch next := by
  rw [readExactPrefixWith]
  simp only [pending, ↓reduceIte, Bind.bind, EStateM.bind, reported, invalid]
  rfl

/-- Every completed prefix contains the exact fragments of the one opened
file, in cursor order, regardless of how the successful reads split it. -/
theorem readExactPrefixWith_success (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (remaining : Nat)
    {offset next : Nat} {bytes out : ByteArray}
    (reported : readExactPrefixWith mismatch read remaining bytes offset = .ok out next) :
    next = offset + remaining ∧ out = bytes ++ source.extract offset next := by
  rw [readExactPrefixWith] at reported
  by_cases finished : remaining = 0
  · subst remaining
    have result : bytes = out ∧ offset = next := by
      simpa only [↓reduceIte, EStateM.pure, Pure.pure, EStateM.Result.ok.injEq] using reported
    obtain ⟨rfl, rfl⟩ := result
    simp
  · rw [ite_eq_right finished] at reported
    simp only [Bind.bind, EStateM.bind] at reported
    cases reading : read remaining.toUSize offset with
    | error cause reached => rw [reading] at reported; contradiction
    | ok chunk reached =>
      rw [reading] at reported
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · simp only [valid] at reported
        have ⟨cursor, payload⟩ := observes remaining.toUSize offset reached chunk reading
        obtain ⟨endAt, output⟩ :=
          readExactPrefixWith_success mismatch observes (remaining - chunk.size) reported
        refine ⟨by omega, ?_⟩
        rw [output, appendPrefixChunk, ByteArray.append_assoc, payload]
        rw [← ByteArray.extract_eq_extract_append_extract reached (by omega) (by omega)]
      · simp only [valid, ↓reduceDIte] at reported
        contradiction
termination_by remaining
decreasing_by omega

end Alvoki.Storage
