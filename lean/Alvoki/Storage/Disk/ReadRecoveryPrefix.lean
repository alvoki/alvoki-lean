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

/-- Read up to the requested prefix, stopping at EOF or the limit. A
positive short read is followed by another request for the remainder. -/
@[specialize] def readPrefixUntilEofWith [Monad m] [MonadExceptOf IO.Error m]
    (mismatch : IO.Error) (read : USize → m ByteArray) (remaining : Nat)
    (bytes : ByteArray) : m ByteArray := do
  if remaining = 0 then return bytes
  let chunk ← read remaining.toUSize
  if chunk.size = 0 then return bytes
  if _within : chunk.size ≤ remaining then
    let bytes := if bytes.isEmpty then chunk else bytes ++ chunk
    readPrefixUntilEofWith mismatch read (remaining - chunk.size) bytes
  else throw mismatch
termination_by remaining

/-- A positive short chunk is followed by the remaining request.
If that request reports an error, the same diagnostic and state return. -/
theorem readPrefixUntilEofWith_shortThenError {state : Type}
    (mismatch : IO.Error) (read : USize → EStateM IO.Error state ByteArray)
    {remaining : Nat} {bytes chunk : ByteArray} {before next after : state} {cause : IO.Error}
    (positive : 0 < chunk.size) (short : chunk.size < remaining)
    (first : read remaining.toUSize before = .ok chunk next)
    (second : read (remaining - chunk.size).toUSize next = .error cause after) :
    readPrefixUntilEofWith mismatch read remaining bytes before = .error cause after := by
  have pending : remaining ≠ 0 := by omega
  have notEOF : chunk.size ≠ 0 := by omega
  have more : remaining - chunk.size ≠ 0 := by omega
  rw [readPrefixUntilEofWith]
  simp only [pending, ↓reduceIte, Bind.bind, EStateM.bind, first, notEOF, Nat.le_of_lt short, ↓reduceDIte]
  rw [readPrefixUntilEofWith]
  simp only [more, ↓reduceIte, Bind.bind, EStateM.bind, second]

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

theorem readExactPrefixWith_readError {state : Type} (mismatch : IO.Error)
    (read : USize → EStateM IO.Error state ByteArray) {remaining : Nat} {offset next : state} {bytes : ByteArray}
    {cause : IO.Error} (pending : remaining ≠ 0)
    (reported : read remaining.toUSize offset = .error cause next) :
    readExactPrefixWith mismatch read remaining bytes offset = .error cause next := by
  rw [readExactPrefixWith]
  simp only [pending, ↓reduceIte, Bind.bind, EStateM.bind, reported]

/-- A positive short chunk continues on the same callback with the
remaining byte count. A later read error keeps its own diagnostic. -/
theorem readExactPrefixWith_shortThenError {state : Type} (mismatch : IO.Error)
    (read : USize → EStateM IO.Error state ByteArray) {count : Nat} {before afterChunk failed : state}
    {chunk : ByteArray} {cause : IO.Error}
    (positive : 0 < chunk.size) (short : chunk.size < count)
    (first : read count.toUSize before = .ok chunk afterChunk)
    (second : read (count - chunk.size).toUSize afterChunk = .error cause failed) :
    readExactPrefixWith mismatch read count ByteArray.empty before = .error cause failed := by
  rw [readExactPrefixWith]
  have remaining : count - chunk.size ≠ 0 := by omega
  have valid : 0 < chunk.size ∧ chunk.size ≤ count := ⟨positive, Nat.le_of_lt short⟩
  have nonzero : count ≠ 0 := by omega
  simp only [nonzero, ↓reduceIte, Bind.bind, EStateM.bind, first, valid]
  exact readExactPrefixWith_readError mismatch read remaining second

theorem readExactPrefixWith_badChunk (mismatch : IO.Error)
    (read : USize → EStateM IO.Error Nat ByteArray) {remaining offset next : Nat} {bytes chunk : ByteArray}
    (pending : remaining ≠ 0) (reported : read remaining.toUSize offset = .ok chunk next)
    (invalid : ¬ (0 < chunk.size ∧ chunk.size ≤ remaining)) :
    readExactPrefixWith mismatch read remaining bytes offset = .error mismatch next := by
  rw [readExactPrefixWith]
  simp only [pending, ↓reduceIte, Bind.bind, EStateM.bind, reported, invalid]
  rfl

/-- Every completed prefix contains the exact fragments of the one opened
file, in cursor order, and preserves the local binding across chunks. -/
theorem readExactPrefixWith_successAtCursor {state : Type} (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error state ByteArray}
    (cursor : state → Nat) (bound : state → Prop)
    (observes : ∀ requested before after chunk, bound before → read requested before = .ok chunk after →
      bound after ∧ cursor after = cursor before + chunk.size ∧
      chunk = source.extract (cursor before) (cursor after))
    (remaining : Nat) {before after : state} {bytes out : ByteArray} (initial : bound before)
    (reported : readExactPrefixWith mismatch read remaining bytes before = .ok out after) :
    bound after ∧ cursor after = cursor before + remaining ∧
      out = bytes ++ source.extract (cursor before) (cursor after) := by
  rw [readExactPrefixWith] at reported
  by_cases finished : remaining = 0
  · subst remaining
    have result : bytes = out ∧ before = after := by
      simpa only [↓reduceIte, EStateM.pure, Pure.pure, EStateM.Result.ok.injEq] using reported
    obtain ⟨rfl, rfl⟩ := result
    simp [initial]
  · rw [ite_eq_right finished] at reported
    simp only [Bind.bind, EStateM.bind] at reported
    cases reading : read remaining.toUSize before with
    | error cause reached => rw [reading] at reported; contradiction
    | ok chunk reached =>
      rw [reading] at reported
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · simp only [valid] at reported
        have ⟨kept, advanced, payload⟩ := observes remaining.toUSize before reached chunk initial reading
        obtain ⟨finalBinding, endAt, output⟩ :=
          readExactPrefixWith_successAtCursor mismatch cursor bound observes (remaining - chunk.size) kept reported
        refine ⟨finalBinding, by omega, ?_⟩
        rw [output, appendPrefixChunk, ByteArray.append_assoc, payload]
        rw [← ByteArray.extract_eq_extract_append_extract (cursor reached) (by omega) (by omega)]
      · simp only [valid, ↓reduceDIte] at reported
        contradiction
termination_by remaining
decreasing_by omega

/-- Every completed prefix contains the exact fragments of the one opened
file, in cursor order, regardless of how the successful reads split it. -/
theorem readExactPrefixWith_success (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (remaining : Nat)
    {offset next : Nat} {bytes out : ByteArray}
    (reported : readExactPrefixWith mismatch read remaining bytes offset = .ok out next) :
    next = offset + remaining ∧ out = bytes ++ source.extract offset next := by
  have projected := readExactPrefixWith_successAtCursor mismatch id (fun _ => True)
    (fun requested before after chunk _ returned =>
      ⟨True.intro, observes requested before after chunk returned⟩) remaining True.intro reported
  exact projected.2

/-- A healthy read can return any positive chunk within the pending request.
The caller supplies successful primitive reads only for requests covered
by the stable file and representable as machine sizes. -/
def PrefixChunksAvailable (source : ByteArray) (read : USize → EStateM IO.Error Nat ByteArray) : Prop :=
  ∀ offset count, 0 < count → count < USize.size → offset + count ≤ source.size →
    ∃ chunk next, read count.toUSize offset = .ok chunk next ∧ 0 < chunk.size ∧ chunk.size ≤ count

/-- Bounded reads return the same cursor prefix, including a short
prefix only when a positive request actually reaches EOF. -/
theorem readPrefixUntilEofWith_successAtCursor {state : Type} (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error state ByteArray}
    (cursor : state → Nat) (bound : state → Prop)
    (observes : ∀ requested before after chunk, bound before → read requested before = .ok chunk after →
      bound after ∧ cursor after = cursor before + chunk.size ∧
      chunk = source.extract (cursor before) (cursor after) ∧
      (0 < requested.toNat → chunk.size = 0 → source.size ≤ cursor before))
    (remaining : Nat) (fits : remaining < USize.size) {before after : state} {bytes out : ByteArray}
    (initial : bound before) (covered : cursor before ≤ source.size)
    (reported : readPrefixUntilEofWith mismatch read remaining bytes before = .ok out after) :
    bound after ∧ cursor after = cursor before + min remaining (source.size - cursor before) ∧
      out = bytes ++ source.extract (cursor before) (cursor after) := by
  rw [readPrefixUntilEofWith] at reported
  by_cases finished : remaining = 0
  · subst remaining
    have result : bytes = out ∧ before = after := by
      simpa only [↓reduceIte, EStateM.pure, Pure.pure, EStateM.Result.ok.injEq] using reported
    obtain ⟨rfl, rfl⟩ := result
    simp [initial]
  · rw [ite_eq_right finished] at reported
    simp only [Bind.bind, EStateM.bind] at reported
    cases reading : read remaining.toUSize before with
    | error cause reached => rw [reading] at reported; contradiction
    | ok chunk reached =>
      rw [reading] at reported
      obtain ⟨kept, advanced, payload, eof⟩ :=
        observes remaining.toUSize before reached chunk initial reading
      by_cases empty : chunk.size = 0
      · have requested : 0 < remaining.toUSize.toNat := by
          simpa only [USize.toNat_ofNat_of_lt' fits] using Nat.pos_of_ne_zero finished
        have exhausted := eof requested empty
        simp only [empty, ↓reduceIte, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at reported
        obtain ⟨rfl, rfl⟩ := reported
        simp [kept, show cursor reached = cursor before by omega,
          show source.size - cursor before = 0 by omega]
      · by_cases within : chunk.size ≤ remaining
        · simp only [empty, ↓reduceIte, within, ↓reduceDIte] at reported
          have readSize := congrArg ByteArray.size payload
          rw [ByteArray.size_extract] at readSize
          have stillCovered : cursor reached ≤ source.size := by omega
          obtain ⟨finalBinding, endAt, output⟩ :=
            readPrefixUntilEofWith_successAtCursor mismatch cursor bound observes
              (remaining - chunk.size) (by omega) kept stillCovered reported
          refine ⟨finalBinding, by omega, ?_⟩
          rw [output, appendPrefixChunk, ByteArray.append_assoc, payload]
          rw [← ByteArray.extract_eq_extract_append_extract (cursor reached) (by omega) (by omega)]
        · simp only [empty, ↓reduceIte, within, ↓reduceDIte] at reported
          contradiction
termination_by remaining
decreasing_by omega

/-- Healthy primitive reads of the covered interval complete despite
positive short reads and leave the cursor at the end of the interval. -/
theorem readExactPrefixWith_completes (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailable source read)
    (remaining : Nat) (fits : remaining < USize.size) {offset : Nat} {bytes : ByteArray}
    (covered : offset + remaining ≤ source.size) :
    readExactPrefixWith mismatch read remaining bytes offset =
      .ok (bytes ++ source.extract offset (offset + remaining)) (offset + remaining) := by
  rw [readExactPrefixWith]
  by_cases finished : remaining = 0
  · subst remaining
    simp [Pure.pure, EStateM.pure]
  · obtain ⟨chunk, next, reported, progress, within⟩ := available offset remaining (by omega) fits covered
    obtain ⟨cursor, payload⟩ := observes remaining.toUSize offset next chunk reported
    have endAt : next + (remaining - chunk.size) = offset + remaining := by omega
    have later := readExactPrefixWith_completes mismatch observes available
      (remaining - chunk.size) (by omega) (offset := next)
      (bytes := if bytes.isEmpty then chunk else bytes ++ chunk) (by omega)
    have joined : (if bytes.isEmpty then chunk else bytes ++ chunk) ++
        source.extract next (offset + remaining) = bytes ++ source.extract offset (offset + remaining) := by
      rw [appendPrefixChunk, ByteArray.append_assoc, payload,
        ← ByteArray.extract_eq_extract_append_extract next (by omega) (by omega)]
    rw [endAt, joined] at later
    simp only [finished, ↓reduceIte, Bind.bind, EStateM.bind, reported, progress, within, and_self, ↓reduceDIte]
    exact later
termination_by remaining
decreasing_by omega

/-- A newly opened description starts at offset zero. Its admitted read
returns exactly the selected bytes and leaves the cursor at their end. -/
theorem readExactPrefixWith_completesAtStart (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailable source read)
    (count : Nat) (fits : count < USize.size) (covered : count ≤ source.size) :
    readExactPrefixWith mismatch read count ByteArray.empty 0 = .ok (source.extract 0 count) count := by
  simpa only [Nat.zero_add, ByteArray.empty_append] using
    readExactPrefixWith_completes mismatch observes available count fits (offset := 0)
      (bytes := ByteArray.empty) (by simpa using covered)

/-- Reading an admitted complete run or sealed WAL returns the file bytes. -/
theorem readExactPrefixWith_completesFile (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailable source read)
    (fits : source.size < USize.size) :
    readExactPrefixWith mismatch read source.size ByteArray.empty 0 = .ok source source.size := by
  simpa only [ByteArray.extract_zero_size] using
    readExactPrefixWith_completesAtStart mismatch observes available source.size fits (Nat.le_refl _)

/-- Healthy reads through the end of a stable file return at most the
requested bytes. An empty report marks EOF. -/
def PrefixChunksAvailableUntilEof (source : ByteArray) (read : USize → EStateM IO.Error Nat ByteArray) : Prop :=
  ∀ offset count, 0 < count → count < USize.size → offset ≤ source.size →
    ∃ chunk next, read count.toUSize offset = .ok chunk next ∧ chunk.size ≤ count ∧
      (chunk.size = 0 → offset = source.size)

/-- The bounded reader returns the exact prefix of the observed file and
advances its cursor only through those bytes. -/
theorem readPrefixUntilEofWith_completes (mismatch : IO.Error)
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailableUntilEof source read)
    (remaining : Nat) (fits : remaining < USize.size) {offset : Nat} {bytes : ByteArray}
    (withinFile : offset ≤ source.size) :
    let stop := min (offset + remaining) source.size
    readPrefixUntilEofWith mismatch read remaining bytes offset =
      .ok (bytes ++ source.extract offset stop) stop := by
  dsimp only
  rw [readPrefixUntilEofWith]
  by_cases finished : remaining = 0
  · subst remaining
    simp [Nat.min_eq_left withinFile, Pure.pure, EStateM.pure]
  · obtain ⟨chunk, next, reported, within, ended⟩ := available offset remaining (by omega) fits withinFile
    obtain ⟨cursor, payload⟩ := observes remaining.toUSize offset next chunk reported
    by_cases empty : chunk.size = 0
    · have eof := ended empty
      have stop : min (offset + remaining) source.size = offset := by omega
      simp [finished, empty, reported, stop, cursor, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    · have nextWithin : next ≤ source.size := by
        have length := congrArg ByteArray.size payload
        rw [ByteArray.size_extract] at length
        omega
      have endAt : next + (remaining - chunk.size) = offset + remaining := by omega
      have later := readPrefixUntilEofWith_completes mismatch observes available
        (remaining - chunk.size) (by omega) (offset := next)
        (bytes := if bytes.isEmpty then chunk else bytes ++ chunk) nextWithin
      have joined : (if bytes.isEmpty then chunk else bytes ++ chunk) ++
          source.extract next (min (offset + remaining) source.size) =
          bytes ++ source.extract offset (min (offset + remaining) source.size) := by
        rw [appendPrefixChunk, ByteArray.append_assoc, payload,
          ← ByteArray.extract_eq_extract_append_extract next (by omega) (by omega)]
      dsimp only at later
      rw [endAt, joined] at later
      simp only [finished, ↓reduceIte, Bind.bind, EStateM.bind, reported, empty, within, ↓reduceDIte]
      exact later
termination_by remaining
decreasing_by omega

end Alvoki.Storage
