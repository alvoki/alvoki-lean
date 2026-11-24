import Alvoki.Storage.Disk.Recovery

namespace Alvoki.WAL.Boundary
open Alvoki.ByteWords

private def magic : UInt64 := 0x31544d434f564c41

/-- The number of WAL bytes selected for replay, encoded in its own synced file. -/
def encode (length : UInt64) : ByteArray :=
  encodeWords [magic, length, checksumWords [magic, length]]

@[simp] theorem encode_size (length : UInt64) : (encode length).size = 24 := by
  simp [encode]

def decode (bytes : ByteArray) : Except String UInt64 :=
  if bytes.size ≠ 24 then .error "invalid WAL boundary length"
  else if word bytes 0 != magic then .error "invalid WAL boundary version"
  else
    let length := word bytes 8
    if word bytes 16 != checksumWords [magic, length] then .error "WAL boundary checksum mismatch"
    else .ok length

theorem decode_encode (length : UInt64) : decode (encode length) = .ok length := by
  let words := [magic, length, checksumWords [magic, length]]
  have version : word (encode length) 0 = magic := word_encodeWords words 0 (by simp [words])
  have count : word (encode length) 8 = length := word_encodeWords words 1 (by simp [words])
  have hash : word (encode length) 16 = checksumWords [magic, length] :=
    word_encodeWords words 2 (by simp [words])
  simp [decode, version, count, hash]

/-- An accepted marker is exactly the canonical encoding of its byte count. -/
theorem decode_reencode {bytes : ByteArray} {length : UInt64}
    (accepted : decode bytes = .ok length) : encode length = bytes := by
  unfold decode at accepted
  split at accepted
  · contradiction
  rename_i size
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i version
  split at accepted
  · contradiction
  rename_i checksum
  cases accepted
  have bytesSize : bytes.size = 24 := by simpa using size
  have original : encodeWords [word bytes 0, word bytes 8, word bytes 16] = bytes := by
    apply eq_of_aligned_words (by simp [bytesSize])
    intro index within
    have lane : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases lane with rfl | rfl | rfl <;> rw [word_encodeWords] <;> first | rfl | simp
  have tag : word bytes 0 = magic := by simpa using version
  have digest : word bytes 16 = checksumWords [magic, word bytes 8] := by simpa using checksum
  rw [digest, tag] at original
  exact original

/-- Check the recorded byte count before selecting complete frames. The common
case returns the existing byte array and retains no second copy. -/
def select (length : UInt64) (wal : ByteArray) : Except String ByteArray :=
  let count := length.toNat
  if count % frameSize != 0 then .error "WAL boundary is not frame aligned"
  else if wal.size < count then .error "WAL is shorter than its durable boundary"
  else if wal.size = count then .ok wal
  else .ok (wal.extract 0 count)

/-- Validate the marked WAL and retain both its selected bytes and recovered table.
The selected bytes are also used if reopen must repair the on-disk WAL. -/
@[inline] def recoverMarked (base : Storage.PackedTable) (length : UInt64) (contents : ByteArray) :
    Except String (ByteArray × Storage.PackedTable) := do
  let selected ← select length contents
  let table ← Storage.recoverSelected base selected
  return (selected, table)

/-- Read and validate the optional marker before requesting the WAL. An absent
file takes a separate path from a failed read. The caller supplies bootstrap
behavior for the absent WAL. Inline the continuation to pass the bytes and
decoded count without allocating an intermediate pair. -/
@[macro_inline] def withOpenWal [Monad m] {α : Type}
    (readBoundary readWal : m (Option ByteArray)) (validate : Except String UInt64 → m UInt64)
    (missingWal : Option UInt64 → m ByteArray) (finish : Option UInt64 → ByteArray → m α) : m α := do
  let boundary ← (← readBoundary).mapM fun bytes => validate (decode bytes)
  let contents ← match ← readWal with
    | some bytes => pure bytes
    | none => missingWal boundary
  finish boundary contents

/-- For a present marker, decoding precedes even a WAL lookup that reports
an error or an absent file. -/
theorem withOpenWal_marked {α : Type} (marker : ByteArray)
    (wal : Except String (Option ByteArray))
    (missingWal : Option UInt64 → Except String ByteArray)
    (finish : Option UInt64 → ByteArray → Except String α) :
    withOpenWal (.ok (some marker)) wal id missingWal finish = (do
      let count ← decode marker
      let contents ← match ← wal with
        | some bytes => pure bytes
        | none => missingWal (some count)
      finish (some count) contents) := by
  cases decoded : decode marker <;>
    simp [withOpenWal, Option.mapM, Functor.map, Except.map, Except.bind, Bind.bind, Pure.pure,
      Except.pure, decoded]

/-- Native open error for a missing WAL required by installed metadata. -/
def missingOpenWal : String := "installed checkpoint or boundary is missing its WAL"

/-- Only empty bootstrap can open without a WAL commit marker. -/
def missingOpenMarker : String := "checkpoint or nonempty WAL is missing its commit marker"

private theorem select_eq_ok_iff {length : UInt64} {wal selected : ByteArray} :
    select length wal = .ok selected ↔
      length.toNat % frameSize = 0 ∧ length.toNat ≤ wal.size ∧
        selected = wal.extract 0 length.toNat := by
  by_cases aligned : length.toNat % frameSize = 0
  · by_cases enough : length.toNat ≤ wal.size
    · by_cases exactSize : wal.size = length.toNat
      · have entire : wal.extract 0 length.toNat = wal := by
          rw [← exactSize, ByteArray.extract_zero_size]
        simp [select, aligned, exactSize, entire, eq_comm]
      · simp [select, aligned, enough, Nat.not_lt.mpr enough, exactSize, eq_comm]
    · simp [select, aligned, enough, Nat.lt_of_not_ge enough]
  · simp [select, aligned]

theorem select_size {length : UInt64} {wal selected : ByteArray}
    (accepted : select length wal = .ok selected) : selected.size = length.toNat := by
  obtain ⟨_, fits, rfl⟩ := select_eq_ok_iff.mp accepted
  simp [Nat.min_eq_left fits]

/-- Trimming to the currently visible marker preserves selection at any still
possible marker whose length is at most the visible length. -/
theorem select_shorter_after_trim {shorter length : UInt64} {wal trimmed : ByteArray}
    (trim : select length wal = .ok trimmed) (bounded : shorter.toNat ≤ length.toNat) :
    select shorter trimmed = select shorter wal := by
  obtain ⟨_, fits, rfl⟩ := select_eq_ok_iff.mp trim
  by_cases aligned : shorter.toNat % frameSize = 0
  · have trimmedSize : (wal.extract 0 length.toNat).size = length.toNat := by
      simp [Nat.min_eq_left fits]
    have extractPrefix :
        (wal.extract 0 length.toNat).extract 0 shorter.toNat = wal.extract 0 shorter.toNat := by
      simp [ByteArray.extract_extract, Nat.min_eq_left bounded]
    have trimmedFits : shorter.toNat ≤ (wal.extract 0 length.toNat).size := by
      simpa only [trimmedSize] using bounded
    have afterTrim : select shorter (wal.extract 0 length.toNat) = .ok (wal.extract 0 shorter.toNat) :=
      select_eq_ok_iff.mpr ⟨aligned, trimmedFits, extractPrefix.symm⟩
    have beforeTrim : select shorter wal = .ok (wal.extract 0 shorter.toNat) :=
      select_eq_ok_iff.mpr ⟨aligned, Nat.le_trans bounded fits, rfl⟩
    exact afterTrim.trans beforeTrim.symm
  · simp [select, aligned]

/-- The adapter flushes the append first. Boundary installation syncs both
files before making the new boundary visible. -/
@[inline] def commit [Monad m] (appendFrame installBoundary : m Unit) : m Unit := do
  appendFrame
  installBoundary

theorem select_encoded (events : List WAL.Write) (tail : ByteArray)
    (fits : (WAL.encode events).size < UInt64.size) :
    select (WAL.encode events).size.toUInt64 (WAL.encode events ++ tail) = .ok (WAL.encode events) := by
  have count : (WAL.encode events).size.toUInt64.toNat = (WAL.encode events).size :=
    UInt64.toNat_ofNat_of_lt' fits
  have aligned : (WAL.encode events).size % frameSize = 0 := by simp [WAL.encode_size]
  have enough : ¬ (WAL.encode events ++ tail).size < (WAL.encode events).size := by
    rw [ByteArray.size_append]
    omega
  unfold select
  simp only [count, aligned, bne_self_eq_false, Bool.false_eq_true, ite_false, enough]
  split
  · rename_i sameSize
    rw [ByteArray.size_append] at sameSize
    have empty : tail = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (by omega)
    simp [empty]
  · rw [ByteArray.extract_append_eq_left rfl]

/-- No property of the bytes beyond the selected boundary is needed for replay. -/
theorem recover_encoded (base : Storage.PackedTable) (events : List WAL.Write) (tail : ByteArray)
    (fits : (WAL.encode events).size < UInt64.size) :
    (do
      let count ← decode (encode (WAL.encode events).size.toUInt64)
      let wal ← select count (WAL.encode events ++ tail)
      Storage.recoverCheckpoint base wal) = Storage.recoverCheckpoint base (WAL.encode events) := by
  rw [decode_encode]
  change (do
    let wal ← select (WAL.encode events).size.toUInt64 (WAL.encode events ++ tail)
    Storage.recoverCheckpoint base wal) = _
  rw [select_encoded events tail fits]
  rfl

end Alvoki.WAL.Boundary
