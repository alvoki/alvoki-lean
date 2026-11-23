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

/-- Check the recorded byte count before selecting complete frames. The common
case returns the existing byte array and retains no second copy. -/
def select (length : UInt64) (wal : ByteArray) : Except String ByteArray :=
  let count := length.toNat
  if count % frameSize != 0 then .error "WAL boundary is not frame aligned"
  else if wal.size < count then .error "WAL is shorter than its durable boundary"
  else if wal.size = count then .ok wal
  else .ok (wal.extract 0 count)

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
