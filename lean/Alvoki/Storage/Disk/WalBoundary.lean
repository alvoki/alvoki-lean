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
