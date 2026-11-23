import ByteWords

namespace Alvoki.Manifest
open Alvoki.ByteWords

/-- A generation names an ordered set of run files by consecutive index.
The WAL covers all writes beyond the installed watermark. -/
structure Checkpoint where
  generation : UInt64
  committed : UInt64
  floor : UInt64
  runCount : UInt64
  deriving Repr, DecidableEq

private def magic : UInt64 := 0x31464e4d4f564c41
private def fields (m : Checkpoint) : List UInt64 :=
  [magic, m.generation, m.committed, m.floor, m.runCount]

def encode (m : Checkpoint) : ByteArray :=
  encodeWords (fields m ++ [checksumWords (fields m)])

@[simp] theorem encode_size (m : Checkpoint) : (encode m).size = 48 := by
  simp [encode, fields]

def decode (bytes : ByteArray) : Except String Checkpoint :=
  if bytes.size ≠ 48 then .error "invalid manifest length"
  else
    let tag := word bytes 0
    let generation := word bytes 8
    let committed := word bytes 16
    let floor := word bytes 24
    let runCount := word bytes 32
    if tag != magic then .error "invalid manifest version"
    else if word bytes 40 != checksumWords [tag, generation, committed, floor, runCount] then
      .error "manifest checksum mismatch"
    else if committed < floor then .error "manifest floor exceeds the watermark"
    else .ok ⟨generation, committed, floor, runCount⟩

theorem decode_encode (m : Checkpoint) (valid : m.floor ≤ m.committed) :
    decode (encode m) = .ok m := by
  let words := fields m ++ [checksumWords (fields m)]
  have tag : word (encode m) 0 = magic := word_encodeWords words 0 (by simp [words, fields])
  have gen : word (encode m) 8 = m.generation := word_encodeWords words 1 (by simp [words, fields])
  have seq : word (encode m) 16 = m.committed := word_encodeWords words 2 (by simp [words, fields])
  have floor : word (encode m) 24 = m.floor := word_encodeWords words 3 (by simp [words, fields])
  have count : word (encode m) 32 = m.runCount := word_encodeWords words 4 (by simp [words, fields])
  have hash : word (encode m) 40 = checksumWords (fields m) :=
    word_encodeWords words 5 (by simp [words, fields])
  simp [decode, tag, gen, seq, floor, count, hash, fields, UInt64.not_lt.mpr valid]

theorem decode_reencode {bytes : ByteArray} {manifest : Checkpoint}
    (accepted : decode bytes = .ok manifest) : encode manifest = bytes := by
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
  split at accepted
  · contradiction
  cases accepted
  have original := encodeSixWords bytes (by simpa using size)
  have magicEq : word bytes 0 = magic := by simpa using version
  have checksumEq : word bytes 40 =
      checksumWords [word bytes 0, word bytes 8, word bytes 16, word bytes 24, word bytes 32] := by
    simpa using checksum
  rw [checksumEq, magicEq] at original
  exact original

end Alvoki.Manifest
