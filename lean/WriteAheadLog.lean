import ByteWords

namespace Alvoki.WAL
open Alvoki.ByteWords

/-- One committed-sequence assignment. An absent value is a delete. -/
structure Write where
  sequence : UInt64
  key : UInt64
  value : Option UInt64
  deriving Repr, DecidableEq

def frameSize : Nat := 48

private def magic : UInt64 := 0x314c41574f564c41

private def fieldChecksum (tag sequence key kind value : UInt64) : UInt64 :=
  checksumWords [tag, sequence, key, kind, value]

private def kind (event : Write) : UInt64 := if event.value.isSome then 0 else 1
private def payload (event : Write) : UInt64 := event.value.getD 0

def encodeFrame (event : Write) : ByteArray :=
  encodeWords [magic, event.sequence, event.key, kind event, payload event,
    fieldChecksum magic event.sequence event.key (kind event) (payload event)]

@[simp] theorem encodeFrame_size (event : Write) : (encodeFrame event).size = frameSize := by
  simp [encodeFrame, frameSize]

def decodeFrame (bytes : ByteArray) : Except String Write :=
  if bytes.size ≠ frameSize then .error "invalid WAL frame length"
  else
    let tag := word bytes 0
    let sequence := word bytes 8
    let key := word bytes 16
    let kind := word bytes 24
    let value := word bytes 32
    if tag != magic then .error "invalid WAL version"
    else if word bytes 40 != fieldChecksum tag sequence key kind value then .error "WAL checksum mismatch"
    else if kind == 0 then .ok ⟨sequence, key, some value⟩
    else if kind == 1 && value == 0 then .ok ⟨sequence, key, none⟩
    else .error "invalid WAL operation"

private theorem encodeFrame_words (e : Write) :
    word (encodeFrame e) 0 = magic ∧
    word (encodeFrame e) 8 = e.sequence ∧
    word (encodeFrame e) 16 = e.key ∧
    word (encodeFrame e) 24 = kind e ∧
    word (encodeFrame e) 32 = payload e ∧
    word (encodeFrame e) 40 = fieldChecksum magic e.sequence e.key (kind e) (payload e) := by
  let words := [magic, e.sequence, e.key, kind e, payload e,
    fieldChecksum magic e.sequence e.key (kind e) (payload e)]
  exact ⟨word_encodeWords words 0 (by simp [words]), word_encodeWords words 1 (by simp [words]),
    word_encodeWords words 2 (by simp [words]), word_encodeWords words 3 (by simp [words]),
    word_encodeWords words 4 (by simp [words]), word_encodeWords words 5 (by simp [words])⟩

theorem decodeFrame_encode (event : Write) : decodeFrame (encodeFrame event) = .ok event := by
  obtain ⟨tag, seq, key, kindWord, val, hash⟩ := encodeFrame_words event
  simp [decodeFrame, tag, seq, key, kindWord, val, hash]
  cases event with
  | mk seq key value => cases value <;> simp [kind, payload]

/-- A successful decoder accepts only the canonical bytes of the decoded event. -/
theorem decodeFrame_reencode {bytes : ByteArray} {event : Write}
    (accepted : decodeFrame bytes = .ok event) : encodeFrame event = bytes := by
  unfold decodeFrame at accepted
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
  have sizeEq : bytes.size = 48 := by simpa [frameSize] using size
  have magicEq : word bytes 0 = magic := by simpa using version
  have checksumEq : word bytes 40 =
      fieldChecksum (word bytes 0) (word bytes 8) (word bytes 16) (word bytes 24) (word bytes 32) := by
    simpa using checksum
  have finish (op : Option UInt64)
      (tag : word bytes 24 = kind ⟨word bytes 8, word bytes 16, op⟩)
      (value : word bytes 32 = payload ⟨word bytes 8, word bytes 16, op⟩) :
      encodeFrame ⟨word bytes 8, word bytes 16, op⟩ = bytes := by
    have original := encodeSixWords bytes sizeEq
    rw [checksumEq, magicEq, tag, value] at original
    exact original
  split at accepted
  · rename_i putTag
    cases accepted
    exact finish _ (by simpa [kind] using putTag) rfl
  · split at accepted
    · rename_i deleteTag
      cases accepted
      have fields : word bytes 24 = 1 ∧ word bytes 32 = 0 := by simpa using deleteTag
      exact finish _ fields.1 fields.2
    · contradiction

/-- A complete frame with a bad checksum, format, or tag fails recovery.
A final incomplete frame is outside the complete frame count. -/
private def decodeFrom (bytes : @& ByteArray) (offset remaining : Nat)
    (reversed : List Write) : Except String (List Write) :=
  match remaining with
  | 0 => .ok reversed.reverse
  | n + 1 =>
    match decodeFrame (bytes.extract offset (offset + frameSize)) with
    | .error message => .error message
    | .ok event => decodeFrom bytes (offset + frameSize) n (event :: reversed)

def decode (bytes : @& ByteArray) : Except String (List Write) :=
  decodeFrom bytes 0 (bytes.size / frameSize) []

def encode : List Write → ByteArray
  | [] => ByteArray.empty
  | event :: rest => encodeFrame event ++ encode rest

theorem encode_append (left right : List Write) :
    encode (left ++ right) = encode left ++ encode right := by
  induction left with
  | nil => simp [encode]
  | cons event rest ih => simp [encode, ih, ByteArray.append_assoc]

@[simp] theorem encode_size (events : List Write) :
    (encode events).size = frameSize * events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    simp only [encode, ByteArray.size_append, encodeFrame_size, ih, frameSize, List.length_cons]
    omega

private theorem decodeFrom_shift (prefixBytes bytes : ByteArray) (offset remaining : Nat)
    (reversed : List Write) :
    decodeFrom (prefixBytes ++ bytes) (prefixBytes.size + offset) remaining reversed =
      decodeFrom bytes offset remaining reversed := by
  induction remaining generalizing offset reversed with
  | zero => rfl
  | succ n ih =>
    rw [decodeFrom, decodeFrom, Nat.add_assoc, ByteArray.extract_append_size_add]
    split
    · rfl
    · exact ih (offset + frameSize) _

private theorem decodeFrom_append_encoded (events : List Write) (tail : ByteArray) (remaining : Nat)
    (reversed : List Write) :
    decodeFrom (encode events ++ tail) 0 (events.length + remaining) reversed =
      decodeFrom tail 0 remaining (events.reverse ++ reversed) := by
  induction events generalizing reversed with
  | nil => simp [encode]
  | cons event rest ih =>
    simp only [encode, ByteArray.append_assoc, List.length_cons,
      Nat.add_right_comm rest.length 1 remaining, decodeFrom, Nat.zero_add]
    rw [ByteArray.extract_append_eq_left (encodeFrame_size event).symm, decodeFrame_encode]
    dsimp only
    have shifted := decodeFrom_shift (encodeFrame event) (encode rest ++ tail) 0
      (rest.length + remaining) (event :: reversed)
    rw [encodeFrame_size, Nat.add_zero] at shifted
    rw [shifted, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem decode_ignores_incomplete_tail (events : List Write) (tail : ByteArray)
    (incomplete : tail.size < frameSize) :
    decode (encode events ++ tail) = .ok events := by
  have count : (encode events ++ tail).size / frameSize = events.length := by
    rw [ByteArray.size_append, encode_size]
    change (48 * events.length + tail.size) / 48 = events.length
    change tail.size < 48 at incomplete
    omega
  have parsed := decodeFrom_append_encoded events tail 0 []
  rw [decode, count]
  simpa [decodeFrom] using parsed

theorem decode_encode (events : List Write) : decode (encode events) = .ok events := by
  have h := decode_ignores_incomplete_tail events ByteArray.empty (by decide)
  simpa only [ByteArray.append_empty] using h

/-- A complete, malformed last frame cannot be treated as a short tear by the
current decoder. A durable replay boundary must come from outside this codec. -/
theorem decode_bad_final_frame (events : List Write) {last : ByteArray} {message : String}
    (full : last.size = frameSize) (bad : decodeFrame last = .error message) :
    decode (encode events ++ last) = .error message := by
  have count : (encode events ++ last).size / frameSize = events.length + 1 := by
    rw [ByteArray.size_append, encode_size, full]
    change (48 * events.length + 48) / 48 = events.length + 1
    omega
  have entire : last.extract 0 frameSize = last := by
    rw [← full, ByteArray.extract_zero_size]
  rw [decode, count, decodeFrom_append_encoded]
  simp [decodeFrom, entire, bad]

/-- After replay validates the complete frames, return replacement bytes only for a short tail. -/
def repairPrefix (bytes : ByteArray) : Option ByteArray :=
  let complete := bytes.size / frameSize * frameSize
  if complete < bytes.size then some (bytes.extract 0 complete) else none

theorem repairPrefix_encode (events : List Write) (tail : ByteArray) (incomplete : tail.size < frameSize) :
    repairPrefix (encode events ++ tail) = if tail.size = 0 then none else some (encode events) := by
  have length : (encode events ++ tail).size / frameSize * frameSize = (encode events).size := by
    rw [ByteArray.size_append, encode_size]
    change (48 * events.length + tail.size) / 48 * 48 = 48 * events.length
    change tail.size < 48 at incomplete
    omega
  unfold repairPrefix
  dsimp only
  rw [length, ByteArray.extract_append_eq_left rfl, ByteArray.size_append]
  split <;> split <;> simp_all <;> omega

private theorem decodeFrom_prefix (bytes : ByteArray) (limit offset remaining : Nat)
    (reversed : List Write) (fits : offset + remaining * frameSize ≤ limit) :
    decodeFrom (bytes.extract 0 limit) offset remaining reversed =
      decodeFrom bytes offset remaining reversed := by
  induction remaining generalizing offset reversed with
  | zero => rfl
  | succ remaining ih =>
    simp only [Nat.succ_mul] at fits
    have frameFits : offset + frameSize ≤ limit := by omega
    rw [decodeFrom, decodeFrom, ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
      Nat.min_eq_left frameFits]
    split
    · rfl
    · exact ih _ _ (by omega)

/-- Trimming a short tail preserves the entire decoder result, including errors
in any complete frame. Replay uses this same decoder before publishing repair. -/
theorem decode_repairPrefix (bytes : ByteArray) :
    decode ((repairPrefix bytes).getD bytes) = decode bytes := by
  let count := bytes.size / frameSize
  let complete := count * frameSize
  change decode ((if complete < bytes.size then some (bytes.extract 0 complete) else none).getD bytes) = _
  split
  · have within : complete ≤ bytes.size := Nat.div_mul_le_self ..
    have size : (bytes.extract 0 complete).size = complete := by simp [Nat.min_eq_left within]
    have frames : (bytes.extract 0 complete).size / frameSize = count := by
      rw [size]
      change count * 48 / 48 = count
      omega
    change decode (bytes.extract 0 complete) = decode bytes
    rw [decode, decode, frames]
    exact decodeFrom_prefix bytes complete 0 count [] (by simp [complete])
  · rfl

end Alvoki.WAL
