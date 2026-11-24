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

@[inline] private def advanceOrdinal (checkOrdinals : Bool) (ordinal count : Nat) : Nat :=
  if checkOrdinals then ordinal + count else ordinal

/-- A complete frame with a bad checksum, format, tag, or required ordinal
fails recovery. A final incomplete frame is outside the complete frame count. -/
@[specialize checkOrdinals]
private def decodeFrom (checkOrdinals : Bool) (bytes : @& ByteArray) (ordinal offset remaining : Nat)
    (reversed : List Write) : Except String (List Write) :=
  match remaining with
  | 0 => .ok reversed.reverse
  | n + 1 =>
    match decodeFrame (bytes.extract offset (offset + frameSize)) with
    | .error message => .error message
    | .ok event =>
      if checkOrdinals && event.sequence.toNat != ordinal then
        .error "WAL frame sequence does not match its ordinal"
      else
        decodeFrom checkOrdinals bytes (advanceOrdinal checkOrdinals ordinal 1)
          (offset + frameSize) n (event :: reversed)

def decode (bytes : @& ByteArray) : Except String (List Write) :=
  decodeFrom false bytes 1 0 (bytes.size / frameSize) []

/-- Decode a whole WAL prefix, checking the frame sequence against its
one-based position during the same pass. -/
def decodeOrdinals (bytes : @& ByteArray) : Except String (List Write) :=
  decodeFrom true bytes 1 0 (bytes.size / frameSize) []

/-- A contiguous sequence of frame ordinals beginning at `first`. -/
def OrdinalsFrom : Nat → List Write → Prop
  | _, [] => True
  | first, event :: rest => event.sequence.toNat = first ∧ OrdinalsFrom (first + 1) rest

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

private theorem decodeFrom_shift (checkOrdinals : Bool) (prefixBytes bytes : ByteArray)
    (ordinal offset remaining : Nat)
    (reversed : List Write) :
    decodeFrom checkOrdinals (prefixBytes ++ bytes) ordinal (prefixBytes.size + offset) remaining reversed =
      decodeFrom checkOrdinals bytes ordinal offset remaining reversed := by
  induction remaining generalizing ordinal offset reversed with
  | zero => rfl
  | succ n ih =>
    rw [decodeFrom, decodeFrom, Nat.add_assoc, ByteArray.extract_append_size_add]
    split
    · rfl
    · split
      · rfl
      · exact ih (advanceOrdinal checkOrdinals ordinal 1) (offset + frameSize) _

private theorem decodeFrom_append_encoded (checkOrdinals : Bool) (events : List Write)
    (tail : ByteArray) (ordinal remaining : Nat) (reversed : List Write)
    (ordered : checkOrdinals = true → OrdinalsFrom ordinal events) :
    decodeFrom checkOrdinals (encode events ++ tail) ordinal 0 (events.length + remaining) reversed =
      decodeFrom checkOrdinals tail (advanceOrdinal checkOrdinals ordinal events.length)
        0 remaining (events.reverse ++ reversed) := by
  induction events generalizing ordinal reversed with
  | nil => simp [encode, advanceOrdinal]
  | cons event rest ih =>
    simp only [encode, ByteArray.append_assoc, List.length_cons,
      Nat.add_right_comm rest.length 1 remaining, decodeFrom, Nat.zero_add]
    rw [ByteArray.extract_append_eq_left (encodeFrame_size event).symm, decodeFrame_encode]
    have accepted : (checkOrdinals && event.sequence.toNat != ordinal) = false := by
      cases checkOrdinals with
      | false => rfl
      | true => simp [(ordered rfl).1]
    simp only [accepted, Bool.false_eq_true, ↓reduceIte]
    let next := advanceOrdinal checkOrdinals ordinal 1
    have shifted := decodeFrom_shift checkOrdinals (encodeFrame event) (encode rest ++ tail) next 0
      (rest.length + remaining) (event :: reversed)
    simp only [encodeFrame_size, Nat.add_zero] at shifted
    have remainingOrdered (enabled : checkOrdinals = true) : OrdinalsFrom next rest := by
      simpa [next, advanceOrdinal, enabled] using (ordered enabled).2
    rw [shifted, ih next _ remainingOrdered]
    cases checkOrdinals <;> simp [next, advanceOrdinal, List.reverse_cons,
      List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem decode_ignores_incomplete_tail (events : List Write) (tail : ByteArray)
    (incomplete : tail.size < frameSize) :
    decode (encode events ++ tail) = .ok events := by
  have count : (encode events ++ tail).size / frameSize = events.length := by
    rw [ByteArray.size_append, encode_size]
    change (48 * events.length + tail.size) / 48 = events.length
    change tail.size < 48 at incomplete
    omega
  have parsed := decodeFrom_append_encoded false events tail 1 0 [] (by simp)
  rw [decode, count]
  simpa [decodeFrom] using parsed

theorem decode_encode (events : List Write) : decode (encode events) = .ok events := by
  have h := decode_ignores_incomplete_tail events ByteArray.empty (by decide)
  simpa only [ByteArray.append_empty] using h

theorem decodeOrdinals_encode (events : List Write) (ordered : OrdinalsFrom 1 events) :
    decodeOrdinals (encode events) = .ok events := by
  have count : (encode events).size / frameSize = events.length := by
    rw [encode_size, Nat.mul_div_cancel_left _ (by decide : 0 < frameSize)]
  have parsed := decodeFrom_append_encoded true events ByteArray.empty 1 0 [] (fun _ => ordered)
  rw [decodeOrdinals, count]
  simpa [decodeFrom] using parsed

private theorem decodeFrom_ordinals (bytes : ByteArray) (ordinal offset remaining : Nat)
    (reversed result : List Write) (decoded : decodeFrom true bytes ordinal offset remaining reversed = .ok result) :
    ∃ suffix, OrdinalsFrom ordinal suffix ∧ result = reversed.reverse ++ suffix := by
  induction remaining generalizing ordinal offset reversed with
  | zero =>
    cases decoded
    exact ⟨[], trivial, by simp⟩
  | succ remaining ih =>
    rw [decodeFrom] at decoded
    split at decoded
    · contradiction
    · rename_i event _
      split at decoded
      · contradiction
      · rename_i sequence
        have number : event.sequence.toNat = ordinal := by simpa using sequence
        obtain ⟨suffix, ordered, combined⟩ := ih (ordinal + 1) (offset + frameSize) (event :: reversed) decoded
        exact ⟨event :: suffix, ⟨number, ordered⟩, by simpa [List.reverse_cons, List.append_assoc] using combined⟩

/-- Every complete frame returned by the selected-WAL decoder has the
sequence assigned to its one-based position. -/
theorem decodeOrdinals_sound {bytes : ByteArray} {events : List Write}
    (decoded : decodeOrdinals bytes = .ok events) : OrdinalsFrom 1 events := by
  obtain ⟨suffix, ordered, reconstructed⟩ := decodeFrom_ordinals bytes 1 0 (bytes.size / frameSize) [] events decoded
  simpa using reconstructed.symm ▸ ordered

private theorem decodeFrom_reencode (bytes : ByteArray) (ordinal offset remaining : Nat)
    (reversed result : List Write)
    (decoded : decodeFrom true bytes ordinal offset remaining reversed = .ok result) :
    ∃ suffix, result = reversed.reverse ++ suffix ∧
      encode suffix = bytes.extract offset (offset + remaining * frameSize) := by
  induction remaining generalizing ordinal offset reversed with
  | zero =>
    cases decoded
    exact ⟨[], by simp, by simp [encode]⟩
  | succ remaining ih =>
    rw [decodeFrom] at decoded
    split at decoded
    · contradiction
    · rename_i event frame
      split at decoded
      · contradiction
      · obtain ⟨suffix, reconstructed, encoded⟩ :=
          ih (advanceOrdinal true ordinal 1) (offset + frameSize) (event :: reversed) decoded
        refine ⟨event :: suffix, by simpa [List.reverse_cons, List.append_assoc] using reconstructed, ?_⟩
        rw [encode, decodeFrame_reencode frame, encoded]
        exact (ByteArray.extract_eq_extract_append_extract (offset + frameSize)
          (by omega) (by omega)).symm.trans
          (congrArg (bytes.extract offset) (by rw [Nat.succ_mul]; omega))

/-- The checked decoder identifies the exact bytes of every complete frame.
Any short tail is outside the reproduced prefix. -/
theorem decodeOrdinals_reencode {bytes : ByteArray} {events : List Write}
    (decoded : decodeOrdinals bytes = .ok events) :
    encode events = bytes.extract 0 (bytes.size / frameSize * frameSize) := by
  obtain ⟨suffix, result, encoded⟩ := decodeFrom_reencode bytes 1 0 (bytes.size / frameSize) [] events decoded
  simp only [List.reverse_nil, List.nil_append] at result
  simpa only [result, Nat.zero_add] using encoded

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
  rw [decode, count, decodeFrom_append_encoded false events last 1 1 [] (by simp)]
  simp [decodeFrom, entire, bad]

/-- After replay validates the complete frames, return replacement bytes only for a short tail. -/
def repairPrefix (bytes : ByteArray) : Option ByteArray :=
  let complete := bytes.size / frameSize * frameSize
  if complete < bytes.size then some (bytes.extract 0 complete) else none

theorem repairPrefix_getD_eq_extract (bytes : ByteArray) :
    (repairPrefix bytes).getD bytes = bytes.extract 0 (bytes.size / frameSize * frameSize) := by
  unfold repairPrefix
  dsimp only
  split
  · rfl
  · have size : bytes.size / frameSize * frameSize = bytes.size :=
      Nat.le_antisymm (Nat.div_mul_le_self ..) (by omega)
    rw [size, ByteArray.extract_zero_size]
    rfl

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

private theorem decodeFrom_prefix (checkOrdinals : Bool) (bytes : ByteArray) (limit ordinal offset remaining : Nat)
    (reversed : List Write) (fits : offset + remaining * frameSize ≤ limit) :
    decodeFrom checkOrdinals (bytes.extract 0 limit) ordinal offset remaining reversed =
      decodeFrom checkOrdinals bytes ordinal offset remaining reversed := by
  induction remaining generalizing ordinal offset reversed with
  | zero => rfl
  | succ remaining ih =>
    simp only [Nat.succ_mul] at fits
    have frameFits : offset + frameSize ≤ limit := by omega
    rw [decodeFrom, decodeFrom, ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
      Nat.min_eq_left frameFits]
    split
    · rfl
    · split
      · rfl
      · exact ih _ _ _ (by omega)

private theorem decodeFrom_repairPrefix (checkOrdinals : Bool) (bytes : ByteArray) :
    let selected := (repairPrefix bytes).getD bytes
    decodeFrom checkOrdinals selected 1 0 (selected.size / frameSize) [] =
      decodeFrom checkOrdinals bytes 1 0 (bytes.size / frameSize) [] := by
  simp only [repairPrefix_getD_eq_extract, ByteArray.size_extract,
    Nat.min_eq_left (Nat.div_mul_le_self bytes.size frameSize), Nat.sub_zero]
  rw [Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  exact decodeFrom_prefix checkOrdinals bytes _ 1 0 _ [] (by simp)

/-- Trimming a short tail preserves the entire decoder result, including errors
in any complete frame. Replay uses this same decoder before publishing repair. -/
theorem decode_repairPrefix (bytes : ByteArray) :
    decode ((repairPrefix bytes).getD bytes) = decode bytes :=
  decodeFrom_repairPrefix false bytes

/-- Short-tail repair also preserves ordinal checks used by legacy open. -/
theorem decodeOrdinals_repairPrefix (bytes : ByteArray) :
    decodeOrdinals ((repairPrefix bytes).getD bytes) = decodeOrdinals bytes :=
  decodeFrom_repairPrefix true bytes

end Alvoki.WAL
