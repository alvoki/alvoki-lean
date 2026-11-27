import Alvoki.Experiments.Manifest.Basic
import Alvoki.Codec.ByteWords
import Alvoki.Experiments.DurableBlob.Trace

namespace L0Manifest
open Alvoki Alvoki.ByteWords

private theorem fold_words (words : List UInt64) (prefixBytes : ByteArray) :
    words.foldl pushWordFast prefixBytes = prefixBytes ++ encodeWords words := by
  induction words generalizing prefixBytes with
  | nil => simp [encodeWords]
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, encodeWords]
    rw [pushWordFast_append, ByteArray.append_assoc]

theorem decode_encode (valid : v.Valid) : decode (encode v) = some v := by
  let checksum := checksumWords (payload v)
  let words := payload v ++ [checksum]
  have encoded : encode v = encodeWords words := by
    change pushWordFast ((payload v).foldl pushWordFast ByteArray.empty) checksum = _
    change [checksum].foldl pushWordFast ((payload v).foldl pushWordFast ByteArray.empty) = _
    rw [← List.foldl_append]
    simp only [words, fold_words, ByteArray.empty_append]
  rw [encoded]
  have width : (encodeWords words).size = 8 * (v.tables.length + 3) := by
    simp [words, payload]
  have tag := word_encodeWords words 0 (by simp [words, payload])
  have position := word_encodeWords words 1 (by simp [words, payload])
  change word _ 0 = magic at tag
  change word _ 8 = v.flushedThrough at position
  have trailer : word (encodeWords words) (8 * (v.tables.length + 3) - 8) = checksum := by
    rw [show 8 * (v.tables.length + 3) - 8 = 8 * (v.tables.length + 2) by omega]
    rw [word_encodeWords _ _ (by simp [words, payload])]
    simp [words, payload]
  have tables : (List.range v.tables.length).map
      (fun i => word (encodeWords words) (8 * (i + 2))) = v.tables := by
    apply List.ext_getElem
    · simp
    · intro i left right
      simp only [List.getElem_map, List.getElem_range]
      have within : i < v.tables.length := right
      rw [word_encodeWords _ (i + 2) (by simp [words, payload]; omega)]
      simp [words, payload, List.getElem_append_left within]
  have readBack : readVersion (encodeWords words) = v := by
    cases v
    simp_all [readVersion]
  simp [decode, width, tag, trailer, checksum, readBack, valid]
  omega

/-- A mismatch between the stored checksum and the checksum of the decoded
payload is rejected, including when the extent or tag is invalid. -/
theorem decode_rejects_checksum
    (mismatch : word bytes (bytes.size - 8) ≠ checksumWords (payload (readVersion bytes))) :
    decode bytes = none := by
  simp [decode, mismatch]

/-- The typed publication path delegates exactly one encoded replacement. -/
theorem publish_valid [Monad m] [MonadExceptOf error m] (makeError : String → error)
    (blob : DurableBlob.Backend m ByteArray) (valid : v.Valid) :
    (backend makeError blob).publish v = blob.publish (encode v) := by
  simp [backend, valid]

/-- The typed recovery path decodes the bytes returned by the backend's
successful reopen, which has already durably settled its selection. -/
theorem reopen_encoded [Monad m] [LawfulMonad m] [MonadExceptOf error m]
    (makeError : String → error) (blob : DurableBlob.Backend m ByteArray)
    (valid : v.Valid) (opened : blob.reopen = pure (encode v)) :
    (backend makeError blob).reopen = pure v := by
  simp [backend, opened, decode_encode valid]

/-- Complete manifest sessions obey the same client contract over Version.
The backend supplies only its byte trace. The adapter submits encodings of
valid proposals, and the contract supplies all selected reopen values. Every
related observed payload decodes to exactly the typed value. -/
theorem trace_refines
    (trace : DurableBlob.Allows (encode Version.empty) events state)
    (submitted : ∀ event ∈ events,
      event.Submitted (fun bytes => ∃ v, Version.Valid v ∧ encode v = bytes)) :
    ∃ observed next, DurableBlob.Allows Version.empty observed next ∧
      observed.map (DurableBlob.Event.map encode) = events ∧ next.map encode = state ∧
      (∀ event ∈ observed, event.Values (fun v => decode (encode v) = some v)) := by
  obtain ⟨observed, next, allowed, related, finalState, valid, _⟩ :=
    trace.lift encode Version.Valid Version.empty (by simp [Version.Valid, Version.empty]) submitted
  refine ⟨observed, next, allowed, related, finalState, ?_⟩
  intro event member
  have accepted := valid event member
  cases event <;> first | exact trivial | exact decode_encode accepted

end L0Manifest
