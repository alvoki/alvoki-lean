import Alvoki.Experiments.Manifest.Basic
import Alvoki.Codec.ByteWords

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
  have encoded : encode v = encodeWords (magic :: v.flushedThrough :: v.tables) := by
    unfold encode
    rw [fold_words, ByteArray.empty_append]
  rw [encoded]
  have width : (encodeWords (magic :: v.flushedThrough :: v.tables)).size =
      8 * (v.tables.length + 2) := by simp
  have tag := word_encodeWords (magic :: v.flushedThrough :: v.tables) 0 (by simp)
  have position := word_encodeWords (magic :: v.flushedThrough :: v.tables) 1 (by simp)
  change word _ 0 = magic at tag
  change word _ 8 = v.flushedThrough at position
  have tables : (List.range v.tables.length).map
      (fun i => word (encodeWords (magic :: v.flushedThrough :: v.tables)) (8 * (i + 2))) =
      v.tables := by
    apply List.ext_getElem
    · simp
    · intro i left right
      simp only [List.getElem_map, List.getElem_range]
      rw [word_encodeWords _ (i + 2) (by simp; omega)]
      rfl
  simp [decode, width, tag, position, tables, valid]
  omega

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

/-- A replacing backend can select either candidate after an uncertain
publication. Decoding preserves both candidates, including their exact WAL
positions and table order. -/
theorem recover_version (knownValid : known.Valid)
    (pendingValid : ∀ v ∈ pending, Version.Valid v)
    (chosen : DurableBlob.Permitted (encode known) (pending.map encode) bytes) :
    ∃ v, decode bytes = some v ∧ DurableBlob.Permitted known pending v := by
  rcases chosen with rfl | pendingBytes
  · exact ⟨known, decode_encode knownValid, Or.inl rfl⟩
  · cases pending with
    | none => simp at pendingBytes
    | some v =>
      simp only [Option.map_some, Option.some.injEq] at pendingBytes
      subst bytes
      exact ⟨v, decode_encode (pendingValid v (by simp)), Or.inr rfl⟩

end L0Manifest
