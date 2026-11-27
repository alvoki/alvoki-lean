import Alvoki.Kernel.BlockContracts

namespace Alvoki.ByteWords

theorem pushWordFast_size (bytes : ByteArray) (word : UInt64) :
    (pushWordFast bytes word).size = bytes.size + 8 := by
  simp only [pushWordFast, ByteArray.size_push]

theorem pushWordFast_append (bytes : ByteArray) (word : UInt64) :
    pushWordFast bytes word = bytes ++ pushWordFast ByteArray.empty word := by
  ext1
  simp only [pushWordFast, ByteArray.data_push, ByteArray.data_append, Array.append_push,
    ByteArray.data_empty, Array.append_empty]

theorem word_left (a b : ByteArray) (offset : Nat) (fits : offset + 7 < a.size) :
    word (a ++ b) offset = word a offset := by
  have lane (i : Nat) (small : i ≤ 7) : (a ++ b).get! (offset + i) = a.get! (offset + i) := by
    have h : offset + i < a.size := by omega
    have hab : offset + i < (a ++ b).size := by rw [ByteArray.size_append]; omega
    simp only [getBang_eq_index]
    rw [getElem!_pos (a ++ b) (offset + i) hab, getElem!_pos a (offset + i) h, ByteArray.getElem_append_left h]
  simp only [word, joinBytes, lane 0 (by decide), lane 1 (by decide), lane 2 (by decide),
    lane 3 (by decide), lane 4 (by decide), lane 5 (by decide), lane 6 (by decide), lane 7 (by decide)]

theorem word_right (a b : ByteArray) (offset : Nat) (fits : offset + 7 < b.size) :
    word (a ++ b) (a.size + offset) = word b offset := by
  have lane (i : Nat) (small : i ≤ 7) :
      (a ++ b).get! (a.size + offset + i) = b.get! (offset + i) := by
    have h : offset + i < b.size := by omega
    have hab : a.size + offset + i < (a ++ b).size := by rw [ByteArray.size_append]; omega
    simp only [getBang_eq_index]
    rw [getElem!_pos (a ++ b) (a.size + offset + i) hab, getElem!_pos b (offset + i) h,
      ByteArray.getElem_append_right (by omega)]
    congr 1
    omega
  simp only [word, joinBytes, lane 0 (by decide), lane 1 (by decide), lane 2 (by decide),
    lane 3 (by decide), lane 4 (by decide), lane 5 (by decide), lane 6 (by decide), lane 7 (by decide)]

theorem word_preserved (prefixBytes : ByteArray) (value : UInt64) (offset : Nat)
    (fits : offset + 7 < prefixBytes.size) :
    word (pushWordFast prefixBytes value) offset = word prefixBytes offset := by
  rw [pushWordFast_append]
  exact word_left _ _ _ fits

/-- Equal aligned eight-byte words and equal length determine the entire array. -/
theorem eq_of_aligned_words {a b : ByteArray} (outputSize : a.size = b.size)
    (aligned : ∀ k : Nat, 8 * k < b.size → word a (8 * k) = word b (8 * k)) : a = b := by
  ext1
  apply Array.ext
  · exact outputSize
  · intro j hOut hSrc
    let k := j / 8
    let lane := j % 8
    have within : lane < 8 := Nat.mod_lt _ (by decide)
    have position : 8 * k + lane = j := Nat.div_add_mod j 8
    have wordEq := aligned k (by change j < b.size at hSrc; omega)
    have first := splitByte_joinBytes (fun i => a.get! (8 * k + i)) lane within
    have second := splitByte_joinBytes (fun i => b.get! (8 * k + i)) lane within
    change splitByte (word a (8 * k)) lane = _ at first
    change splitByte (word b (8 * k)) lane = _ at second
    rw [wordEq] at first
    have eq := first.symm.trans second
    rw [position, getBang_eq_index, getBang_eq_index,
      getElem!_pos a j hOut, getElem!_pos b j hSrc] at eq
    exact eq

theorem word_extract (bytes : ByteArray) (start stop offset : Nat)
    (inSlice : start + offset + 7 < stop) (inBytes : stop ≤ bytes.size) :
    word (bytes.extract start stop) offset = word bytes (start + offset) := by
  have lane (i : Nat) (small : i ≤ 7) :
      (bytes.extract start stop).get! (offset + i) = bytes.get! (start + offset + i) := by
    have a : offset + i < (bytes.extract start stop).size := by
      simp only [ByteArray.size_extract, Nat.min_eq_left inBytes]
      omega
    have b : start + offset + i < bytes.size := by omega
    simp only [getBang_eq_index]
    rw [getElem!_pos (bytes.extract start stop) (offset + i) a,
      getElem!_pos bytes (start + offset + i) b, ByteArray.getElem_extract]
    exact getElem_congr_idx (by omega)
  simp only [word, joinBytes, lane 0 (by decide), lane 1 (by decide), lane 2 (by decide),
    lane 3 (by decide), lane 4 (by decide), lane 5 (by decide), lane 6 (by decide),
    lane 7 (by decide)]

/-- Encode consecutive unsigned little-endian words. -/
def encodeWords : List UInt64 → ByteArray
  | [] => ByteArray.empty
  | word :: rest => pushWordFast ByteArray.empty word ++ encodeWords rest

@[simp] theorem encodeWords_size (words : List UInt64) :
    (encodeWords words).size = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons head rest ih =>
    simp only [encodeWords, ByteArray.size_append, pushWordFast_size, ByteArray.size_empty,
      ih, List.length_cons]
    omega

theorem word_encodeWords (words : List UInt64) (i : Nat) (within : i < words.length) :
    word (encodeWords words) (8 * i) = words[i] := by
  induction words generalizing i with
  | nil => simp at within
  | cons head rest ih =>
    let prefixBytes := pushWordFast ByteArray.empty head
    have size : prefixBytes.size = 8 := pushWordFast_size _ _
    cases i with
    | zero =>
      change word (prefixBytes ++ encodeWords rest) 0 = head
      rw [word_left _ _ _ (by rw [size]; decide)]
      exact pushWordFast_roundtrip _ _
    | succ i =>
      change word (prefixBytes ++ encodeWords rest) (8 * (i + 1)) = rest[i]'(by simpa using within)
      have hit : i < rest.length := by simpa using within
      have position : 8 * (i + 1) = prefixBytes.size + 8 * i := by omega
      rw [position, word_right _ _ _ (by simp; omega)]
      exact ih i hit

theorem encodeSixWords (bytes : ByteArray) (size : bytes.size = 48) :
    encodeWords [word bytes 0, word bytes 8, word bytes 16, word bytes 24, word bytes 32,
      word bytes 40] = bytes := by
  apply eq_of_aligned_words (by simp [size])
  intro k bound
  have lane : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases lane with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [word_encodeWords] <;> first | rfl | simp

/-- FNV-1a over the little-endian encoding of consecutive words. -/
def checksumWords (words : List UInt64) : UInt64 :=
  words.foldl (fun hash field =>
    (List.range 8).foldl (fun state lane =>
      (state ^^^ (splitByte field lane).toUInt64) * 1099511628211) hash) 14695981039346656037

end Alvoki.ByteWords
