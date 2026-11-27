import Alvoki.Experiments.L0.Model
import Alvoki.Codec.ByteWords

namespace ExperimentalL0
open Alvoki Alvoki.ByteWords WalRecoverySlice.Segmented

theorem decode_encode (change : Change) : decode (encode change) = some change := by
  rcases change with ⟨key, mutation⟩
  let keyBytes := pushWordFast ByteArray.empty key
  have keySize : keyBytes.size = 8 := by simp [keyBytes, pushWordFast_size]
  have keyRead : word keyBytes 0 = key := pushWordFast_roundtrip _ _
  cases mutation with
  | delete =>
    change decode keyBytes.data.toList = _
    simp [decode, keySize, keyRead]
  | put value =>
    let bytes := pushWordFast keyBytes value
    have size : bytes.size = 16 := by simp [bytes, pushWordFast_size, keySize]
    have first : word bytes 0 = key :=
      (word_preserved keyBytes value 0 (by simp [keySize])).trans keyRead
    have last : word bytes 8 = value := by
      simpa [keySize] using pushWordFast_roundtrip keyBytes value
    change decode bytes.data.toList = _
    simp [decode, size, first, last]

theorem encode_size (change : Change) : (encode change).length ≤ 32 := by
  rcases change with ⟨key, mutation⟩
  cases mutation <;> simp [encode, pushWordFast_size]

/-- A newest mutation overrides both the old value and an older tombstone. -/
def latest (changes : Rows) (key : UInt64) : Option Mutation :=
  (changes.reverse.find? (fun entry => entry.1 == key)).map Prod.snd

theorem latest_append (xs ys : Rows) (key : UInt64) :
    latest (xs ++ ys) key = (latest ys key).or (latest xs key) := by
  simp only [latest, List.reverse_append, List.find?_append]
  cases ys.reverse.find? (fun entry => entry.1 == key) <;> rfl

private theorem lookup_insert (mem : MemTable) (change : Change) (key : UInt64) :
    (insert mem change)[key]? =
      if key = change.1 then some change.2 else mem[key]? := by
  rw [insert, Std.TreeMap.getElem?_insert]
  simp only [show compare change.1 key = .eq ↔ key = change.1 by
    constructor
    · intro h; exact (Std.LawfulEqOrd.eq_of_compare h).symm
    · intro h; subst key; simp]

theorem replay_lookup (changes : Rows) (key : UInt64) :
    (replay changes)[key]? = latest changes key := by
  have fold (mem : MemTable) (xs : Rows) :
      (xs.foldl insert mem)[key]? = (latest xs key).or mem[key]? := by
    induction xs generalizing mem with
    | nil => rfl
    | cons x xs ih =>
      have newest : latest (x :: xs) key = (latest xs key).or (latest [x] key) :=
        latest_append [x] xs key
      rw [List.foldl_cons, ih, lookup_insert, newest]
      cases hit : latest xs key with
      | some value => rfl
      | none =>
        by_cases same : x.1 = key
        · simp [latest, same]
        · have different := Ne.symm same
          simp [latest, same, different]
  rw [replay, fold]
  cases latest changes key <;> rfl

theorem rows_lookup (mem : MemTable) (key : UInt64) :
    lookupRows mem.toList key = mem[key]? := by
  cases found : mem[key]? with
  | none =>
    have missing : mem.toList.find? (fun entry => entry.1 == key) = none := by
      apply List.find?_eq_none.mpr
      intro entry member
      have hit := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
      by_cases eq : entry.1 = key
      · rw [eq, found] at hit
        contradiction
      · simp [eq]
    simp [lookupRows, missing]
  | some value =>
    have member : (key, value) ∈ mem.toList := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found
    have present : (mem.toList.find? (fun entry => entry.1 == key)).isSome :=
      List.find?_isSome.mpr ⟨(key, value), member, by exact BEq.rfl⟩
    cases hit : mem.toList.find? (fun entry => entry.1 == key) with
    | none => simp [hit] at present
    | some entry =>
      have same : entry.1 = key := by simpa using List.find?_some hit
      have got := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_find?_eq_some hit)
      rw [same, found] at got
      simpa [lookupRows, hit] using got.symm

theorem rows_ordered (mem : MemTable) : Rows.Ordered mem.toList := by
  have order := mem.ordered_keys_toList
  exact order.imp (fun h => compareOfLessAndEq_eq_lt.mp h)

end ExperimentalL0
