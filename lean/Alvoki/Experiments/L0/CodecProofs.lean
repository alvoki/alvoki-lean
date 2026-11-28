import Alvoki.Experiments.L0.Codecs
import Alvoki.Experiments.SSTable.Proofs.Typed
import Alvoki.Codec.ByteWords

namespace ExperimentalL0
open ImmutableSSTable

@[simp] private theorem keyDigits_length (width key : Nat) :
    (keyDigits width key).length = width := by
  induction width generalizing key <;> simp [keyDigits, *]

private theorem highByte_fits (fits : key < 256 ^ (width + 1)) :
    key / 256 ^ width < 256 := by
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
  simpa [Nat.pow_succ, Nat.mul_comm] using fits

private theorem read_keyDigits (width key : Nat) (fits : key < 256 ^ width) :
    readDigits (keyDigits width key) = key := by
  induction width generalizing key with
  | zero =>
    have : key = 0 := by simpa using fits
    simp [keyDigits, readDigits, this]
  | succ width ih =>
    have positive : 0 < 256 ^ width := Nat.pow_pos (by decide)
    have small : key / 256 ^ width < UInt8.size := highByte_fits fits
    simp only [keyDigits, readDigits, keyDigits_length, UInt8.toNat_ofNat_of_lt' small,
      ih _ (Nat.mod_lt _ positive)]
    rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]

theorem keyCodec_roundtrips : keyCodec.Roundtrips := by
  intro key
  have fits : key.toNat < 256 ^ 8 := key.toNat_lt
  have width : (keyCodec.encode key).size = 8 := by
    change (keyDigits 8 key.toNat).toArray.size = 8
    simp
  change (if (keyCodec.encode key).size = 8 then
    .ok (readDigits (keyCodec.encode key).data.toList).toUInt64
    else .error "invalid L0 table key width") = Except.ok key
  rw [ite_eq_left width]
  change Except.ok (readDigits (keyDigits 8 key.toNat).toArray.toList).toUInt64 = _
  simp [read_keyDigits 8 key.toNat fits]

private theorem divMod_order {a b place : Nat} :
    a < b ↔ a / place < b / place ∨ a / place = b / place ∧ a % place < b % place := by
  constructor
  · intro less
    have divOrder := Nat.div_le_div_right (a := a) (b := b) (c := place) (Nat.le_of_lt less)
    rcases Nat.lt_or_eq_of_le divOrder with lessDiv | same
    · exact .inl lessDiv
    · refine .inr ⟨same, ?_⟩
      have combined := Nat.mod_add_div a place
      have other := Nat.mod_add_div b place
      rw [same] at combined
      omega
  · rintro (lessDiv | ⟨same, lessMod⟩)
    · exact Nat.lt_of_div_lt_div lessDiv
    · have combined := Nat.mod_add_div a place
      have other := Nat.mod_add_div b place
      rw [same] at combined
      omega

private theorem keyDigits_order (width a b : Nat) (aFits : a < 256 ^ width)
    (bFits : b < 256 ^ width) :
    keyDigits width a < keyDigits width b ↔ a < b := by
  induction width generalizing a b with
  | zero =>
    have az : a = 0 := by simpa using aFits
    have bz : b = 0 := by simpa using bFits
    simp [az, bz, keyDigits]
  | succ width ih =>
    have positive : 0 < 256 ^ width := Nat.pow_pos (by decide)
    have asmall : a / 256 ^ width < UInt8.size := highByte_fits aFits
    have bsmall : b / 256 ^ width < UInt8.size := highByte_fits bFits
    simp only [keyDigits, List.cons_lt_cons_iff, UInt8.lt_iff_toNat_lt,
      ← UInt8.toNat_inj, UInt8.toNat_ofNat_of_lt' asmall, UInt8.toNat_ofNat_of_lt' bsmall,
      ih _ _ (Nat.mod_lt _ positive) (Nat.mod_lt _ positive)]
    exact divMod_order.symm

theorem keyCodec_preservesOrder : keyCodec.PreservesOrder (· < ·) := by
  intro a b
  change (keyDigits 8 a.toNat).toArray < (keyDigits 8 b.toNat).toArray ↔ a < b
  rw [List.lt_toArray, UInt64.lt_iff_toNat_lt]
  exact keyDigits_order 8 _ _ a.toNat_lt b.toNat_lt

theorem mutationCodec_roundtrips : mutationCodec.Roundtrips := by
  intro mutation
  cases mutation with
  | delete => rfl
  | put value =>
    let tag : ByteArray := ⟨#[1]⟩
    have sameWord : Alvoki.word (Alvoki.pushWordFast tag value) 1 = value :=
      Alvoki.pushWordFast_roundtrip tag value
    have width : (Alvoki.pushWordFast tag value).size = 9 :=
      Alvoki.ByteWords.pushWordFast_size tag value
    have tagUnchanged : (Alvoki.pushWordFast tag value)[0]'(by rw [width]; decide) = 1 := rfl
    change (if (Alvoki.pushWordFast tag value).size = 1 &&
        (Alvoki.pushWordFast tag value)[0]! == 0 then Except.ok Mutation.delete
      else if (Alvoki.pushWordFast tag value).size = 9 &&
        (Alvoki.pushWordFast tag value)[0]! == 1 then
        Except.ok (Mutation.put (Alvoki.word (Alvoki.pushWordFast tag value) 1))
      else Except.error "invalid L0 table mutation") = Except.ok (.put value)
    simp [width, tagUnchanged, sameWord]

theorem encode_rows_ordered {rows : Rows} (ordered : Rows.Ordered rows) :
    ImmutableSSTable.Ordered (rows.map (Entry.encode keyCodec mutationCodec)) := by
  exact List.pairwise_map.mpr (ordered.imp fun h => (keyCodec_preservesOrder _ _).mpr h)

theorem typed_table_from_bytes [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : Rows}
    (bytes : table.Represents (rows.map (Entry.encode keyCodec mutationCodec))) :
    (TypedTable.mk table keyCodec mutationCodec).Represents (· < ·) rows :=
  TypedTable.represents_of_bytes bytes keyCodec_roundtrips mutationCodec_roundtrips
    keyCodec_preservesOrder

theorem typed_lookup_spec [Monad m] [MonadExceptOf String m]
    {table : TypedTable m UInt64 Mutation} {rows : Rows}
    (rep : table.Represents (· < ·) rows) (key : UInt64) :
    table.lookup key = pure (lookupRows rows key) := by
  have predicate : (fun row : Change => row.1 == key) = (fun row => decide (row.1 = key)) := by
    funext row
    apply Bool.eq_iff_iff.mpr
    simp [beq_iff_eq]
  simpa [TypedContents.lookup, lookupRows, predicate] using rep.lookup key

end ExperimentalL0
