import Alvoki.Experiments.SSTable.Representation

namespace ImmutableSSTable

/-- Bytes emitted by a caller's codec decode to their original value. -/
def Codec.Roundtrips (codec : Codec α) : Prop :=
  ∀ value, codec.decode (codec.encode value) = .ok value

/-- Lexicographic bytes implement the caller's strict key order. -/
def Codec.PreservesOrder (codec : Codec κ) (less : κ → κ → Prop) : Prop :=
  ∀ a b, codec.encode a < codec.encode b ↔ less a b

private theorem Codec.encode_eq_iff (codec : Codec α) (law : codec.Roundtrips) (a b : α) :
    codec.encode a = codec.encode b ↔ a = b := by
  constructor
  · intro h
    have same := congrArg codec.decode h
    rw [law a, law b, Except.ok.injEq] at same
    exact same
  · exact congrArg codec.encode

namespace TypedContents

def lookup [DecidableEq κ] (rows : List (κ × ν)) (key : κ) : Option ν :=
  (rows.find? fun row => decide (row.1 = key)).map Prod.snd

def next (rows : List (κ × ν)) (i : Nat) : Option ((κ × ν) × Nat) :=
  if h : i < rows.length then some (rows[i], i + 1) else none

/-- At a lower-bound cursor, earlier keys are strictly smaller and the
remaining keys are at least the query in the caller's order. -/
def IsSeek (less : κ → κ → Prop) (rows : List (κ × ν)) (key : κ) (i : Nat) : Prop :=
  i ≤ rows.length ∧
    (∀ j (h : j < rows.length), j < i → less rows[j].1 key) ∧
    (∀ j (h : j < rows.length), i ≤ j → ¬ less rows[j].1 key)

end TypedContents

/-- The healthy observations of an opened typed table, in caller values. -/
structure TypedTable.Represents [Monad m] [MonadExceptOf String m] [DecidableEq κ]
    (table : TypedTable m κ ν) (less : κ → κ → Prop) (rows : List (κ × ν)) : Prop where
  ordered : rows.Pairwise (fun a b => less a.1 b.1)
  rowCount : table.table.rowCount = rows.length
  lookup : ∀ key, table.lookup key = pure (TypedContents.lookup rows key)
  seek : ∀ key, ∃ i, table.seek key = pure i ∧ TypedContents.IsSeek less rows key i
  next : ∀ i, table.next i = pure (TypedContents.next rows i)

private theorem lookup_encode [DecidableEq κ] (keyCodec : Codec κ) (valueCodec : Codec ν)
    (keyLaw : keyCodec.Roundtrips) (rows : List (κ × ν)) (key : κ) :
    Contents.lookup (rows.map (Entry.encode keyCodec valueCodec)) (keyCodec.encode key) =
      (TypedContents.lookup rows key).map valueCodec.encode := by
  have sameKey (row : κ × ν) :
      (keyCodec.encode row.1 == keyCodec.encode key) =
        decide (row.1 = key) := by
    apply Bool.eq_iff_iff.mpr
    simp [keyCodec.encode_eq_iff keyLaw]
  simp [Contents.lookup, TypedContents.lookup, Function.comp_def, Entry.encode, sameKey,
    Option.map_map]

/-- The actual typed operations refine lookup, lower-bound seek and iteration
over the caller's values when the byte table represents their encodings. -/
theorem TypedTable.represents_of_bytes [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    [DecidableEq κ] {table : TypedTable m κ ν} {rows : List (κ × ν)} {less : κ → κ → Prop}
    (bytes : table.table.Represents (rows.map (Entry.encode table.keyCodec table.valueCodec)))
    (keyLaw : table.keyCodec.Roundtrips) (valueLaw : table.valueCodec.Roundtrips)
    (orderLaw : table.keyCodec.PreservesOrder less) :
    table.Represents less rows := by
  unfold Codec.Roundtrips at keyLaw valueLaw
  refine ⟨?_, by simpa using bytes.rowCount, ?_, ?_, ?_⟩
  · refine (List.pairwise_map.mp bytes.ordered).imp ?_
    intro a b related
    exact (orderLaw a.1 b.1).mp related
  · intro key
    unfold TypedTable.lookup
    rw [bytes.lookup, lookup_encode _ _ keyLaw, pure_bind]
    cases TypedContents.lookup rows key <;> simp [liftDecode, valueLaw]
  · intro key
    obtain ⟨i, observed, bound, left, right⟩ := bytes.seek (table.keyCodec.encode key)
    refine ⟨i, observed, by simpa using bound, ?_, ?_⟩
    · intro j within earlier
      have test := left j earlier
      exact (orderLaw rows[j].1 key).mp (by
        simpa [Entry.encode, List.getElem?_eq_getElem within] using test)
    · intro j within later lessKey
      have inBytes : j < (rows.map (Entry.encode table.keyCodec table.valueCodec)).length := by
        simpa using within
      have test := right j later inBytes
      have lessBytes := (orderLaw rows[j].1 key).mpr lessKey
      exact Std.not_lt.mpr (by
        simpa [Entry.encode, List.getElem?_eq_getElem within] using test) lessBytes
  · intro i
    unfold TypedTable.next TypedContents.next
    rw [bytes.next, pure_bind]
    by_cases within : i < rows.length
    · simp [Contents.next, within, Entry.encode, liftDecode, keyLaw, valueLaw]
    · simp [Contents.next, within]

end ImmutableSSTable
