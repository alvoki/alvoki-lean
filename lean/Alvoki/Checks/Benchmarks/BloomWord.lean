import Alvoki.Experiments.SSTable.Recursive.Bloom

namespace ImmutableSSTable.BloomPlacement

private def fnv (acc : UInt64) (byte : UInt8) : UInt64 :=
  (acc ^^^ byte.toUInt64) * 1099511628211

def copiedHash (bytes : ByteArray) : UInt64 :=
  bytes.data.foldl fnv 14695981039346656037

private def mix (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

def wordPositions (hash : ByteArray → UInt64) (bytes : Nat) (key : ByteArray) :
    List Nat :=
  let first := mix (hash key)
  let step := mix (first + 0x9e3779b97f4a7c15) ||| 1
  let modulus := (8 * bytes).toUInt64
  (List.range 7).map fun probe => ((first + probe.toUInt64 * step) % modulus).toNat

def packedHash (bytes : ByteArray) : UInt64 :=
  bytes.foldl fnv 14695981039346656037

private theorem copiedHash_eq (bytes : ByteArray) : copiedHash bytes = packedHash bytes := by
  cases bytes with
  | mk data =>
    let step : UInt64 → UInt8 → Id UInt64 := fun acc byte => pure (fnv acc byte)
    have loop (fuel idx : Nat) (acc : UInt64) :
        Array.foldlM.loop step data data.size (Nat.le_refl _) fuel idx acc =
          ByteArray.foldlM.loop step ⟨data⟩ data.size (Nat.le_refl _) fuel idx acc := by
      induction fuel generalizing idx acc with
      | zero =>
        simp [Array.foldlM.loop, ByteArray.foldlM.loop]
      | succ fuel ih =>
        by_cases inside : idx < data.size
        · rw [Array.foldlM.loop, ByteArray.foldlM.loop]
          simp only [inside, ↓reduceDIte]
          exact ih (idx + 1) (fnv acc data[idx])
        · rw [Array.foldlM.loop, ByteArray.foldlM.loop]
          simp only [inside, ↓reduceDIte]
    simp only [copiedHash, packedHash, Array.foldl, ByteArray.foldl, Array.foldlM,
      ByteArray.foldlM, ByteArray.size, Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
    exact loop data.size 0 _

private theorem wordPositions_eq (bytes : Nat) (key : ByteArray) (fit : 8 * bytes < UInt64.size) :
    wordPositions copiedHash bytes key = Bloom.positions bytes key := by
  unfold wordPositions Bloom.positions
  apply List.map_congr_left
  intro probe _
  rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' fit]
  rfl

def blank (bytes : Nat) : ByteArray :=
  ⟨Array.replicate bytes 0⟩

private def packedWordInsert (mask : ByteArray) (key : ByteArray) : ByteArray :=
  let first := mix (packedHash key)
  let step := mix (first + 0x9e3779b97f4a7c15) ||| 1
  let modulus := (8 * mask.size).toUInt64
  (List.range 7).foldl (fun mask probe =>
    Bloom.setBit mask ((first + probe.toUInt64 * step) % modulus).toNat) mask

private theorem packedWordInsert_eq (mask : ByteArray) (key : ByteArray)
    (fit : 8 * mask.size < UInt64.size) : packedWordInsert mask key = Bloom.insert mask key := by
  unfold Bloom.insert
  rw [← wordPositions_eq _ _ fit]
  rw [wordPositions, copiedHash_eq, List.foldl_map]
  rfl

def packedWordBuild (rows : Array Entry) : ByteArray :=
  rows.foldl (fun mask row => packedWordInsert mask row.key) (blank (Bloom.bytesFor rows.size))

/-- The packed byte fold and word-sized residue produce the current wire mask
when the modulus fits in UInt64. The insertion fold computes one position
at a time. -/
theorem packedWordBuild_eq (rows : Array Entry) (fit : 8 * Bloom.bytesFor rows.size < UInt64.size) :
    packedWordBuild rows = Bloom.build rows := by
  have fold (input : List Entry) (mask : ByteArray) (fits : 8 * mask.size < UInt64.size) :
      input.foldl (fun mask row => packedWordInsert mask row.key) mask =
        input.foldl (fun mask row => Bloom.insert mask row.key) mask := by
    induction input generalizing mask with
    | nil => simp only [List.foldl_nil]
    | cons row more ih =>
      simp only [List.foldl_cons]
      rw [packedWordInsert_eq _ row.key fits]
      exact ih (Bloom.insert mask row.key) (by simpa using fits)
  unfold packedWordBuild Bloom.build
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have fits : 8 * (blank (Bloom.bytesFor rows.size)).size < UInt64.size := by
    simpa [blank, ByteArray.size] using fit
  exact fold rows.toList (blank (Bloom.bytesFor rows.size)) fits

theorem packedWordBuild_covers (rows : Array Entry)
    (fit : 8 * Bloom.bytesFor rows.size < UInt64.size) (row : Entry)
    (member : row ∈ rows.toList) : Bloom.mayContain (packedWordBuild rows) row.key = true := by
  rw [packedWordBuild_eq rows fit]
  exact Bloom.build_covers rows row member

end ImmutableSSTable.BloomPlacement
