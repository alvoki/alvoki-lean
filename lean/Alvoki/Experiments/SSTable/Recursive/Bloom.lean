import Alvoki.Experiments.SSTable.Contract

namespace ImmutableSSTable.Bloom

/-- One independent mask for a bounded key range. The bit layout is
little-endian within each byte. -/
def bytesFor (rows : Nat) : Nat :=
  max 8 ((10 * rows + 7) / 8)

private def hash (key : ByteArray) : UInt64 :=
  key.data.foldl (fun h byte => (h ^^^ byte.toUInt64) * 1099511628211) 14695981039346656037

private def mix (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

def positions (bytes : Nat) (key : ByteArray) : List Nat :=
  let first := mix (hash key)
  let step := mix (first + 0x9e3779b97f4a7c15) ||| 1
  (List.range 7).map fun probe => (first + probe.toUInt64 * step).toNat % (8 * bytes)

def bit (mask : ByteArray) (atBit : Nat) : Bool :=
  mask[atBit / 8]!.toNat.testBit (atBit % 8)

def setBit (mask : ByteArray) (atBit : Nat) : ByteArray :=
  let byte := atBit / 8
  mask.set! byte (mask[byte]! ||| UInt8.ofNat (1 <<< (atBit % 8)))

def insert (mask : ByteArray) (key : ByteArray) : ByteArray :=
  (positions mask.size key).foldl setBit mask

def mayContain (mask : ByteArray) (key : ByteArray) : Bool :=
  (positions mask.size key).all (bit mask)

private def addRow (mask : ByteArray) (row : Entry) : ByteArray :=
  insert mask row.key

def build (rows : Array Entry) : ByteArray :=
  rows.foldl addRow
    ⟨Array.replicate (bytesFor rows.size) 0⟩

@[simp] theorem setBit_size (mask : ByteArray) (p : Nat) : (setBit mask p).size = mask.size := by
  simp [setBit]

private theorem foldBits_size (mask : ByteArray) (probes : List Nat) :
    (probes.foldl setBit mask).size = mask.size := by
  induction probes generalizing mask with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem insert_size (mask : ByteArray) (key : ByteArray) :
    (insert mask key).size = mask.size := foldBits_size _ _

private theorem bit_set_same (mask : ByteArray) (p : Nat) (bound : p < 8 * mask.size) :
    bit (setBit mask p) p = true := by
  have byteInside : p / 8 < mask.size := by omega
  have bitInside : p % 8 < 8 := Nat.mod_lt _ (by decide)
  have fit : 1 <<< (p % 8) < UInt8.size := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) bitInside
  unfold bit setBit
  dsimp only
  rw [ByteArray.getElem!_set!_self _ _ _ byteInside, UInt8.toNat_or, Nat.testBit_or]
  have reduced : (UInt8.ofNat (1 <<< (p % 8))).toNat = 1 <<< (p % 8) :=
    UInt8.toNat_ofNat_of_lt fit
  rw [reduced, Nat.testBit_shiftLeft]
  simp

private theorem bit_set_preserves (mask : ByteArray) (p q : Nat)
    (bound : q < 8 * mask.size) (present : bit mask p = true) :
    bit (setBit mask q) p = true := by
  have byteInside : q / 8 < mask.size := by omega
  unfold bit at present ⊢
  unfold setBit
  dsimp only
  rw [ByteArray.getElem!_set! _ _ _ _ byteInside]
  split
  · rename_i same
    rw [same, UInt8.toNat_or, Nat.testBit_or, present]
    rfl
  · exact present

private theorem foldBits_preserves (mask : ByteArray) (probes : List Nat)
    (bounds : ∀ q ∈ probes, q < 8 * mask.size) (present : bit mask p = true) :
    bit (probes.foldl setBit mask) p = true := by
  induction probes generalizing mask with
  | nil => exact present
  | cons q qs ih =>
    apply ih
    · simpa using fun v member => bounds v (List.mem_cons_of_mem q member)
    · exact bit_set_preserves mask p q (bounds q (by simp)) present

private theorem foldBits_sets (mask : ByteArray) (probes : List Nat)
    (bounds : ∀ q ∈ probes, q < 8 * mask.size) (member : p ∈ probes) :
    bit (probes.foldl setBit mask) p = true := by
  induction probes generalizing mask with
  | nil => simp at member
  | cons q qs ih =>
    have rest : ∀ v ∈ qs, v < 8 * (setBit mask q).size := by
      simpa using fun v member => bounds v (List.mem_cons_of_mem q member)
    rcases List.mem_cons.mp member with rfl | tail
    · change bit (qs.foldl setBit (setBit mask p)) p = true
      exact foldBits_preserves (setBit mask p) qs rest (bit_set_same mask p (bounds p (by simp)))
    · exact ih _ rest tail

private theorem positions_bounded (positive : 0 < bytes) (member : p ∈ positions bytes key) :
    p < 8 * bytes := by
  simp only [positions, List.mem_map] at member
  obtain ⟨i, _, rfl⟩ := member
  exact Nat.mod_lt _ (by omega)

theorem insert_own (mask : ByteArray) (key : ByteArray) (positive : 0 < mask.size) :
    mayContain (insert mask key) key = true := by
  unfold mayContain
  rw [insert_size, List.all_eq_true]
  intro p member
  exact foldBits_sets mask _ (fun _ => positions_bounded positive) member

theorem insert_preserves (mask : ByteArray) (key other : ByteArray)
    (positive : 0 < mask.size) (present : mayContain mask key = true) :
    mayContain (insert mask other) key = true := by
  unfold mayContain at *
  rw [insert_size, List.all_eq_true]
  intro p member
  exact foldBits_preserves mask _ (fun _ => positions_bounded positive)
    (List.all_eq_true.mp present _ member)

private theorem fold_rows_preserves (rows : List Entry) (mask : ByteArray) (key : ByteArray)
    (positive : 0 < mask.size) (present : mayContain mask key = true) :
    mayContain (rows.foldl addRow mask) key = true := by
  induction rows generalizing mask with
  | nil => exact present
  | cons row rest ih =>
    apply ih
    · simpa [addRow] using positive
    · exact insert_preserves mask key row.key positive present

private theorem fold_rows_covers (rows : List Entry) (mask : ByteArray) (row : Entry)
    (positive : 0 < mask.size) (member : row ∈ rows) :
    mayContain (rows.foldl addRow mask) row.key = true := by
  induction rows generalizing mask with
  | nil => simp at member
  | cons current rest ih =>
    simp only [List.foldl_cons]
    have nextPositive : 0 < (addRow mask current).size := by
      simpa [addRow] using positive
    rcases List.mem_cons.mp member with same | later
    · have inserted : mayContain (addRow mask current) row.key = true := by
        rw [same]
        exact insert_own mask current.key positive
      exact fold_rows_preserves rest (addRow mask current) row.key nextPositive inserted
    · exact ih (addRow mask current) nextPositive later

private theorem fold_rows_size (rows : List Entry) (mask : ByteArray) :
    (rows.foldl addRow mask).size = mask.size := by
  induction rows generalizing mask with
  | nil => rfl
  | cons row rest ih => simp [addRow, ih]

theorem build_size (rows : Array Entry) : (build rows).size = bytesFor rows.size := by
  unfold build
  rw [← Array.foldl_toList, fold_rows_size]
  exact Array.size_replicate

/-- The exact packed mask accepts every row passed to its producer. The
value is opaque to both operations. -/
theorem build_covers (rows : Array Entry) (row : Entry) (member : row ∈ rows.toList) :
    mayContain (build rows) row.key = true := by
  unfold build
  rw [← Array.foldl_toList]
  apply fold_rows_covers _ _ _ _ member
  change 0 < (Array.replicate (bytesFor rows.size) (0 : UInt8)).size
  simp only [Array.size_replicate, bytesFor]
  omega

end ImmutableSSTable.Bloom
