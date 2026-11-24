import Alvoki.Storage.Disk.RetainedWalReplay

namespace Alvoki.Storage
open WAL (frameSize)

private def checkWalSegmentSizes (through : Nat) : List (Nat × ByteArray) → Bool
  | [] => false
  | [(first, bytes)] => decide ((through - first) * frameSize ≤ bytes.size)
  | (first, bytes) :: (next, rest) :: remaining =>
    decide (first < next ∧ bytes.size = (next - first) * frameSize) &&
      checkWalSegmentSizes through ((next, rest) :: remaining)

/-- Check physical file boundaries separately from aggregate WAL decoding.
The first selected start is at or before the marker, and each sealed file
fills its claimed range exactly. If newer files follow the marker, the
original final file supplies zero required bytes and repair chooses an
earlier keeper. -/
def checkWalSegmentSpans (through : Nat) (files : List (Nat × ByteArray)) : Bool :=
  (files.head?.any fun file => decide (file.1 ≤ through)) && checkWalSegmentSizes through files

inductive WalSegmentSpans (through : Nat) : List (Nat × ByteArray) → Prop where
  | active (covered : (through - first) * frameSize ≤ bytes.size) : WalSegmentSpans through [(first, bytes)]
  | sealed (forward : first < next) (size : bytes.size = (next - first) * frameSize)
      (rest : WalSegmentSpans through ((next, nextBytes) :: remaining)) :
      WalSegmentSpans through ((first, bytes) :: (next, nextBytes) :: remaining)

private theorem checkWalSegmentSizes_iff (through : Nat) (files : List (Nat × ByteArray)) :
    checkWalSegmentSizes through files = true ↔ WalSegmentSpans through files := by
  induction files with
  | nil => simp [checkWalSegmentSizes]; intro accepted; cases accepted
  | cons file remaining ih =>
    obtain ⟨first, bytes⟩ := file
    cases remaining with
    | nil =>
      simp only [checkWalSegmentSizes, decide_eq_true_eq]
      exact ⟨.active, fun accepted => by cases accepted; assumption⟩
    | cons next rest =>
      obtain ⟨next, nextBytes⟩ := next
      simp only [checkWalSegmentSizes, Bool.and_eq_true, decide_eq_true_eq, ih]
      exact ⟨fun ⟨⟨forward, size⟩, accepted⟩ => .sealed forward size accepted,
        fun accepted => by cases accepted; exact ⟨⟨‹first < next›, ‹_›⟩, ‹_›⟩⟩

theorem checkWalSegmentSpans_iff (through : Nat) (files : List (Nat × ByteArray)) :
    checkWalSegmentSpans through files = true ↔
      (∃ first rest, files = first :: rest ∧ first.1 ≤ through) ∧ WalSegmentSpans through files := by
  rw [checkWalSegmentSpans, Bool.and_eq_true, checkWalSegmentSizes_iff]
  cases files with
  | nil => simp
  | cons file rest => simp

/-- The marker-limited vector has no later starts. Each required sealed
file must fill its exact span, and the keeper must reach the marker. -/
def checkSelectedWalSegmentSpans (through : Nat) (files : List (Nat × ByteArray)) : Bool :=
  files.all (fun file => decide (file.1 ≤ through)) && checkWalSegmentSpans through files

def walSegmentPayloadBytes (files : List (Nat × ByteArray)) : ByteArray :=
  files.foldr (fun file later => file.2 ++ later) ByteArray.empty

private def copyWalSegmentPrefix (buffer : ByteArray) (remaining : Nat) : List (Nat × ByteArray) → ByteArray
  | [] => buffer
  | (_, bytes) :: rest =>
    if remaining = 0 then
      buffer
    else
      copyWalSegmentPrefix (bytes.copySlice 0 buffer buffer.size remaining) (remaining - bytes.size) rest

private theorem copyWalSegmentPrefix_eq (buffer : ByteArray) (remaining : Nat) (files : List (Nat × ByteArray)) :
    copyWalSegmentPrefix buffer remaining files = buffer ++ (walSegmentPayloadBytes files).extract 0 remaining := by
  induction files generalizing buffer remaining with
  | nil =>
    have noBytes : ByteArray.empty.extract 0 remaining = ByteArray.empty := by
      apply ByteArray.ext
      simp
    simp [copyWalSegmentPrefix, walSegmentPayloadBytes, noBytes]
  | cons file rest ih =>
    obtain ⟨offset, bytes⟩ := file
    by_cases empty : remaining = 0
    · simp [copyWalSegmentPrefix, empty]
    · have copy : bytes.copySlice 0 buffer buffer.size remaining = buffer ++ bytes.extract 0 remaining := by
        rw [ByteArray.copySlice_eq_append, ByteArray.extract_zero_size]
        simp
      rw [copyWalSegmentPrefix, ite_eq_right empty, ih, copy]
      change _ = buffer ++ (bytes ++ walSegmentPayloadBytes rest).extract 0 remaining
      rw [ByteArray.extract_append, Nat.zero_sub, ByteArray.append_assoc]

/-- Copy each required payload slice once into a single owned buffer.
An exactly sized sole segment can be used directly. -/
private def walSegmentPrefixBytes (count : Nat) (files : List (Nat × ByteArray)) : ByteArray :=
  match files with
  | [(_, bytes)] => if count = bytes.size then bytes else bytes.extract 0 count
  | _ => copyWalSegmentPrefix (ByteArray.emptyWithCapacity count) count files

private theorem walSegmentPrefixBytes_eq (count : Nat) (files : List (Nat × ByteArray)) :
    walSegmentPrefixBytes count files = (walSegmentPayloadBytes files).extract 0 count := by
  unfold walSegmentPrefixBytes
  split
  · next offset bytes =>
      by_cases exactSize : count = bytes.size <;> simp [walSegmentPayloadBytes, exactSize]
  · simp [copyWalSegmentPrefix_eq, show ByteArray.emptyWithCapacity count = ByteArray.empty from rfl]

/-- Validate file boundaries before passing the selected bytes to the
ordinary retained decoder. The keeper can contain an unselected tail. -/
def recoverMarkedWalSegments (base : PackedTable) (length : UInt64) (files : List (Nat × ByteArray)) :
    Except String (ByteArray × PackedTable) :=
  match files with
  | [] => .error "invalid selected WAL segment spans"
  | (first, _) :: _ =>
    if checkSelectedWalSegmentSpans (length.toNat / frameSize) files then
      let count := length.toNat - first * frameSize
      WAL.Boundary.recoverRetainedMarked base first length (walSegmentPrefixBytes count files)
    else .error "invalid selected WAL segment spans"

theorem recoverMarkedWalSegments_eq_extract (base : PackedTable) (length : UInt64) (first : Nat)
    (bytes : ByteArray) (rest : List (Nat × ByteArray))
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true) :
    recoverMarkedWalSegments base length ((first, bytes) :: rest) =
      WAL.Boundary.recoverRetainedMarked base first length
        ((walSegmentPayloadBytes ((first, bytes) :: rest)).extract 0 (length.toNat - first * frameSize)) := by
  simp only [recoverMarkedWalSegments, checked, ↓reduceIte, walSegmentPrefixBytes_eq]

end Alvoki.Storage
