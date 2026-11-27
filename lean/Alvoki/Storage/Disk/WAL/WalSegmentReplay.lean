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

/-- Calls to the prefix copy primitive and the sum of the clipped source-slice lengths.
The count excludes destination allocation and any copying inside the runtime. -/
structure WalPrefixCopyWork where
  calls : Nat
  sourceBytes : Nat

private noncomputable def copyWalSegmentPrefixWithWork (buffer : ByteArray) (remaining : Nat) :
    List (Nat × ByteArray) → ByteArray × WalPrefixCopyWork
  | [] => (buffer, ⟨0, 0⟩)
  | (_, bytes) :: rest =>
    if remaining = 0 then (buffer, ⟨0, 0⟩)
    else
      let reached := copyWalSegmentPrefixWithWork (bytes.copySlice 0 buffer buffer.size remaining)
        (remaining - bytes.size) rest
      (reached.1, ⟨reached.2.calls + 1, reached.2.sourceBytes + min remaining bytes.size⟩)

private theorem copyWalSegmentPrefixWithWork_spec
    (buffer : ByteArray) (remaining : Nat) (files : List (Nat × ByteArray)) :
    let reached := copyWalSegmentPrefixWithWork buffer remaining files
    reached.1 = copyWalSegmentPrefix buffer remaining files ∧ reached.2.calls ≤ files.length ∧
    reached.2.sourceBytes = min remaining (walSegmentPayloadBytes files).size := by
  induction files generalizing buffer remaining with
  | nil => simp [copyWalSegmentPrefixWithWork, copyWalSegmentPrefix, walSegmentPayloadBytes]
  | cons file rest ih =>
    obtain ⟨offset, bytes⟩ := file
    by_cases empty : remaining = 0
    · simp [copyWalSegmentPrefixWithWork, copyWalSegmentPrefix, empty]
    · have tail := ih (bytes.copySlice 0 buffer buffer.size remaining) (remaining - bytes.size)
      simp only [copyWalSegmentPrefixWithWork, copyWalSegmentPrefix, empty, ↓reduceIte] at ⊢
      refine ⟨tail.1, by simpa using Nat.add_le_add_right tail.2.1 1, ?_⟩
      rw [tail.2.2]
      change min (remaining - bytes.size) (walSegmentPayloadBytes rest).size + min remaining bytes.size =
        min remaining (bytes ++ walSegmentPayloadBytes rest).size
      rw [ByteArray.size_append]
      omega

/-- The same assembly uses a sole exact-sized file directly and otherwise
charges only the source portions copied into the requested prefix. -/
private noncomputable def walSegmentPrefixWithWork (count : Nat) (files : List (Nat × ByteArray)) :
    ByteArray × WalPrefixCopyWork :=
  match files with
  | [(_, bytes)] =>
    if count = bytes.size then (bytes, ⟨0, 0⟩)
    else (bytes.extract 0 count, ⟨1, min count bytes.size⟩)
  | _ => copyWalSegmentPrefixWithWork (ByteArray.emptyWithCapacity count) count files

private theorem walSegmentPrefixWithWork_spec (count : Nat) (files : List (Nat × ByteArray)) :
    let reached := walSegmentPrefixWithWork count files
    reached.1 = walSegmentPrefixBytes count files ∧ reached.2.calls ≤ files.length ∧ reached.2.sourceBytes ≤ count := by
  cases files with
  | nil => simp [walSegmentPrefixWithWork, walSegmentPrefixBytes, copyWalSegmentPrefixWithWork, copyWalSegmentPrefix]
  | cons file rest =>
    obtain ⟨offset, bytes⟩ := file
    cases rest with
    | nil =>
      by_cases exactSize : count = bytes.size
      · simp [walSegmentPrefixWithWork, walSegmentPrefixBytes, exactSize]
      · simp [walSegmentPrefixWithWork, walSegmentPrefixBytes, exactSize, Nat.min_le_left]
    | cons next rest =>
      have work := copyWalSegmentPrefixWithWork_spec (ByteArray.emptyWithCapacity count) count
        ((offset, bytes) :: next :: rest)
      exact ⟨work.1, work.2.1, work.2.2 ▸ Nat.min_le_left _ _⟩

/-- The counted interpreter runs the same span guard and prefix assembly,
then passes the exact assembled bytes to the ordinary recovery decoder. -/
noncomputable def recoverMarkedWalSegmentsWithCopyWork (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray)) : Except String (ByteArray × PackedTable) × WalPrefixCopyWork :=
  match files with
  | [] => (recoverMarkedWalSegments base length files, ⟨0, 0⟩)
  | (first, _) :: _ =>
    if checkSelectedWalSegmentSpans (length.toNat / frameSize) files then
      let reached := walSegmentPrefixWithWork (length.toNat - first * frameSize) files
      (WAL.Boundary.recoverRetainedMarked base first length reached.1, reached.2)
    else (recoverMarkedWalSegments base length files, ⟨0, 0⟩)

/-- Successful span selection charges at most one prefix copy per selected
file, within the marker-limited source byte budget. Bad spans copy nothing. -/
theorem recoverMarkedWalSegmentsWithCopyWork_spec (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray)) :
    let reached := recoverMarkedWalSegmentsWithCopyWork base length files
    reached.1 = recoverMarkedWalSegments base length files ∧ reached.2.calls ≤ files.length ∧
    reached.2.sourceBytes ≤ length.toNat - (files.head?.map Prod.fst).getD 0 * frameSize := by
  cases files with
  | nil => simp [recoverMarkedWalSegmentsWithCopyWork]
  | cons file rest =>
    obtain ⟨first, bytes⟩ := file
    by_cases checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true
    · obtain ⟨sameBuffer, calls, sourceBytes⟩ :=
        walSegmentPrefixWithWork_spec (length.toNat - first * frameSize) ((first, bytes) :: rest)
      have callsBound : (walSegmentPrefixWithWork (length.toNat - first * frameSize)
          ((first, bytes) :: rest)).2.calls ≤ rest.length + 1 := by
        simpa only [List.length_cons] using calls
      simp [recoverMarkedWalSegmentsWithCopyWork, recoverMarkedWalSegments, checked, sameBuffer, callsBound, sourceBytes]
    · simp [recoverMarkedWalSegmentsWithCopyWork, checked]

theorem recoverMarkedWalSegmentsWithCopyWork_rejectedSpans (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray))
    (invalid : checkSelectedWalSegmentSpans (length.toNat / frameSize) files = false) :
    let work := (recoverMarkedWalSegmentsWithCopyWork base length files).2
    work.calls = 0 ∧ work.sourceBytes = 0 := by
  cases files <;> simp [recoverMarkedWalSegmentsWithCopyWork, invalid]

/-- The exact-sized single-segment fast path makes no assembly copies. -/
theorem recoverMarkedWalSegmentsWithCopyWork_singleExact (base : PackedTable) (length : UInt64)
    (first : Nat) (bytes : ByteArray) (exactSize : length.toNat - first * frameSize = bytes.size) :
    let work := (recoverMarkedWalSegmentsWithCopyWork base length [(first, bytes)]).2
    work.calls = 0 ∧ work.sourceBytes = 0 := by
  by_cases checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) [(first, bytes)] = true <;>
    simp [recoverMarkedWalSegmentsWithCopyWork, walSegmentPrefixWithWork, exactSize, checked]

end Alvoki.Storage
