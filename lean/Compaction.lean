import PackedView
import ScopedBytes
import CompactionModel
import ByteWords

namespace Alvoki.Compaction
open Alvoki.Opt Alvoki.ScopedBytes

structure Run where
  private mk ::
  bytes : ByteArray
  count : USize
  size_eq : bytes.size = 16 + 32 * count.toNat

@[inline] private def readLane (run : @& Run) (i : USize) (lane : USize)
    (within : i < run.count) (laneFits : lane.toNat ≤ 40) : UInt64 :=
  wordBounded run.bytes (lane + 32 * i) (by
    have index := USize.lt_iff_toNat_lt.mp within
    have size := run.size_eq
    have stride : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [USize.toNat_add, USize.toNat_mul, stride]
    have offset : (lane.toNat + 32 * i.toNat % USize.size) % USize.size ≤ lane.toNat + 32 * i.toNat :=
      Nat.le_trans (Nat.mod_le ..) (Nat.add_le_add_left (Nat.mod_le ..) lane.toNat)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right offset 7) (by omega))

@[inline] private def key (run : @& Run) (i : USize) (within : i < run.count) : UInt64 :=
  readLane run i 16 within (by simp)

@[inline] private def sequence (run : @& Run) (i : USize) (within : i < run.count) : UInt64 :=
  readLane run i 24 within (by simp)

@[inline] private def kind (run : @& Run) (i : USize) : UInt64 :=
  wordMachine run.bytes (32 + 32 * i)

@[inline] private def value (run : @& Run) (i : USize) : UInt64 :=
  wordMachine run.bytes (40 + 32 * i)

private def validateFrom (run : @& Run) (i : USize) (prevKey prevSeq : UInt64)
    (firstRow : Bool) : Bool :=
  if within : i < run.count then
    let k := key run i within
    let seq := sequence run i within
    let tag := readLane run i 32 within (by simp)
    if tag > 1 || (tag == 1 && readLane run i 40 within (by simp) != 0) then false
    else if !firstRow && (k < prevKey || (k == prevKey && seq >= prevSeq)) then false
    else validateFrom run (i + 1) k seq false
  else true
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

def parse (bytes : ByteArray) : Except String Run :=
  if short : bytes.size < 16 then .error "expected a versioned run"
  else if word bytes 8 != 3 then .error "expected a versioned run"
  else
    let payload := bytes.size - 16
    let count := payload / 32
    if valid : bytes.size < USize.size ∧ payload % 32 = 0 ∧ (word bytes 0).toNat = count then
      have countExact : count.toUSize.toNat = count := USize.toNat_ofNat_of_lt (by
        have fits := valid.1
        dsimp [count, payload]
        omega)
      have size : bytes.size = 16 + 32 * count := by
        have aligned := valid.2.1
        dsimp [count, payload] at *
        omega
      let run : Run := ⟨bytes, count.toUSize, by rwa [countExact]⟩
      if validateFrom run 0 0 0 true then .ok run else .error "invalid version order or row kind"
    else .error "invalid versioned run length"

/-- Entries sort by key ascending and sequence descending. Equal pairs select right. -/
@[inline] private def first (ka sa kb sb : UInt64) : Bool :=
  ka < kb || (ka == kb && sa > sb)

@[specialize] private def visitFrom (left right : @& Run) (floor : UInt64)
    (emit : α → Bool → USize → UInt64 → UInt64 → α)
    (i j : USize) (previous : UInt64) (covered : Bool) (state : α) : α :=
  if hi : i < left.count then
    let a := key left i hi
    let sa := sequence left i hi
    if hj : j < right.count then
      let b := key right j hj
      let sb := sequence right j hj
      if first a sa b sb then
        let keep := a != previous || !covered
        let next := if keep then emit state false i a sa else state
        visitFrom left right floor emit (i + 1) j a (sa ≤ floor) next
      else
        let keep := b != previous || !covered
        let next := if keep then emit state true j b sb else state
        let skip := if a == b && sa == sb then i + 1 else i
        visitFrom left right floor emit skip (j + 1) b (sb ≤ floor) next
    else
      let keep := a != previous || !covered
      let next := if keep then emit state false i a sa else state
      visitFrom left right floor emit (i + 1) j a (sa ≤ floor) next
  else if hj : j < right.count then
    let b := key right j hj
    let sb := sequence right j hj
    let keep := b != previous || !covered
    let next := if keep then emit state true j b sb else state
    visitFrom left right floor emit i (j + 1) b (sb ≤ floor) next
  else state
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    try have li := USize.lt_iff_toNat_lt.mp hi
    try have ls := addOne i left.count li
    try have rj := USize.lt_iff_toNat_lt.mp hj
    try have rs := addOne j right.count rj
    try dsimp [skip]
    first | omega | (split <;> omega)

@[inline] private def visit (left right : @& Run) (floor : UInt64) (init : α)
    (emit : α → Bool → USize → UInt64 → UInt64 → α) : α :=
  visitFrom left right floor emit 0 0 0 false init

@[inline] private def payloadOffset (i : USize) : Nat := 16 + i.toNat * 32

private def initial (a b : @& Run) : Builder :=
  Builder.ofPrefix (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity
    (16 + 32 * (a.count.toNat + b.count.toNat))) 0) 3)

private def finish (out : Builder) : ByteArray :=
  let bytes := out.finish
  let header := pushWordFast (ByteArray.emptyWithCapacity 8) ((bytes.size - 16) / 32).toUInt64
  header.copySlice 0 bytes 0 8

def compact (left right : @& Run) (floor : UInt64) : ByteArray :=
  finish (visit left right floor (initial left right) fun out fromRight i _ _ =>
    let source := if fromRight then right else left
    out.copyToTail source.bytes (payloadOffset i) 32)

private structure Pending where
  output : Builder
  right : Bool
  start : USize
  stop : USize

@[inline] private def flush (left right : @& Run) (span : Pending) : Builder :=
  if span.start == span.stop then span.output
  else
    let source := if span.right then right else left
    span.output.copyToTail source.bytes (payloadOffset span.start)
      (32 * (span.stop.toNat - span.start.toNat))

def compactSpans (left right : @& Run) (floor : UInt64) : ByteArray :=
  let span : Pending := ⟨initial left right, false, 0, 0⟩
  let tail := visit left right floor span fun prev fromRight i _ _ =>
    if fromRight == prev.right && i == prev.stop then { prev with stop := i + 1 }
    else ⟨flush left right prev, fromRight, i, i + 1⟩
  finish (flush left right tail)

/-- Fold the visible non-tombstone rows at the given snapshot. -/
def scan (left right : @& Run) (snapshot : UInt64) : UInt64 :=
  visit left right snapshot 0 fun sum fromRight i k seq =>
    let source := if fromRight then right else left
    if seq ≤ snapshot && kind source i == 0 then sum + (k ^^^ value source i) else sum

def Run.scan (run : @& Run) (snapshot : UInt64) : UInt64 :=
  let empty := pushWordFast (pushWordFast ByteArray.empty 0) 3
  Alvoki.Compaction.scan run ⟨empty, 0, by
    have zero : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [zero]
    rfl⟩ snapshot

/-- Natural-offset interpretation of the four little-endian words in a v3 row. -/
def rawRow (bytes : ByteArray) (i : Nat) : Model.Entry (UInt64 × UInt64) :=
  ⟨word bytes (16 + i * 32), word bytes (24 + i * 32),
    (word bytes (32 + i * 32), word bytes (40 + i * 32))⟩

def rawRows (bytes : ByteArray) (count : Nat) : List (Model.Entry (UInt64 × UInt64)) :=
  (List.range count).map (rawRow bytes)

/-- A put has tag zero and an arbitrary value. A tombstone has tag one and a zero value. -/
def CanonicalRow (row : Model.Entry (UInt64 × UInt64)) : Prop :=
  row.payload.1 = 0 ∨ row.payload.1 = 1 ∧ row.payload.2 = 0

/-- The byte-level v3 contract, independent of machine offsets and the executable parser. -/
def ValidV3 (bytes : ByteArray) : Prop :=
  let count := (word bytes 0).toNat
  bytes.size < USize.size ∧ word bytes 8 = 3 ∧ bytes.size = 16 + 32 * count ∧
    Model.Ordered (rawRows bytes count) ∧ ∀ row ∈ rawRows bytes count, CanonicalRow row

private theorem naturalLane (run : Run) {i : USize} (lane : USize)
    (within : i < run.count) (laneFits : lane.toNat ≤ 40)
    (fits : run.bytes.size < USize.size) :
    (lane + 32 * i).toNat = lane.toNat + 32 * i.toNat := by
  have index := USize.lt_iff_toNat_lt.mp within
  have size := run.size_eq
  rw [USize.toNat_add, USize.toNat_mul,
    show (32 : USize).toNat = 32 from USize.toNat_ofNat_of_lt_32 (by decide)]
  rw [Nat.mod_eq_of_lt (show 32 * i.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show lane.toNat + 32 * i.toNat < USize.size by omega)]

private theorem readLane_eq (run : Run) {i : USize} (lane : USize)
    (within : i < run.count) (laneFits : lane.toNat ≤ 40)
    (fits : run.bytes.size < USize.size) :
    readLane run i lane within laneFits = word run.bytes (lane.toNat + 32 * i.toNat) := by
  unfold readLane
  rw [wordBounded_eq _ _ fits, naturalLane run lane within laneFits fits]

private theorem tagValue_eq (run : Run) {i : USize} (within : i < run.count)
    (fits : run.bytes.size < USize.size) :
    kind run i = (rawRow run.bytes i.toNat).payload.1 ∧
      value run i = (rawRow run.bytes i.toNat).payload.2 := by
  have index := USize.lt_iff_toNat_lt.mp within
  have size := run.size_eq
  have tagOffset := naturalLane run 32 within (by simp) fits
  have valOffset := naturalLane run 40 within (by simp) fits
  simp only [show (32 : USize).toNat = 32 from USize.toNat_ofNat_of_lt_32 (by decide),
    show (40 : USize).toNat = 40 from USize.toNat_ofNat_of_lt_32 (by decide)] at tagOffset valOffset
  unfold kind value rawRow
  dsimp only
  rw [wordMachine_eq _ _ fits (by rw [tagOffset]; omega),
    wordMachine_eq _ _ fits (by rw [valOffset]; omega), tagOffset, valOffset, Nat.mul_comm 32]
  exact ⟨rfl, rfl⟩

private theorem keys_eq (run : Run) {i : USize} (within : i < run.count)
    (fits : run.bytes.size < USize.size) :
    key run i within = (rawRow run.bytes i.toNat).key ∧
      sequence run i within = (rawRow run.bytes i.toNat).sequence := by
  simp only [key, sequence, readLane_eq _ _ _ _ fits, rawRow,
    show (16 : USize).toNat = 16 from USize.toNat_ofNat_of_lt_32 (by decide),
    show (24 : USize).toNat = 24 from USize.toNat_ofNat_of_lt_32 (by decide), Nat.mul_comm, and_self]

private def rawSuffix (run : Run) (i : USize) : List (Model.Entry (UInt64 × UInt64)) :=
  (List.range' i.toNat (run.count.toNat - i.toNat)).map (rawRow run.bytes)

private theorem rawSuffix_hit (run : Run) {i : USize} (within : i < run.count) :
    rawSuffix run i = rawRow run.bytes i.toNat :: rawSuffix run (i + 1) := by
  have index := USize.lt_iff_toNat_lt.mp within
  have advance := addOne i run.count index
  have length : run.count.toNat - i.toNat = (run.count.toNat - (i + 1).toNat) + 1 := by omega
  unfold rawSuffix
  conv => lhs; rw [length, List.range'_succ, List.map_cons]
  rw [advance]

private theorem rawSuffix_end (run : Run) {i : USize} (stop : ¬ i < run.count) :
    rawSuffix run i = [] := by
  rw [USize.lt_iff_toNat_lt] at stop
  simp [rawSuffix, show run.count.toNat - i.toNat = 0 by omega]

private theorem canonical_iff (row : Model.Entry (UInt64 × UInt64)) :
    CanonicalRow row ↔ ¬ (row.payload.1 > 1 ∨ row.payload.1 = 1 ∧ row.payload.2 ≠ 0) := by
  change row.payload.1 = 0 ∨ row.payload.1 = 1 ∧ row.payload.2 = 0 ↔
    ¬ (1 < row.payload.1 ∨ row.payload.1 = 1 ∧ row.payload.2 ≠ 0)
  rw [← UInt64.toNat_inj (a := row.payload.1) (b := 0),
    ← UInt64.toNat_inj (a := row.payload.1) (b := 1),
    ← UInt64.toNat_inj (a := row.payload.2) (b := 0), UInt64.lt_iff_toNat_lt]
  have valueNonzero : row.payload.2 ≠ 0 ↔ row.payload.2.toNat ≠ 0 := by
    exact not_congr (UInt64.toNat_inj (a := row.payload.2) (b := 0)).symm
  rw [valueNonzero]
  change row.payload.1.toNat = 0 ∨ row.payload.1.toNat = 1 ∧ row.payload.2.toNat = 0 ↔
    ¬ (1 < row.payload.1.toNat ∨ row.payload.1.toNat = 1 ∧ row.payload.2.toNat ≠ 0)
  omega

private theorem guard (p : Prop) [Decidable p] (rest : Bool) :
    (if p then false else rest) = true ↔ ¬p ∧ rest = true := by
  by_cases h : p <;> simp [h]

set_option maxHeartbeats 500000 in
private theorem validateFrom_spec (run : Run) (fits : run.bytes.size < USize.size)
    (i : USize) (pk ps : UInt64) (firstRow : Bool) :
    validateFrom run i pk ps firstRow = true ↔
      Model.Ordered (rawSuffix run i) ∧
        (∀ r ∈ rawSuffix run i, CanonicalRow r) ∧
        (firstRow = true ∨ ∀ r ∈ rawSuffix run i, Model.before ⟨pk, ps, (0, 0)⟩ r) := by
  rw [validateFrom]
  by_cases within : i < run.count
  · rw [dite_eq_left within, rawSuffix_hit run within]
    let row := rawRow run.bytes i.toNat
    have keys := keys_eq run within fits
    have tag : readLane run i 32 within (by simp) = row.payload.1 := by
      rw [readLane_eq run _ within _ fits]
      simp only [row, rawRow, show (32 : USize).toNat = 32 from USize.toNat_ofNat_of_lt_32
        (by decide), Nat.mul_comm 32]
    have value : readLane run i 40 within (by simp) = row.payload.2 := by
      rw [readLane_eq run _ within _ fits]
      simp only [row, rawRow, show (40 : USize).toNat = 40 from USize.toNat_ofNat_of_lt_32
        (by decide), Nat.mul_comm 32]
    simp only [keys.1, keys.2, tag, value]
    change (if row.payload.1 > 1 || (row.payload.1 == 1 && row.payload.2 != 0) then false
      else if !firstRow && (row.key < pk || (row.key == pk && row.sequence ≥ ps)) then false
      else validateFrom run (i + 1) row.key row.sequence false) = true ↔ _
    have sameOrder (r : Model.Entry (UInt64 × UInt64)) :
        Model.before ⟨row.key, row.sequence, (0, 0)⟩ r = Model.before row r := rfl
    have orderGuard : ¬ (!firstRow && (row.key < pk ||
        (row.key == pk && row.sequence ≥ ps))) = true ↔
        firstRow = true ∨ Model.before ⟨pk, ps, (0, 0)⟩ row = true := by
      cases firstRow
      · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, false_or,
          Model.before_iff, Bool.or_eq_true, Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_eq,
          UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
        omega
      · simp
    rw [guard, guard, orderGuard,
      validateFrom_spec run fits (i + 1) row.key row.sequence false]
    simp only [Bool.false_eq_true, false_or, Bool.or_eq_true, Bool.and_eq_true_iff,
      beq_iff_eq, bne_iff_ne, decide_eq_true_eq, ← canonical_iff, sameOrder,
      Model.Ordered, List.pairwise_cons, List.forall_mem_cons]
    constructor
    · rintro ⟨canon, previous, ordered, tags, prior⟩
      refine ⟨⟨prior, ordered⟩, ⟨canon, tags⟩, ?_⟩
      exact previous.imp id fun h => ⟨h, fun r mem => Model.before_trans h (prior r mem)⟩
    · rintro ⟨⟨prior, ordered⟩, ⟨canon, tags⟩, previous⟩
      exact ⟨canon, previous.imp id And.left, ordered, tags, prior⟩
  · rw [dite_eq_right within, rawSuffix_end run within]
    simp [Model.Ordered]
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

private theorem rawSuffix_zero (run : Run) :
    rawSuffix run 0 = rawRows run.bytes run.count.toNat := by
  unfold rawSuffix rawRows
  rw [show (0 : USize).toNat = 0 from USize.toNat_ofNat_of_lt_32 (by decide),
    Nat.sub_zero, List.range_eq_range']

theorem parse_spec {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    run.bytes = bytes ∧ run.count.toNat = (word bytes 0).toNat ∧ ValidV3 bytes := by
  unfold parse at accepted
  split at accepted
  · contradiction
  split at accepted
  · contradiction
  next version =>
    have v : word bytes 8 = 3 := by simpa using version
    dsimp only at accepted
    split at accepted
    next valid =>
      split at accepted
      next checked =>
        injection accepted with same
        subst run
        let payloadCount := (bytes.size - 16) / 32
        have count : payloadCount.toUSize.toNat = (word bytes 0).toNat := by
          have exactCount : payloadCount.toUSize.toNat = payloadCount :=
            USize.toNat_ofNat_of_lt (by dsimp [payloadCount]; have h := valid.1; omega)
          rw [exactCount]
          exact valid.2.2.symm
        obtain ⟨order, tags, _⟩ := (validateFrom_spec _ valid.1 0 0 0 true).mp checked
        rw [rawSuffix_zero] at order tags
        have size := (show Run from ⟨bytes, payloadCount.toUSize, by
          rw [count, valid.2.2]
          have h := valid.2.1
          change bytes.size = 16 + 32 * ((bytes.size - 16) / 32)
          omega⟩).size_eq
        dsimp only at size order tags ⊢
        rw [count] at size order tags
        exact ⟨rfl, count, valid.1, v, size, order, tags⟩
      · contradiction
    · contradiction

theorem parse_iff (bytes : ByteArray) : (∃ run, parse bytes = .ok run) ↔ ValidV3 bytes := by
  refine ⟨fun ⟨_, accepted⟩ => (parse_spec accepted).2.2, ?_⟩
  rintro ⟨fits, version, size, order, tags⟩
  have short : ¬ bytes.size < 16 := by omega
  have aligned : (bytes.size - 16) % 32 = 0 := by omega
  have countEq : (word bytes 0).toNat = (bytes.size - 16) / 32 := by omega
  have zeroVersion : ¬ (word bytes 8 != 3) = true := by simp [version]
  have header : bytes.size < USize.size ∧ (bytes.size - 16) % 32 = 0 ∧
      (word bytes 0).toNat = (bytes.size - 16) / 32 := ⟨fits, aligned, countEq⟩
  let n := (bytes.size - 16) / 32
  have count : n.toUSize.toNat = (word bytes 0).toNat := by
    have exactCount : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt (by change (bytes.size - 16) / 32 < USize.size; omega)
    rw [exactCount]
    exact countEq.symm
  let run : Run := ⟨bytes, n.toUSize, by rwa [count]⟩
  have checked : validateFrom run 0 0 0 true = true := by
    apply (validateFrom_spec run fits 0 0 0 true).mpr
    rw [rawSuffix_zero]
    change _ ∧ _ ∧ (_ ∨ ∀ r ∈ rawRows bytes n.toUSize.toNat, _)
    have h : rawRows run.bytes run.count.toNat = rawRows bytes (word bytes 0).toNat := by
      change rawRows bytes n.toUSize.toNat = _
      rw [count]
    rw [h]
    exact ⟨order, tags, Or.inl rfl⟩
  refine ⟨run, ?_⟩
  unfold parse
  rw [dite_eq_right short, ite_eq_right zeroVersion]
  dsimp only
  rw [dite_eq_left header]
  change (if validateFrom run 0 0 0 true then Except.ok run else Except.error (_ : String)) = Except.ok run
  rw [ite_eq_left checked]

theorem rejects_version {bytes : ByteArray} (wrong : word bytes 8 ≠ 3) :
    ¬ ∃ run, parse bytes = .ok run :=
  fun accepted => wrong ((parse_iff bytes).mp accepted).2.1

theorem rejects_length {bytes : ByteArray}
    (wrong : bytes.size ≠ 16 + 32 * (word bytes 0).toNat) :
    ¬ ∃ run, parse bytes = .ok run :=
  fun accepted => wrong ((parse_iff bytes).mp accepted).2.2.1

theorem rejects_order {bytes : ByteArray}
    (wrong : ¬ Model.Ordered (rawRows bytes (word bytes 0).toNat)) :
    ¬ ∃ run, parse bytes = .ok run :=
  fun accepted => wrong ((parse_iff bytes).mp accepted).2.2.2.1

theorem rejects_row {bytes : ByteArray} {row : Model.Entry (UInt64 × UInt64)}
    (present : row ∈ rawRows bytes (word bytes 0).toNat) (invalid : ¬ CanonicalRow row) :
    ¬ ∃ run, parse bytes = .ok run :=
  fun accepted => invalid (((parse_iff bytes).mp accepted).2.2.2.2 row present)

private def rowsFrom (run : Run) (payload : USize → α) (i : USize) : List (Model.Entry α) :=
  if within : i < run.count then
    ⟨key run i within, sequence run i within, payload i⟩ ::
      rowsFrom run payload (i + 1)
  else []
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

private theorem rowsFrom_hit (run : Run) (payload : USize → α) {i : USize}
    (within : i < run.count) :
    rowsFrom run payload i = ⟨key run i within, sequence run i within, payload i⟩ ::
      rowsFrom run payload (i + 1) := by
  rw [rowsFrom, dite_eq_left within]

private theorem rowsFrom_end (run : Run) (payload : USize → α) {i : USize}
    (within : ¬ i < run.count) : rowsFrom run payload i = [] := by
  rw [rowsFrom, dite_eq_right within]

/-- Ordered source positions, carrying the version fields used by the merge. -/
def Run.positions (run : Run) (fromRight : Bool) : List (Model.Entry (Bool × USize)) :=
  rowsFrom run (fun i => (fromRight, i)) 0

private theorem fold_retain_cons (floor previous : UInt64) (covered : Bool)
    (row : Model.Entry β) (rows : List (Model.Entry β)) (step : α → Model.Entry β → α) (state : α) :
    (Model.retainFrom floor previous covered (row :: rows)).foldl step state =
      (Model.retainFrom floor row.key (row.sequence ≤ floor) rows).foldl step
        (if row.key != previous || !covered then step state row else state) := by
  rw [Model.retainFrom]
  split <;> rfl

private theorem visitFrom_refines (left right : Run) (floor : UInt64)
    (emit : α → Bool → USize → UInt64 → UInt64 → α)
    (i j : USize) (previous : UInt64) (covered : Bool) (state : α) :
    visitFrom left right floor emit i j previous covered state =
      (Model.retainFrom floor previous covered
        (Model.union (rowsFrom left (fun n => (false, n)) i)
          (rowsFrom right (fun n => (true, n)) j))).foldl
        (fun out row => emit out row.payload.1 row.payload.2 row.key row.sequence) state := by
  fun_induction visitFrom with
  | case1 i j previous covered state hi a sa hj b sb order keep next ih =>
    rw [ih, rowsFrom_hit left _ hi, rowsFrom_hit right _ hj, Model.union.eq_3]
    have h : Model.before ⟨a, sa, (false, i)⟩ ⟨b, sb, (true, j)⟩ = true := order
    rw [ite_eq_left h, fold_retain_cons]
    rfl
  | case2 i j previous covered state hi a sa hj b sb order keep next skip ih =>
    rw [ih, rowsFrom_hit left _ hi, rowsFrom_hit right _ hj, Model.union.eq_3]
    have h : ¬ Model.before ⟨a, sa, (false, i)⟩ ⟨b, sb, (true, j)⟩ = true := order
    rw [ite_eq_right h]
    by_cases tie : (a == b && sa == sb) = true
    · have same : Model.sameVersion ⟨a, sa, (false, i)⟩ ⟨b, sb, (true, j)⟩ = true := tie
      rw [ite_eq_left same, fold_retain_cons]
      have advance : skip = i + 1 := ite_eq_left tie
      rw [advance]
      rfl
    · have same : ¬Model.sameVersion ⟨a, sa, (false, i)⟩ ⟨b, sb, (true, j)⟩ = true := tie
      rw [ite_eq_right same, fold_retain_cons]
      have stay : skip = i := ite_eq_right tie
      rw [stay, rowsFrom_hit left _ hi]
      rfl
  | case3 i j previous covered state hi a sa hj keep next ih =>
    rw [ih, rowsFrom_end right _ hj, rowsFrom_hit left _ hi]
    simp only [Model.union_nil_right, fold_retain_cons]
    rfl
  | case4 i j previous covered state hi hj b sb keep next ih =>
    rw [ih, rowsFrom_end left _ hi, rowsFrom_hit right _ hj]
    simp only [Model.union_nil_left, fold_retain_cons]
    rfl
  | case5 i j previous covered state hi hj =>
    rw [rowsFrom_end left _ hi, rowsFrom_end right _ hj, Model.union_nil_left]
    rfl

/-- The executable visitor folds over exactly the positions retained by the model. -/
theorem visit_refines (left right : Run) (floor : UInt64) (state : α)
    (emit : α → Bool → USize → UInt64 → UInt64 → α) :
    visit left right floor state emit =
      (Model.retain (Model.union (left.positions false) (right.positions true)) floor).foldl
        (fun out row => emit out row.payload.1 row.payload.2 row.key row.sequence) state :=
  visitFrom_refines left right floor emit 0 0 0 false state

abbrev Position := Bool × USize

def Run.source (left right : Run) (position : Position) : Run :=
  if position.1 then right else left

def positionsRetained (left right : Run) (floor : UInt64) : List (Model.Entry Position) :=
  Model.retain (Model.union (left.positions false) (right.positions true)) floor

def rowBytes (left right : Run) (position : Position) : ByteArray :=
  let source := left.source right position
  source.bytes.extract (payloadOffset position.2) (payloadOffset position.2 + 32)

private theorem rowsFrom_mem (run : Run) (fromRight : Bool) (i : USize)
    (row : Model.Entry Position) (found : row ∈ rowsFrom run (fun n => (fromRight, n)) i) :
    row.payload.1 = fromRight ∧ row.payload.2 < run.count := by
  by_cases within : i < run.count
  · rw [rowsFrom_hit run _ within, List.mem_cons] at found
    rcases found with rfl | mem
    · exact ⟨rfl, within⟩
    · exact rowsFrom_mem run fromRight (i + 1) row mem
  · simp [rowsFrom_end run _ within] at found
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

theorem position_bounds {left right : Run} {row : Model.Entry Position}
    (found : row ∈ Model.union (left.positions false) (right.positions true)) :
    row.payload.2 < (left.source right row.payload).count := by
  rcases Model.mem_union found with leftMem | rightMem
  · have h := rowsFrom_mem left false 0 row leftMem
    simpa [Run.source, h.1] using h.2
  · have h := rowsFrom_mem right true 0 row rightMem
    simpa [Run.source, h.1] using h.2

theorem retained_bounds {left right : Run} {floor : UInt64} {row : Model.Entry Position}
    (found : row ∈ positionsRetained left right floor) :
    row.payload.2 < (left.source right row.payload).count :=
  position_bounds ((Model.retainFrom_sublist _ floor 0 false).subset found)

private theorem positions_decodeFrom (left right : Run) (fromRight : Bool)
    (fits : (left.source right (fromRight, 0)).bytes.size < USize.size) (i : USize) :
    let run := left.source right (fromRight, 0)
    (rowsFrom run (fun n => (fromRight, n)) i).map
      (Model.Entry.mapPayload (fun position =>
        (rawRow (left.source right position).bytes position.2.toNat).payload)) =
      rawSuffix run i := by
  let run := left.source right (fromRight, 0)
  change (rowsFrom run (fun n => (fromRight, n)) i).map
    (Model.Entry.mapPayload _) = rawSuffix run i
  by_cases hit : i < run.count
  · have keys := keys_eq run hit fits
    rw [rowsFrom_hit run _ hit, rawSuffix_hit run hit, List.map_cons,
      positions_decodeFrom left right fromRight fits (i + 1)]
    simp only [Model.Entry.mapPayload, keys.1, keys.2, List.cons.injEq]
    refine ⟨?_, rfl⟩
    let r := rawRow run.bytes i.toNat
    change (⟨r.key, r.sequence, r.payload⟩ : Model.Entry (UInt64 × UInt64)) = r
    cases r
    rfl
  · rw [rowsFrom_end run _ hit, rawSuffix_end run hit, List.map_nil]
termination_by (left.source right (fromRight, 0)).count.toNat - i.toNat
decreasing_by
  change run.count.toNat - (i + 1).toNat < run.count.toNat - i.toNat
  have index := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i run.count index
  omega

theorem positions_decode (left right : Run) (fromRight : Bool)
    (fits : (left.source right (fromRight, 0)).bytes.size < USize.size) :
    let run := left.source right (fromRight, 0)
    (run.positions fromRight).map
      (Model.Entry.mapPayload (fun position =>
        (rawRow (left.source right position).bytes position.2.toNat).payload)) =
      rawRows run.bytes run.count.toNat := by
  dsimp only
  rw [← rawSuffix_zero, Run.positions]
  exact positions_decodeFrom left right fromRight fits 0

private theorem rowsFrom_keys (run : Run) (fromRight : Bool) (i : USize)
    (fits : run.bytes.size < USize.size)
    (row : Model.Entry Position) (found : row ∈ rowsFrom run (fun n => (fromRight, n)) i) :
    row.key = (rawRow run.bytes row.payload.2.toNat).key ∧
      row.sequence = (rawRow run.bytes row.payload.2.toNat).sequence := by
  by_cases within : i < run.count
  · rw [rowsFrom_hit run _ within, List.mem_cons] at found
    rcases found with rfl | mem
    · exact keys_eq run within fits
    · exact rowsFrom_keys run fromRight (i + 1) fits row mem
  · simp [rowsFrom_end run _ within] at found
termination_by run.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp within
  have step := addOne i run.count index
  omega

theorem position_key_sequence {left right : Run} {row : Model.Entry Position}
    (found : row ∈ Model.union (left.positions false) (right.positions true))
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    row.key = (rawRow (left.source right row.payload).bytes row.payload.2.toNat).key ∧
      row.sequence = (rawRow (left.source right row.payload).bytes row.payload.2.toNat).sequence := by
  rcases Model.mem_union found with lm | rm
  · have h := (rowsFrom_mem left false 0 row lm).1
    simpa [Run.source, h] using rowsFrom_keys left false 0 leftFits row lm
  · have h := (rowsFrom_mem right true 0 row rm).1
    simpa [Run.source, h] using rowsFrom_keys right true 0 rightFits row rm

theorem position_fields {left right : Run} {row : Model.Entry Position}
    (found : row ∈ Model.union (left.positions false) (right.positions true))
    (fits : (left.source right row.payload).bytes.size < USize.size) :
    kind (left.source right row.payload) row.payload.2 =
        (rawRow (left.source right row.payload).bytes row.payload.2.toNat).payload.1 ∧
    value (left.source right row.payload) row.payload.2 =
        (rawRow (left.source right row.payload).bytes row.payload.2.toNat).payload.2 :=
  tagValue_eq (left.source right row.payload) (position_bounds found) fits

/-- Output bytes for a sequence of selected positions, in selection order. -/
def positionBytes (left right : Run) : List (Model.Entry Position) → ByteArray
  | [] => ByteArray.empty
  | row :: rows => rowBytes left right row.payload ++ positionBytes left right rows

private theorem positionBytes_size (left right : Run) (rows : List (Model.Entry Position))
    (bounded : ∀ row ∈ rows, row.payload.2 < (left.source right row.payload).count) :
    (positionBytes left right rows).size = 32 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have h := USize.lt_iff_toNat_lt.mp (bounded row List.mem_cons_self)
    have size := (left.source right row.payload).size_eq
    have extent : payloadOffset row.payload.2 + 32 ≤ (left.source right row.payload).bytes.size := by
      unfold payloadOffset
      omega
    simp only [positionBytes, rowBytes, ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left extent, Nat.add_sub_cancel_left, List.length_cons,
      ih (fun r mem => bounded r (List.mem_cons_of_mem _ mem))]
    omega

private theorem copyPositions (left right : Run) (rows : List (Model.Entry Position)) (init : Builder) :
    (rows.foldl (fun out row => out.copyToTail (left.source right row.payload).bytes
      (payloadOffset row.payload.2) 32) init).finish =
        init.finish ++ positionBytes left right rows := by
  induction rows generalizing init with
  | nil => simp [positionBytes]
  | cons row rows ih =>
    rw [List.foldl_cons, ih, copyToTail_refines, positionBytes, ByteArray.append_assoc]
    rfl

private theorem initial_eq (left right : Run) :
    (initial left right).finish = pushWordFast ByteArray.empty 0 ++ pushWordFast ByteArray.empty 3 := by
  simp only [initial, Builder.ofPrefix, Builder.finish]
  rw [ByteWords.pushWordFast_append _ 3]
  rfl

private theorem finish_eq (out : Builder) (payload : ByteArray) (count : Nat)
    (size : payload.size = 32 * count)
    (layout : out.finish =
      (pushWordFast ByteArray.empty 0 ++ pushWordFast ByteArray.empty 3) ++ payload) :
    finish out = pushWordFast (pushWordFast ByteArray.empty count.toUInt64) 3 ++ payload := by
  let pad := pushWordFast ByteArray.empty 0
  let version := pushWordFast ByteArray.empty 3
  let header := pushWordFast ByteArray.empty count.toUInt64
  have padSize : pad.size = 8 := rfl
  have verSize : version.size = 8 := rfl
  have hSize : header.size = 8 := by simp [header, ByteWords.pushWordFast_size]
  have width : (out.finish.size - 16) / 32 = count := by
    rw [layout, ByteArray.size_append, ByteArray.size_append, padSize, verSize, size]
    omega
  unfold finish
  simp only [width]
  have fresh : pushWordFast (ByteArray.emptyWithCapacity 8) count.toUInt64 = header := rfl
  rw [fresh, layout]
  change header.copySlice 0 ((pad ++ version) ++ payload) 0 8 = _
  rw [ByteArray.append_assoc, ByteArray.copySlice_eq_append]
  rw [show (pad ++ (version ++ payload)).extract 0 0 = ByteArray.empty by simp,
    ByteArray.empty_append, show header.extract 0 8 = header by
      rw [← hSize, ByteArray.extract_zero_size]]
  change header ++ (pad ++ (version ++ payload)).extract (0 + min 8 (header.size - 0))
    (pad ++ (version ++ payload)).size = _
  simp only [hSize, Nat.sub_zero, Nat.min_self, Nat.zero_add]
  rw [ByteArray.extract_append_eq_right padSize.symm ByteArray.size_append,
    ← ByteArray.append_assoc, ← ByteWords.pushWordFast_append header 3]

/-- The per-row kernel writes exactly the retained source slices and the v3 header. -/
theorem compact_refines (left right : Run) (floor : UInt64) :
    let rows := positionsRetained left right floor
    compact left right floor =
      pushWordFast (pushWordFast ByteArray.empty rows.length.toUInt64) 3 ++
        positionBytes left right rows := by
  let rows := positionsRetained left right floor
  unfold compact
  rw [visit_refines]
  apply finish_eq _ _ rows.length (positionBytes_size left right rows (fun _ => retained_bounds))
  exact (copyPositions left right rows (initial left right)).trans
    (congrArg (· ++ positionBytes left right rows) (initial_eq left right))

private theorem flush_eq (left right : Run) (span : Pending)
    (ordered : span.start.toNat ≤ span.stop.toNat) :
    (flush left right span).finish = span.output.finish ++
      (left.source right (span.right, span.start)).bytes.extract
        (payloadOffset span.start) (payloadOffset span.stop) := by
  unfold flush
  by_cases empty : span.start = span.stop
  · simp [empty]
  · rw [ite_eq_right (by simpa using empty), copyToTail_refines]
    have offset : payloadOffset span.start + 32 * (span.stop.toNat - span.start.toNat) =
        payloadOffset span.stop := by
      unfold payloadOffset
      omega
    rw [offset]
    rfl

private def extend (left right : Run) (prev : Pending) (row : Model.Entry Position) : Pending :=
  let (fromRight, i) := row.payload
  if fromRight == prev.right && i == prev.stop then { prev with stop := i + 1 }
  else ⟨flush left right prev, fromRight, i, i + 1⟩

private theorem extend_step (left right : Run) (prev : Pending) (row : Model.Entry Position)
    (ordered : prev.start.toNat ≤ prev.stop.toNat)
    (within : row.payload.2 < (left.source right row.payload).count) :
    let next := extend left right prev row
    next.start.toNat ≤ next.stop.toNat ∧
      (flush left right next).finish = (flush left right prev).finish ++
        rowBytes left right row.payload := by
  obtain ⟨key, seq, origin, i⟩ := row
  let row : Model.Entry Position := ⟨key, seq, (origin, i)⟩
  dsimp only [extend, row, Model.Entry.payload, Prod.fst, Prod.snd]
  have step := addOne i (left.source right (origin, i)).count (USize.lt_iff_toNat_lt.mp within)
  have offset : payloadOffset (i + 1) = payloadOffset i + 32 := by
    unfold payloadOffset
    rw [step]
    omega
  by_cases adjacent : origin = prev.right ∧ i = prev.stop
  · have test : (origin == prev.right && i == prev.stop) = true := by simpa using adjacent
    rw [ite_eq_left test]
    have ⟨originEq, posEq⟩ := adjacent
    have order : prev.start.toNat ≤ (i + 1).toNat := by rw [step, posEq]; omega
    refine ⟨order, ?_⟩
    rw [flush_eq left right _ order, flush_eq left right prev ordered]
    simp only [rowBytes, offset]
    rw [posEq, originEq, ByteArray.append_assoc]
    have ha : payloadOffset prev.start ≤ payloadOffset prev.stop := by
      unfold payloadOffset
      omega
    rw [ByteArray.extract_eq_extract_append_extract (a :=
      (left.source right (prev.right, prev.start)).bytes) (payloadOffset prev.stop) ha
      (Nat.le_add_right ..)]
    rfl
  · have test : ¬ (origin == prev.right && i == prev.stop) = true := by simpa using adjacent
    rw [ite_eq_right test]
    have order : i.toNat ≤ (i + 1).toNat := by omega
    refine ⟨order, ?_⟩
    rw [flush_eq left right _ order]
    simp only [rowBytes, offset]

private theorem flush_fold (left right : Run) (rows : List (Model.Entry Position)) (span : Pending)
    (ordered : span.start.toNat ≤ span.stop.toNat)
    (bounded : ∀ row ∈ rows, row.payload.2 < (left.source right row.payload).count) :
    (flush left right (rows.foldl (extend left right) span)).finish =
      (flush left right span).finish ++ positionBytes left right rows := by
  induction rows generalizing span with
  | nil => simp [positionBytes]
  | cons row rows ih =>
    have ⟨nextOrder, nextBytes⟩ := extend_step left right span row ordered
      (bounded row List.mem_cons_self)
    rw [List.foldl_cons, ih _ nextOrder (fun r mem => bounded r (List.mem_cons_of_mem _ mem)),
      nextBytes, ByteArray.append_assoc, positionBytes]

/-- Coalescing neighboring copies produces exactly the same bytes as the per-row path. -/
theorem compactSpans_eq_compact (left right : Run) (floor : UInt64) :
    compactSpans left right floor = compact left right floor := by
  let rows := positionsRetained left right floor
  let start : Pending := ⟨initial left right, false, 0, 0⟩
  unfold compactSpans
  dsimp only
  rw [visit_refines, compact_refines]
  change finish (flush left right (rows.foldl (extend left right) start)) = _
  apply finish_eq _ _ rows.length (positionBytes_size left right rows (fun _ => retained_bounds))
  rw [flush_fold left right rows start (Nat.le_refl _) (fun _ => retained_bounds)]
  exact congrArg (· ++ positionBytes left right rows) (initial_eq left right)

theorem scan_positions (left right : Run) (snapshot : UInt64) :
    scan left right snapshot =
      (positionsRetained left right snapshot).foldl (fun sum row =>
        let src := left.source right row.payload
        if row.sequence ≤ snapshot && kind src row.payload.2 == 0 then
          sum + (row.key ^^^ value src row.payload.2) else sum) 0 := by
  rw [scan, visit_refines]
  rfl

theorem Run.scan_with_empty (run : Run) (snapshot : UInt64) :
    ∃ empty : Run, empty.count.toNat = 0 ∧ empty.bytes.size < USize.size ∧
      run.scan snapshot = Alvoki.Compaction.scan run empty snapshot := by
  have count : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
  let bytes := pushWordFast (pushWordFast ByteArray.empty 0) 3
  let empty : Run := ⟨bytes, 0, by rw [count]; rfl⟩
  refine ⟨empty, count, ?_, rfl⟩
  rw [empty.size_eq, count]
  have h := USize.le_size
  omega

end Alvoki.Compaction
