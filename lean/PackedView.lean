import Block

namespace Alvoki.Opt

@[inline] private def byteMachine (bytes : @& ByteArray) (offset i : USize)
    (bound : offset.toNat + i.toNat < bytes.size) : UInt64 :=
  (bytes.uget (offset + i) (by
    rw [USize.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le ..) bound)).toUInt64

/-- Read one word when the caller has already established the byte extent. -/
@[inline] def wordBounded (bytes : @& ByteArray) (offset : USize)
    (bound : offset.toNat + 7 < bytes.size) : UInt64 :=
  have small (n : Nat) (hn : n ≤ 7) :
      offset.toNat + (USize.ofNat n).toNat < bytes.size :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_trans USize.toNat_ofNat_le hn) _) bound
  byteMachine bytes offset 0 (small 0 (by decide)) |||
    (byteMachine bytes offset 1 (small 1 (by decide)) <<< 8) |||
    (byteMachine bytes offset 2 (small 2 (by decide)) <<< 16) |||
    (byteMachine bytes offset 3 (small 3 (by decide)) <<< 24) |||
    (byteMachine bytes offset 4 (small 4 (by decide)) <<< 32) |||
    (byteMachine bytes offset 5 (small 5 (by decide)) <<< 40) |||
    (byteMachine bytes offset 6 (small 6 (by decide)) <<< 48) |||
    (byteMachine bytes offset 7 (small 7 (by decide)) <<< 56)

/-- Assemble a word using proof-carrying machine-sized byte offsets. -/
@[inline] def wordMachine (bytes : @& ByteArray) (offset : USize) : UInt64 :=
  if h : 7 < bytes.usize && offset < bytes.usize - 7 then
    have hsize : bytes.usize.toNat ≤ bytes.size := USize.toNat_ofNat_le
    have hle : (7 : USize) ≤ bytes.usize :=
      USize.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1)
    have hb : offset.toNat + 7 < bytes.size := by
      have hi : offset < bytes.usize - 7 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
      rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ hle] at hi
      rw [show (7 : USize).toNat = 7 from USize.toNat_ofNat_of_lt_32 (by decide)] at hi
      omega
    wordBounded bytes offset hb
  else 0

private theorem byteMachine_eq (bytes : ByteArray) (offset i : USize)
    (limit : bytes.size < USize.size)
    (bound : offset.toNat + i.toNat < bytes.size) :
    byteMachine bytes offset i bound = (bytes.get! (offset.toNat + i.toNat)).toUInt64 := by
  have index : (offset + i).toNat = offset.toNat + i.toNat := by
    rw [USize.toNat_add]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bound limit)
  cases bytes with
  | mk data =>
    unfold byteMachine ByteArray.uget ByteArray.get!
    have valid : (offset + i).toNat < data.size := index ▸ bound
    change (data[(offset + i).toNat]'valid).toUInt64 = (data[offset.toNat + i.toNat]!).toUInt64
    rw [getElem!_pos data _ bound]
    exact congrArg UInt8.toUInt64 (getElem_congr_idx index)

private theorem wordMachine_of_extent (bytes : ByteArray) (offset : USize)
    (limit : bytes.size < USize.size) (bound : offset.toNat + 7 < bytes.size) :
    wordMachine bytes offset = wordBounded bytes offset bound := by
  have sizeEq : bytes.usize.toNat = bytes.size := USize.toNat_ofNat_of_lt limit
  have seven : (7 : USize).toNat = 7 := USize.toNat_ofNat_of_lt_32 (by decide)
  have leSize : (7 : USize) ≤ bytes.usize := by
    rw [USize.le_iff_toNat_le, seven, sizeEq]
    omega
  have short : (7 : USize) < bytes.usize := by
    rw [USize.lt_iff_toNat_lt, seven, sizeEq]
    omega
  have inBounds : offset < bytes.usize - 7 := by
    rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ leSize, seven, sizeEq]
    omega
  unfold wordMachine
  rw [dite_eq_left (Bool.and_eq_true_iff.mpr ⟨decide_eq_true short, decide_eq_true inBounds⟩)]

theorem wordMachine_eq (bytes : ByteArray) (offset : USize)
    (limit : bytes.size < USize.size) (bound : offset.toNat + 7 < bytes.size) :
    wordMachine bytes offset = word bytes offset.toNat := by
  have digit (n : Nat) (hn : n < 8) : (USize.ofNat n).toNat = n :=
    USize.toNat_ofNat_of_lt_32 (by omega)
  rw [wordMachine_of_extent bytes offset limit bound]
  unfold word joinBytes wordBounded
  simp only [byteMachine_eq _ _ _ limit,
    show (0 : USize).toNat = 0 from digit 0 (by decide),
    show (1 : USize).toNat = 1 from digit 1 (by decide),
    show (2 : USize).toNat = 2 from digit 2 (by decide),
    show (3 : USize).toNat = 3 from digit 3 (by decide),
    show (4 : USize).toNat = 4 from digit 4 (by decide),
    show (5 : USize).toNat = 5 from digit 5 (by decide),
    show (6 : USize).toNat = 6 from digit 6 (by decide),
    show (7 : USize).toNat = 7 from digit 7 (by decide)]

structure View where
  private mk ::
  bytes : ByteArray
  count : USize
  stride : USize
  values : USize
  fits : bytes.size < USize.size
  size_eq : bytes.size = 16 + 16 * count.toNat
  layout : (stride.toNat = 16 ∧ values.toNat = 24) ∨
    (stride.toNat = 8 ∧ values.toNat = 16 + 8 * count.toNat)

private theorem View.keyExtent (view : View) {i : USize} (within : i < view.count) :
    ((16 : USize) + i * view.stride).toNat + 7 < view.bytes.size := by
  have index := USize.lt_iff_toNat_lt.mp within
  have size := view.size_eq
  have base : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_add, USize.toNat_mul, base]
  have offset : (16 + i.toNat * view.stride.toNat % USize.size) % USize.size ≤
      16 + i.toNat * view.stride.toNat :=
    Nat.le_trans (Nat.mod_le ..) (Nat.add_le_add_left (Nat.mod_le ..) 16)
  rcases view.layout with ⟨stride, _⟩ | ⟨stride, _⟩
  all_goals
    rw [stride] at offset ⊢
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right offset 7) (by omega)

private theorem View.valueExtent (view : View) {i : USize} (within : i < view.count) :
    (view.values + i * view.stride).toNat + 7 < view.bytes.size := by
  have index := USize.lt_iff_toNat_lt.mp within
  have size := view.size_eq
  rw [USize.toNat_add, USize.toNat_mul]
  have offset : (view.values.toNat + i.toNat * view.stride.toNat % USize.size) % USize.size ≤
      view.values.toNat + i.toNat * view.stride.toNat :=
    Nat.le_trans (Nat.mod_le ..) (Nat.add_le_add_left (Nat.mod_le ..) view.values.toNat)
  rcases view.layout with ⟨stride, value⟩ | ⟨stride, value⟩
  all_goals
    rw [stride, value] at offset ⊢
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right offset 7) (by omega)

/-- Checked scalar access for kernels that use a zero sentinel at exhaustion. -/
@[inline] def View.keyOrZero (view : @& View) (i : USize) : UInt64 :=
  if within : i < view.count then wordBounded view.bytes (16 + i * view.stride) (view.keyExtent within)
  else 0

@[inline] def View.valueOrZero (view : @& View) (i : USize) : UInt64 :=
  if within : i < view.count then wordBounded view.bytes
    (view.values + i * view.stride) (view.valueExtent within)
  else 0

theorem View.keyOrZero_wordMachine (view : View) (i : USize) (within : i < view.count) :
    view.keyOrZero i = wordMachine view.bytes (16 + i * view.stride) := by
  rw [keyOrZero, dite_eq_left within]
  exact (wordMachine_of_extent view.bytes _ view.fits (view.keyExtent within)).symm

theorem View.valueOrZero_wordMachine (view : View) (i : USize) (within : i < view.count) :
    view.valueOrZero i = wordMachine view.bytes (view.values + i * view.stride) := by
  rw [valueOrZero, dite_eq_left within]
  exact (wordMachine_of_extent view.bytes _ view.fits (view.valueExtent within)).symm

@[inline] def View.record? (view : @& View) (i : USize) : Option Record :=
  if i < view.count then some (view.keyOrZero i, view.valueOrZero i) else none

@[inline] private def View.keyInBounds (view : @& View) (i offset : USize)
    (position : offset = 16 + i * view.stride) (within : i < view.count) : UInt64 :=
  wordBounded view.bytes offset (position.symm ▸ view.keyExtent within)

private theorem View.keyInBounds_eq (view : View) (i offset : USize)
    (position : offset = 16 + i * view.stride) (within : i < view.count) :
    view.keyInBounds i offset position within = view.keyOrZero i := by
  subst offset
  simp only [keyInBounds, keyOrZero, dite_eq_left within]

private theorem View.nextKeyOffset (view : View) (i offset : USize)
    (position : offset = 16 + i * view.stride) :
    offset + view.stride = 16 + (i + 1) * view.stride := by
  rw [position, USize.add_mul, USize.one_mul, USize.add_assoc]

private theorem addExact (a b : USize) (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem addOne (a b : USize) (h : a.toNat < b.toNat) :
    (a + 1).toNat = a.toNat + 1 := by
  have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
  have lim := b.toNat_lt_size
  rw [addExact, one]
  rw [one]
  omega

private def View.validateFrom (view : @& View) (index offset : USize)
    (position : offset = 16 + index * view.stride) (previous : UInt64) : Bool :=
  if h : index < view.count then
    let key := view.keyInBounds index offset position h
    if previous >= key then false
    else view.validateFrom (index + 1) (offset + view.stride)
      (view.nextKeyOffset index offset position) key
  else true
termination_by view.count.toNat - index.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp h
  have step := addOne index view.count order
  omega

def View.validate (view : @& View) : Bool :=
  view.count == 0 || view.validateFrom 1 (16 + view.stride) (by rw [USize.one_mul]) (view.keyOrZero 0)

private theorem View.validateFrom_ordered (view : View) (i offset : USize)
    (position : offset = 16 + i * view.stride) (previous : UInt64)
    (accepted : view.validateFrom i offset position previous = true) :
    (∀ j, i ≤ j → j < view.count → previous < view.keyOrZero j) ∧
      (∀ j k, i ≤ j → j < k → k < view.count → view.keyOrZero j < view.keyOrZero k) := by
  rw [View.validateFrom] at accepted
  split at accepted
  next within =>
    dsimp only at accepted
    rw [view.keyInBounds_eq i offset position within] at accepted
    split at accepted
    next rejected => contradiction
    next increasing =>
      have step := addOne i view.count (USize.lt_iff_toNat_lt.mp within)
      have tail := view.validateFrom_ordered (i + 1) (offset + view.stride)
        (view.nextKeyOffset i offset position) (view.keyOrZero i) accepted
      have next_le (j : USize) (after : i ≤ j) (different : j ≠ i) : i + 1 ≤ j := by
        rw [USize.le_iff_toNat_le, step]
        have le := USize.le_iff_toNat_le.mp after
        have ne : j.toNat ≠ i.toNat := fun same => different (USize.toNat_inj.mp same)
        omega
      have prev_lt : previous < view.keyOrZero i := UInt64.not_le.mp increasing
      constructor
      · intro j after before
        by_cases same : j = i
        · simpa [same] using prev_lt
        · exact UInt64.lt_trans prev_lt (tail.1 j (next_le j after same) before)
      · intro j k after less before
        by_cases same : j = i
        · subst j
          exact tail.1 k (next_le k (USize.le_of_lt less) (Ne.symm (USize.ne_of_lt less))) before
        · exact tail.2 j k (next_le j after same) less before
  next exhausted =>
    simp only [USize.le_iff_toNat_le, USize.lt_iff_toNat_lt] at *
    constructor
    · intro j after before
      omega
    · intro j k after less before
      omega
termination_by view.count.toNat - i.toNat
decreasing_by
  have order : i.toNat < view.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
  omega

theorem View.validate_ordered (view : View) (accepted : view.validate = true)
    {i j : USize} (less : i < j) (before : j < view.count) :
    view.keyOrZero i < view.keyOrZero j := by
  have order := USize.lt_iff_toNat_lt.mp less
  have bound := USize.lt_iff_toNat_lt.mp before
  have zero : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
  have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
  have nonempty : view.count ≠ 0 := by
    intro empty
    rw [empty, zero] at bound
    omega
  have valid : view.validateFrom 1 (16 + view.stride) (by rw [USize.one_mul])
      (view.keyOrZero 0) = true := by
    simpa [View.validate, nonempty] using accepted
  have tail := view.validateFrom_ordered 1 (16 + view.stride) (by rw [USize.one_mul])
    (view.keyOrZero 0) valid
  by_cases initial : i = 0
  · subst i
    exact tail.1 j (USize.le_iff_toNat_le.mpr (by omega)) before
  · have nonzero : i.toNat ≠ 0 := by
      rw [← zero]
      exact fun same => initial (USize.toNat_inj.mp same)
    exact tail.2 i j (USize.le_iff_toNat_le.mpr (by omega)) less before

private theorem View.validateFrom_complete (view : View) (i offset : USize)
    (position : offset = 16 + i * view.stride) (previous : UInt64)
    (sorted : ∀ j k, j < k → k < view.count → view.keyOrZero j < view.keyOrZero k)
    (prev : i < view.count → previous < view.keyOrZero i) :
    view.validateFrom i offset position previous = true := by
  rw [View.validateFrom]
  by_cases within : i < view.count
  · simp only [dite_eq_left within]
    try dsimp only
    rw [view.keyInBounds_eq i offset position within, ite_eq_right (UInt64.not_le.mpr (prev within))]
    have index := USize.lt_iff_toNat_lt.mp within
    have step := addOne i view.count index
    exact view.validateFrom_complete (i + 1) (offset + view.stride)
      (view.nextKeyOffset i offset position) (view.keyOrZero i) sorted
      (fun hit => sorted i (i + 1) (USize.lt_iff_toNat_lt.mpr (by omega)) hit)
  · simp [within]
termination_by view.count.toNat - i.toNat
decreasing_by omega

theorem View.validate_complete (view : View)
    (sorted : ∀ j k, j < k → k < view.count → view.keyOrZero j < view.keyOrZero k) :
    view.validate = true := by
  unfold View.validate
  exact Bool.or_eq_true_iff.mpr (.inr (view.validateFrom_complete 1 (16 + view.stride)
    (by rw [USize.one_mul]) (view.keyOrZero 0) sorted (fun h => sorted 0 1 (USize.lt_iff_toNat_lt.mpr (by simp)) h)))

@[inline] private def View.checked (view : View) : Except String View :=
  if view.validate then .ok view else .error "keys must increase"

private theorem View.checked_spec {candidate view : View} (accepted : candidate.checked = .ok view) :
    candidate = view ∧ view.validate = true := by
  unfold View.checked at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, by assumption⟩
  · contradiction

def parseView (bytes : ByteArray) : Except String View :=
  if short : bytes.size < 16 then .error "short header"
  else
    let version := word bytes 8
    if version != 1 && version != 2 then .error "invalid header"
    else
      let payload := bytes.size - 16
      let count := payload / 16
      if valid : bytes.size < USize.size ∧ payload % 16 = 0 ∧ (word bytes 0).toNat = count then
        have size_eq : bytes.size = 16 + 16 * count := by
          have aligned := valid.2.1
          dsimp [payload, count] at *
          omega
        have count_exact : count.toUSize.toNat = count :=
          USize.toNat_ofNat_of_lt (by omega)
        have values_exact : (16 + count * 8).toUSize.toNat = 16 + count * 8 :=
          USize.toNat_ofNat_of_lt (by omega)
        let view := if version == 1 then
          View.mk bytes count.toUSize 16 24 valid.1 (by rwa [count_exact])
            (.inl ⟨USize.toNat_ofNat_of_lt_32 (by decide), USize.toNat_ofNat_of_lt_32 (by decide)⟩)
        else
          View.mk bytes count.toUSize 8 (16 + count * 8).toUSize valid.1 (by rwa [count_exact])
            (.inr ⟨USize.toNat_ofNat_of_lt_32 (by decide), by rw [count_exact, values_exact]; omega⟩)
        view.checked
      else .error "invalid length"

/-- Acceptance preserves the input bytes and certifies the header and selected layout. -/
theorem parseView_spec {bytes : ByteArray} {view : View} (accepted : parseView bytes = .ok view) :
    view.bytes = bytes ∧ (word bytes 0).toNat = view.count.toNat ∧ view.validate = true ∧
      ((word bytes 8 = 1 ∧ view.stride.toNat = 16 ∧ view.values.toNat = 24) ∨
        (word bytes 8 = 2 ∧ view.stride.toNat = 8 ∧
          view.values.toNat = 16 + 8 * view.count.toNat)) := by
  unfold parseView at accepted
  split at accepted
  · contradiction
  · dsimp only at accepted
    split at accepted
    · contradiction
    next known =>
      split at accepted
      next valid =>
        try dsimp only at accepted
        have count_exact : ((bytes.size - 16) / 16).toUSize.toNat = (bytes.size - 16) / 16 :=
          USize.toNat_ofNat_of_lt (by have fits := valid.1; omega)
        split at accepted
        next interleaved =>
          obtain ⟨same, sorted⟩ := View.checked_spec accepted
          simp only [beq_iff_eq] at interleaved
          rw [← same]
          simp [count_exact, valid.2.2, interleaved, ← same ▸ sorted]
        next columnar =>
          obtain ⟨same, sorted⟩ := View.checked_spec accepted
          have version : word bytes 8 = 2 := by
            simp only [beq_iff_eq] at columnar
            exact (by simpa [Bool.and_eq_true] using known : word bytes 8 ≠ 1 → word bytes 8 = 2) columnar
          have values_fit : 16 + (bytes.size - 16) / 16 * 8 < USize.size := by
            have fits := valid.1
            omega
          rw [← same]
          refine ⟨rfl, valid.2.2.trans count_exact.symm, same.symm ▸ sorted,
            .inr ⟨version, USize.toNat_ofNat_of_lt_32 (by decide), ?_⟩⟩
          change (16 + (bytes.size - 16) / 16 * 8).toUSize.toNat =
            16 + 8 * (((bytes.size - 16) / 16).toUSize.toNat)
          have value_exact : (16 + (bytes.size - 16) / 16 * 8).toUSize.toNat =
              16 + (bytes.size - 16) / 16 * 8 := USize.toNat_ofNat_of_lt values_fit
          rw [value_exact, count_exact]
          omega
      · contradiction

/-- A v1 block with a complete header and strictly ordered keys is accepted. -/
theorem parseView_v1_complete (bytes : ByteArray) (count : Nat)
    (size : bytes.size = 16 + 16 * count) (fits : bytes.size < USize.size)
    (version : word bytes 8 = 1) (countField : (word bytes 0).toNat = count)
    (ordered : ∀ view : View, view.bytes = bytes → view.count.toNat = count →
      view.stride.toNat = 16 → view.values.toNat = 24 → view.validate = true) :
    ∃ view, parseView bytes = .ok view ∧ view.count.toNat = count := by
  have short : ¬bytes.size < 16 := by omega
  have aligned : (bytes.size - 16) % 16 = 0 := by omega
  have derived : (bytes.size - 16) / 16 = count := by omega
  have valid : bytes.size < USize.size ∧ (bytes.size - 16) % 16 = 0 ∧
      (word bytes 0).toNat = (bytes.size - 16) / 16 :=
    ⟨fits, aligned, countField.trans derived.symm⟩
  have countExact : count.toUSize.toNat = count := USize.toNat_ofNat_of_lt (by omega)
  let view := View.mk bytes count.toUSize 16 24 fits (by rwa [countExact])
    (.inl ⟨USize.toNat_ofNat_of_lt_32 (by decide), USize.toNat_ofNat_of_lt_32 (by decide)⟩)
  refine ⟨view, ?_, countExact⟩
  have accepted := ordered view rfl countExact (USize.toNat_ofNat_of_lt_32 (by decide))
    (USize.toNat_ofNat_of_lt_32 (by decide))
  unfold parseView
  rw [dite_eq_right short]
  try dsimp only
  have validVersion : ¬(word bytes 8 != 1 && word bytes 8 != 2) = true := by simp [version]
  rw [ite_eq_right validVersion]
  try dsimp only
  rw [dite_eq_left valid]
  try dsimp only
  rw [ite_eq_left (show (word bytes 8 == 1) = true by simp [version])]
  have same : View.mk bytes ((bytes.size - 16) / 16).toUSize 16 24 fits
      (by
        rw [show ((bytes.size - 16) / 16).toUSize.toNat = count by rw [derived, countExact]]
        exact size)
      (.inl ⟨USize.toNat_ofNat_of_lt_32 (by decide), USize.toNat_ofNat_of_lt_32 (by decide)⟩) = view := by
    simp [view, derived]
  rw [same, View.checked, ite_eq_left accepted]

theorem midpoint_toNat (lo hi : USize) (h : lo < hi) :
    (lo + (hi - lo) / 2).toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
  have order := USize.lt_iff_toNat_lt.mp h
  have half : (2 : USize).toNat = 2 := USize.toNat_ofNat_of_lt_32 (by decide)
  have distance : ((hi - lo) / 2).toNat = (hi.toNat - lo.toNat) / 2 := by
    rw [USize.toNat_div, USize.toNat_sub_of_le _ _ (USize.le_of_lt h), half]
  have lim := hi.toNat_lt_size
  rw [addExact, distance]
  rw [distance]
  omega

@[specialize] def searchMachineLoop (readKey : USize → UInt64) (key : UInt64)
    (lo hi : USize) : USize :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    have order := USize.lt_iff_toNat_lt.mp h
    have midNat : mid.toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := midpoint_toNat lo hi h
    have below : mid.toNat < hi.toNat := by omega
    have next := addOne mid hi below
    if readKey mid < key then searchMachineLoop readKey key (mid + 1) hi
    else searchMachineLoop readKey key lo mid
  else lo
termination_by hi.toNat - lo.toNat
decreasing_by all_goals (dsimp [mid] at midNat next below; omega)

@[inline] def searchMachine (readKey : USize → UInt64) (key : UInt64) (count : USize) : USize :=
  searchMachineLoop readKey key 0 count

@[inline] def View.lowerBound (view : @& View) (key : UInt64) : USize :=
  searchMachine (fun i => view.keyOrZero i) key view.count

@[inline] def View.lookup (view : @& View) (key : UInt64) : Option UInt64 :=
  let i := view.lowerBound key
  if i < view.count && view.keyOrZero i == key then some (view.valueOrZero i) else none

/-- Internal scan worker. Use `scan` to bound the input to the view. -/
def View.scanFrom (view : @& View) (index hi : USize) (sum : UInt64) : UInt64 :=
  if _h : index < hi then
    view.scanFrom (index + 1) hi (sum + (view.keyOrZero index ^^^ view.valueOrZero index))
  else sum
termination_by hi.toNat - index.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp _h
  have step := addOne index hi order
  omega

@[inline] def View.scan (view : @& View) (lo hi : USize) : UInt64 :=
  view.scanFrom lo (min hi view.count) 0

end Alvoki.Opt
