import Std

namespace Alvoki.Compaction.Model

/-- An entry is ordered by key ascending and then by sequence descending.
The payload can be a decoded value or a reference into a packed run. -/
structure Entry (α : Type) where
  key : UInt64
  sequence : UInt64
  payload : α
  deriving Repr, DecidableEq

def Entry.mapPayload (f : α → β) (row : Entry α) : Entry β :=
  ⟨row.key, row.sequence, f row.payload⟩

def before (a b : Entry α) : Bool :=
  a.key < b.key || (a.key == b.key && a.sequence > b.sequence)

def sameVersion (a b : Entry α) : Bool :=
  a.key == b.key && a.sequence == b.sequence

@[simp] theorem before_iff : before a b = true ↔
    a.key < b.key ∨ a.key = b.key ∧ b.sequence < a.sequence := by
  simp [before]

@[simp] theorem sameVersion_iff : sameVersion a b = true ↔
    a.key = b.key ∧ a.sequence = b.sequence := by
  simp [sameVersion]

theorem before_trans {a b c : Entry α} (ab : before a b) (bc : before b c) :
    before a c := by
  rw [before_iff] at ab bc ⊢
  rcases ab with ab | ⟨keyAB, seqAB⟩ <;> rcases bc with bc | ⟨keyBC, seqBC⟩
  · exact Or.inl (UInt64.lt_trans ab bc)
  · exact Or.inl (keyBC ▸ ab)
  · exact Or.inl (keyAB.symm ▸ bc)
  · exact Or.inr ⟨keyAB.trans keyBC, UInt64.lt_trans seqBC seqAB⟩

theorem before_flip {a b : Entry α} (order : before a b = false)
    (distinct : sameVersion a b = false) : before b a := by
  apply before_iff.mpr
  have ordered := Bool.eq_false_iff.mp order
  change ¬ before a b = true at ordered
  rw [before_iff] at ordered
  have unequal := Bool.eq_false_iff.mp distinct
  change ¬ sameVersion a b = true at unequal
  rw [sameVersion_iff] at unequal
  have keyOrder : a.key < b.key ∨ a.key = b.key ∨ b.key < a.key := by simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]; omega
  rcases keyOrder with lt | eq | gt
  · exact False.elim (ordered (Or.inl lt))
  · refine Or.inr ⟨eq.symm, ?_⟩
    have seqOrder : a.sequence < b.sequence ∨ a.sequence = b.sequence ∨
        b.sequence < a.sequence := by simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]; omega
    rcases seqOrder with lt | eqSeq | gt
    · exact lt
    · exact False.elim (unequal ⟨eq, eqSeq⟩)
    · exact False.elim (ordered (Or.inr ⟨eq, gt⟩))
  · exact Or.inl gt

def Ordered (rows : List (Entry α)) : Prop :=
  rows.Pairwise fun a b => before a b

/-- Merge two ordered histories. The right history takes precedence on an exact tie. -/
def union (left right : List (Entry α)) : List (Entry α) :=
  match left, right with
  | [], rows | rows, [] => rows
  | a :: as, b :: bs =>
    if before a b then a :: union as (b :: bs)
    else if sameVersion a b then b :: union as bs
    else b :: union (a :: as) bs
termination_by left.length + right.length

@[simp] theorem union_nil_left (rows : List (Entry α)) : union [] rows = rows :=
  union.eq_1 rows

@[simp] theorem union_nil_right (rows : List (Entry α)) : union rows [] = rows := by
  cases rows <;> simp [union]

theorem union_map (f : α → β) (left right : List (Entry α)) :
    union (left.map (Entry.mapPayload f)) (right.map (Entry.mapPayload f)) =
      (union left right).map (Entry.mapPayload f) := by
  induction left, right using union.induct with
  | case1 rows => simp
  | case2 rows _ => simp
  | case3 a as b bs order ih =>
    have h : before (a.mapPayload f) (b.mapPayload f) = true := order
    simp only [List.map_cons] at ih ⊢
    rw [union.eq_3, ite_eq_left h, union.eq_3, ite_eq_left order, List.map_cons, ih]
  | case4 a as b bs order tie ih =>
    have h : ¬before (a.mapPayload f) (b.mapPayload f) = true := order
    have t : sameVersion (a.mapPayload f) (b.mapPayload f) = true := tie
    simp only [List.map_cons]
    rw [union.eq_3, ite_eq_right h, ite_eq_left t, union.eq_3, ite_eq_right order,
      ite_eq_left tie, List.map_cons, ih]
  | case5 a as b bs order tie ih =>
    have h : ¬before (a.mapPayload f) (b.mapPayload f) = true := order
    have t : ¬sameVersion (a.mapPayload f) (b.mapPayload f) = true := tie
    simp only [List.map_cons] at ih ⊢
    rw [union.eq_3, ite_eq_right h, ite_eq_right t, union.eq_3, ite_eq_right order,
      ite_eq_right tie, List.map_cons, ih]

theorem mem_union {row : Entry α} {left right : List (Entry α)} (h : row ∈ union left right) :
    row ∈ left ∨ row ∈ right := by
  induction left, right using union.induct with
  | case1 rows => simpa [union] using h
  | case2 rows _ => simpa [union] using h
  | case3 a as b bs order ih =>
    rw [union.eq_3, ite_eq_left order, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl List.mem_cons_self
    · exact (ih h).imp (List.mem_cons_of_mem _) id
  | case4 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_left tie, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr List.mem_cons_self
    · exact (ih h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
  | case5 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_right tie, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr List.mem_cons_self
    · exact (ih h).imp id (List.mem_cons_of_mem _)

theorem union_ordered {left right : List (Entry α)} (leftOrder : Ordered left)
    (rightOrder : Ordered right) : Ordered (union left right) := by
  induction left, right using union.induct with
  | case1 rows => simpa [union] using rightOrder
  | case2 rows _ => simpa [union] using leftOrder
  | case3 a as b bs order ih =>
    rw [union.eq_3, ite_eq_left order]
    exact List.pairwise_cons.mpr ⟨fun row h => (mem_union h).elim
      (List.rel_of_pairwise_cons leftOrder)
      (fun br => (List.mem_cons.mp br).elim (fun e => e.symm ▸ order)
        (fun mem => before_trans order (List.rel_of_pairwise_cons rightOrder mem))),
      ih (List.Pairwise.of_cons leftOrder) rightOrder⟩
  | case4 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_left tie]
    have ⟨key, seq⟩ := sameVersion_iff.mp tie
    exact List.pairwise_cons.mpr ⟨fun row h => (mem_union h).elim
      (fun mem => by
        have h := before_iff.mp (List.rel_of_pairwise_cons leftOrder mem)
        exact before_iff.mpr (by simpa [key, seq] using h))
      (List.rel_of_pairwise_cons rightOrder),
      ih (List.Pairwise.of_cons leftOrder) (List.Pairwise.of_cons rightOrder)⟩
  | case5 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_right tie]
    have ba := before_flip (Bool.eq_false_iff.mpr order) (Bool.eq_false_iff.mpr tie)
    exact List.pairwise_cons.mpr ⟨fun row h => (mem_union h).elim
      (fun ar => (List.mem_cons.mp ar).elim (fun e => e.symm ▸ ba)
        (fun mem => before_trans ba (List.rel_of_pairwise_cons leftOrder mem)))
      (List.rel_of_pairwise_cons rightOrder),
      ih leftOrder (List.Pairwise.of_cons rightOrder)⟩

theorem versions_unique {rows : List (Entry α)} (h : Ordered rows) :
    List.Nodup (rows.map fun (row : Entry α) => (row.key, row.sequence)) := by
  rw [List.Nodup, List.pairwise_map]
  apply h.imp
  intro a b order same
  have keys : a.key = b.key := congrArg Prod.fst same
  have sequences : a.sequence = b.sequence := congrArg Prod.snd same
  simpa [keys, sequences] using before_iff.mp order

/-- The first eligible version in a history sorted by `before`. -/
def eligible (key snapshot : UInt64) (row : Entry α) : Bool :=
  row.key == key && row.sequence ≤ snapshot

def winner (rows : List (Entry α)) (key snapshot : UInt64) : Option (Entry α) :=
  rows.find? (eligible key snapshot)

theorem winner_latest {rows : List (Entry α)} (ordered : Ordered rows) {key snapshot : UInt64}
    {chosen candidate : Entry α} (found : winner rows key snapshot = some chosen)
    (mem : candidate ∈ rows) (visible : eligible key snapshot candidate) :
    candidate.sequence ≤ chosen.sequence := by
  have ⟨chosenEligible, prefixRows, suffix, splitRows, beforeWinner⟩ :=
    List.find?_eq_some_iff_append.mp found
  rw [splitRows] at mem ordered
  rcases List.mem_append.mp mem with before | after
  · have rejected := beforeWinner _ before
    simp [visible] at rejected
  · rcases List.mem_cons.mp after with rfl | later
    · exact UInt64.le_refl _
    · have suffixOrder := (List.pairwise_append.mp ordered).2.1
      have order := before_iff.mp (List.rel_of_pairwise_cons suffixOrder later)
      have chosenKey : chosen.key = key := (by simpa [eligible] using chosenEligible :
        chosen.key = key ∧ chosen.sequence ≤ snapshot).1
      have candidateKey : candidate.key = key := (by simpa [eligible] using visible :
        candidate.key = key ∧ candidate.sequence ≤ snapshot).1
      have older : candidate.sequence < chosen.sequence := by simpa [chosenKey, candidateKey] using order
      exact UInt64.le_of_lt older

/-- The option inside the row distinguishes a tombstone from a put.
The outer option is resolved before projecting the value. -/
def read (rows : List (Entry (Option α))) (key snapshot : UInt64) : Option α :=
  (winner rows key snapshot).bind Entry.payload

/-- Choose the newer candidate, using the right candidate on an equal sequence.
Both candidates are for the same queried key when supplied by `winner`. -/
def newest (left right : Option (Entry α)) : Option (Entry α) :=
  match left, right with
  | none, row | row, none => row
  | some a, some b => if b.sequence < a.sequence then some a else some b

private theorem winner_before (ordered : Ordered (head :: rows))
    (order : before row head) (visible : eligible key snapshot row)
    (found : winner (head :: rows) key snapshot = some candidate) :
    candidate.sequence < row.sequence := by
  have ⟨rowKey, _⟩ : row.key = key ∧ row.sequence ≤ snapshot := by simpa [eligible] using visible
  have candidateVisible := List.find?_some found
  have ⟨candidateKey, _⟩ : candidate.key = key ∧ candidate.sequence ≤ snapshot := by
    simpa [eligible] using candidateVisible
  have hc := List.mem_of_find?_eq_some found
  have earlier : before row candidate := (List.mem_cons.mp hc).elim
    (fun e => e.symm ▸ order)
    (fun mem => before_trans order (List.rel_of_pairwise_cons ordered mem))
  simpa [rowKey, candidateKey] using before_iff.mp earlier

theorem winner_union {left right : List (Entry α)} (leftOrder : Ordered left)
    (rightOrder : Ordered right) (key snapshot : UInt64) :
    winner (union left right) key snapshot =
      newest (winner left key snapshot) (winner right key snapshot) := by
  induction left, right using union.induct with
  | case1 rows => simp [winner, newest]
  | case2 rows nonempty =>
    rw [union.eq_2 _ nonempty]
    cases winner rows key snapshot <;> rfl
  | case3 a as b bs order ih =>
    rw [union.eq_3, ite_eq_left order]
    by_cases visible : eligible key snapshot a = true
    · have chosen : winner (a :: as) key snapshot = some a := by simp [winner, visible]
      have out : winner (a :: union as (b :: bs)) key snapshot = some a := by
        simp [winner, visible]
      rw [chosen, out]
      cases found : winner (b :: bs) key snapshot with
      | none => rfl
      | some candidate => simp [newest, winner_before rightOrder order visible found]
    · simpa [winner, visible] using ih (List.Pairwise.of_cons leftOrder) rightOrder
  | case4 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_left tie]
    have ⟨sameKey, sameSeq⟩ := sameVersion_iff.mp tie
    have sameEligibility : eligible key snapshot a = eligible key snapshot b := by
      simp [eligible, sameKey, sameSeq]
    by_cases visible : eligible key snapshot b = true
    · simp [winner, newest, sameEligibility, visible, sameSeq]
    · simpa [winner, sameEligibility, visible] using
        ih (List.Pairwise.of_cons leftOrder) (List.Pairwise.of_cons rightOrder)
  | case5 a as b bs order tie ih =>
    rw [union.eq_3, ite_eq_right order, ite_eq_right tie]
    by_cases visible : eligible key snapshot b = true
    · have chosen : winner (b :: bs) key snapshot = some b := by simp [winner, visible]
      have out : winner (b :: union (a :: as) bs) key snapshot = some b := by
        simp [winner, visible]
      rw [chosen, out]
      cases found : winner (a :: as) key snapshot with
      | none => rfl
      | some candidate =>
        have ba := before_flip (Bool.eq_false_iff.mpr order) (Bool.eq_false_iff.mpr tie)
        have earlier := winner_before leftOrder ba visible found
        simp [newest, UInt64.not_lt.mpr (UInt64.le_of_lt earlier)]
    · simpa [winner, visible] using ih leftOrder (List.Pairwise.of_cons rightOrder)

def retainFrom (floor previous : UInt64) (covered : Bool) :
    List (Entry α) → List (Entry α)
  | [] => []
  | row :: rows =>
    let rest := retainFrom floor row.key (row.sequence ≤ floor) rows
    if row.key != previous || !covered then row :: rest else rest

def retain (rows : List (Entry α)) (floor : UInt64) : List (Entry α) :=
  retainFrom floor 0 false rows

theorem retain_map (f : α → β) (rows : List (Entry α)) (floor : UInt64) :
    retain (rows.map (Entry.mapPayload f)) floor = (retain rows floor).map (Entry.mapPayload f) := by
  unfold retain
  generalize (0 : UInt64) = previous
  generalize false = covered
  induction rows generalizing previous covered with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, retainFrom, Entry.mapPayload]
    split
    · simp only [List.map_cons, ih, Entry.mapPayload]
    · exact ih ..

theorem retainFrom_sublist (rows : List (Entry α)) (floor previous : UInt64) (covered : Bool) :
    List.Sublist (retainFrom floor previous covered rows) rows := by
  induction rows generalizing previous covered with
  | nil => exact .slnil
  | cons row rows ih =>
    simp only [retainFrom]
    split
    · exact .cons_cons _ (ih ..)
    · exact .cons _ (ih ..)

theorem retain_ordered {rows : List (Entry α)} (ordered : Ordered rows) (floor : UInt64) :
    Ordered (retain rows floor) :=
  ordered.sublist (retainFrom_sublist rows floor 0 false)

def hasKey (key : UInt64) (row : Entry α) : Bool := row.key == key

def above (key floor : UInt64) (row : Entry α) : Bool :=
  hasKey key row && floor < row.sequence

private theorem older_or_after (order : before a b) (query : a.key = key)
    (matching : b.key = key) : b.sequence < a.sequence := by
  simpa [query, matching] using before_iff.mp order

private theorem filter_retained_after_floor (rows : List (Entry α)) (head : Entry α)
    (floor : UInt64) (covered : head.sequence ≤ floor) (ordered : Ordered (head :: rows)) :
    (retainFrom floor head.key true rows).filter (hasKey head.key) = [] := by
  induction rows generalizing head with
  | nil => rfl
  | cons row rows ih =>
    have hr := List.rel_of_pairwise_cons ordered (List.mem_cons_self (a := row))
    have tailOrder := List.Pairwise.of_cons ordered
    by_cases key : row.key = head.key
    · have old := UInt64.le_trans (UInt64.le_of_lt (older_or_after hr rfl key)) covered
      have rest := ih row old tailOrder
      simpa [retainFrom, key, old] using rest
    · have after : head.key < row.key := by simpa [Ne.symm key] using before_iff.mp hr
      have notMatching (candidate : Entry α) (mem : candidate ∈ rows) :
          ¬ hasKey head.key candidate = true := by
        have h := before_iff.mp (List.rel_of_pairwise_cons tailOrder mem)
        have ge : row.key ≤ candidate.key := h.elim UInt64.le_of_lt
          (fun eq => eq.1 ▸ UInt64.le_refl _)
        have lt := UInt64.lt_of_lt_of_le after ge
        simp [hasKey, Ne.symm (UInt64.ne_of_lt lt)]
      have rest : (retainFrom floor row.key (row.sequence ≤ floor) rows).filter
          (hasKey head.key) = [] := List.filter_eq_nil_iff.mpr fun candidate hb =>
        notMatching candidate ((retainFrom_sublist rows floor _ _).subset hb)
      simp [retainFrom, hasKey, key] at rest ⊢
      exact rest

private theorem retain_key_from {rows : List (Entry α)} (ordered : Ordered rows)
    (key floor previous : UInt64) (covered : Bool)
    (available : covered = false ∨ previous ≠ key) :
    (retainFrom floor previous covered rows).filter (hasKey key) =
      rows.filter (above key floor) ++ (winner rows key floor).toList := by
  induction rows generalizing previous covered with
  | nil => rfl
  | cons row rows ih =>
    have tailOrder := List.Pairwise.of_cons ordered
    by_cases matching : row.key = key
    · have keep : (row.key != previous || !covered) = true := by
        rcases available with h | h
        · simp [h]
        · simp [matching, Ne.symm h]
      by_cases old : row.sequence ≤ floor
      · have rest := filter_retained_after_floor rows row floor old ordered
        have noneAbove : rows.filter (above key floor) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate mem
          by_cases candidateMatches : candidate.key = key
          · have seq := older_or_after (List.rel_of_pairwise_cons ordered mem)
              matching candidateMatches
            have le := UInt64.le_trans (UInt64.le_of_lt seq) old
            simp [above, hasKey, candidateMatches, UInt64.not_lt.mpr le]
          · simp [above, hasKey, candidateMatches]
        rw [retainFrom, ite_eq_left keep]
        simpa [above, hasKey, winner, eligible, matching, old, UInt64.not_lt.mpr old,
          noneAbove] using rest
      · have newer := UInt64.not_le.mp old
        have rest := ih tailOrder row.key (decide (row.sequence ≤ floor))
          (Or.inl (by simp [old]))
        rw [retainFrom, ite_eq_left keep]
        simp [above, hasKey, winner, eligible, matching, old, newer] at rest ⊢
        exact rest
    · have rest := ih tailOrder row.key (decide (row.sequence ≤ floor)) (Or.inr matching)
      rw [retainFrom]
      split <;> simpa [above, hasKey, winner, eligible, matching] using rest

/-- For each key retain every version newer than the floor and then the first
entry at or below it, including a tombstone. -/
theorem retain_key {rows : List (Entry α)} (ordered : Ordered rows) (key floor : UInt64) :
    (retain rows floor).filter (hasKey key) =
      rows.filter (above key floor) ++ (winner rows key floor).toList :=
  retain_key_from ordered key floor 0 false (Or.inl rfl)

theorem winner_retainFrom (rows : List (Entry α)) {floor snapshot key previous : UInt64}
    {covered : Bool} (live : floor ≤ snapshot) (available : covered = false ∨ previous ≠ key) :
    winner (retainFrom floor previous covered rows) key snapshot = winner rows key snapshot := by
  induction rows generalizing previous covered with
  | nil => rfl
  | cons row rows ih =>
    by_cases usable : eligible key snapshot row = true
    · have relevant : row.key = key := by
        exact (by simpa [eligible] using usable : row.key = key ∧ row.sequence ≤ snapshot).1
      have keep : (row.key != previous || !covered) = true := by
        rcases available with h | h
        · simp [h]
        · simp [relevant, Ne.symm h]
      simp [retainFrom, keep, winner, usable]
    · have step : decide (row.sequence ≤ floor) = false ∨ row.key ≠ key := by
        by_cases matching : row.key = key
        · left
          simpa [eligible, matching] using
            (show ¬ row.sequence ≤ floor from fun atFloor =>
              usable (by simp [eligible, matching, UInt64.le_trans atFloor live]))
        · exact Or.inr matching
      have rest := ih (previous := row.key) (covered := decide (row.sequence ≤ floor)) step
      rw [retainFrom]
      split <;> simpa [winner, usable] using rest

theorem winner_retain (rows : List (Entry α)) (key : UInt64) {floor snapshot : UInt64}
    (live : floor ≤ snapshot) :
    winner (retain rows floor) key snapshot = winner rows key snapshot :=
  winner_retainFrom rows live (Or.inl rfl)

theorem read_retain (rows : List (Entry (Option α))) (key : UInt64) {floor snapshot : UInt64}
    (live : floor ≤ snapshot) : read (retain rows floor) key snapshot = read rows key snapshot := by
  simp [read, winner_retain rows key live]

theorem winner_advanceFloor (rows : List (Entry α)) (key : UInt64) {floor next snapshot : UInt64}
    (advance : floor ≤ next) (live : next ≤ snapshot) :
    winner (retain (retain rows floor) next) key snapshot = winner rows key snapshot := by
  rw [winner_retain _ _ live, winner_retain _ _ (UInt64.le_trans advance live)]

/-- The compacted run retains its original precedence over the older context.
The equality preserves the winning tombstone before projecting the value. -/
theorem winner_retain_in_context {older rows : List (Entry α)} (olderOrder : Ordered older)
    (rowOrder : Ordered rows) (key : UInt64) {floor snapshot : UInt64} (live : floor ≤ snapshot) :
    winner (union older (retain rows floor)) key snapshot =
      winner (union older rows) key snapshot := by
  rw [winner_union olderOrder (retain_ordered rowOrder floor) key snapshot,
    winner_union olderOrder rowOrder key snapshot, winner_retain rows key live]

/-- Entries returned by a scan. The predicate excludes tombstone payloads. -/
def visibleRows (rows : List (Entry α)) (snapshot : UInt64) (put : α → Bool) : List (Entry α) :=
  (retain rows snapshot).filter fun row => row.sequence ≤ snapshot && put row.payload

theorem visibleRows_ordered {rows : List (Entry α)} (ordered : Ordered rows)
    (snapshot : UInt64) (put : α → Bool) : Ordered (visibleRows rows snapshot put) :=
  (retain_ordered ordered snapshot).filter _

theorem visibleRows_key {rows : List (Entry α)} (ordered : Ordered rows)
    (key snapshot : UInt64) (put : α → Bool) :
    (visibleRows rows snapshot put).filter (hasKey key) =
      ((winner rows key snapshot).filter (fun row => put row.payload)).toList := by
  let included : Entry α → Bool := fun row => row.sequence ≤ snapshot && put row.payload
  change ((retain rows snapshot).filter included).filter (hasKey key) = _
  rw [List.filter_filter, show (fun row => hasKey key row && included row) =
    (fun row => included row && hasKey key row) by funext row; exact Bool.and_comm _ _,
    ← List.filter_filter, retain_key ordered, List.filter_append]
  have noAbove : (List.filter (above key snapshot) rows).filter included = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row mem
    have newer : snapshot < row.sequence := by
      have h := (List.mem_filter.mp mem).2
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    simp [included, UInt64.not_le.mpr newer]
  rw [noAbove, List.nil_append]
  cases found : winner rows key snapshot with
  | none => rfl
  | some row =>
    have h := List.find?_some found
    have visible : row.sequence ≤ snapshot := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    by_cases keep : put row.payload = true <;> simp [included, visible, Option.filter, keep]

theorem mem_visibleRows {rows : List (Entry α)} {row : Entry α} (ordered : Ordered rows)
    (snapshot : UInt64) (put : α → Bool) :
    row ∈ visibleRows rows snapshot put ↔
      winner rows row.key snapshot = some row ∧ put row.payload = true := by
  have w := visibleRows_key ordered row.key snapshot put
  constructor
  · intro mem
    have h : row ∈ (visibleRows rows snapshot put).filter (hasKey row.key) :=
      List.mem_filter.mpr ⟨mem, by simp [hasKey]⟩
    rw [w] at h
    cases found : winner rows row.key snapshot with
    | none => simp [found] at h
    | some other =>
      by_cases includeOther : put other.payload = true
      · have same : row = other := by simpa [found, Option.filter, includeOther] using h
        subst other
        exact ⟨rfl, includeOther⟩
      · simp [found, Option.filter, includeOther] at h
  · rintro ⟨found, h⟩
    have mem : row ∈ (visibleRows rows snapshot put).filter (hasKey row.key) := by
      rw [w]
      simp [found, Option.filter, h]
    exact (List.mem_filter.mp mem).1

theorem visibleRows_key_order {rows : List (Entry α)} (ordered : Ordered rows)
    (snapshot : UInt64) (put : α → Bool) :
    (visibleRows rows snapshot put).Pairwise (fun a b => a.key < b.key) := by
  rw [List.pairwise_iff_forall_sublist]
  intro a b pair
  have order := List.pairwise_iff_forall_sublist.mp (visibleRows_ordered ordered snapshot put) pair
  rcases before_iff.mp order with lt | ⟨same, older⟩
  · exact lt
  · have ha := (mem_visibleRows ordered snapshot put).mp (pair.subset (by simp : a ∈ [a,b]))
    have hb := (mem_visibleRows ordered snapshot put).mp (pair.subset (by simp : b ∈ [a,b]))
    rw [same, hb.1] at ha
    have eq := Option.some.inj ha.1
    subst b
    exact False.elim ((UInt64.lt_irrefl _) older)

theorem visibleRows_congr_visible {left right : List (Entry α)} (lo : Ordered left) (ro : Ordered right)
    (snapshot : UInt64) (put : α → Bool)
    (same : ∀ key, (winner left key snapshot).filter (fun row => put row.payload) =
      (winner right key snapshot).filter (fun row => put row.payload)) :
    visibleRows left snapshot put = visibleRows right snapshot put := by
  have leftKeys := visibleRows_key_order lo snapshot put
  have rightKeys := visibleRows_key_order ro snapshot put
  have different {a b : Entry α} (h : a.key < b.key) : a ≠ b :=
    fun eq => (UInt64.lt_irrefl _) (eq ▸ h)
  have permutation := (List.perm_ext_iff_of_nodup (leftKeys.imp different)
    (rightKeys.imp different)).mpr (fun row => by
      rw [mem_visibleRows lo, mem_visibleRows ro]
      have shows (found : Option (Entry α)) :
          (found.filter fun r => put r.payload) = some row ↔
            found = some row ∧ put row.payload = true := Option.filter_eq_some_iff
      rw [← shows (winner left row.key snapshot), ← shows (winner right row.key snapshot), same])
  apply permutation.eq_of_pairwise _ leftKeys rightKeys
  intro a b _ _ lt gt
  exact False.elim ((UInt64.lt_irrefl _) (UInt64.lt_trans lt gt))

theorem visibleRows_congr {left right : List (Entry α)} (lo : Ordered left) (ro : Ordered right)
    (snapshot : UInt64) (put : α → Bool)
    (same : ∀ key, winner left key snapshot = winner right key snapshot) :
    visibleRows left snapshot put = visibleRows right snapshot put :=
  visibleRows_congr_visible lo ro snapshot put (fun key => congrArg (Option.filter (fun row => put row.payload)) (same key))

end Alvoki.Compaction.Model
