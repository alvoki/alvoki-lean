import Alvoki.Experiments.SortedRun.Merge

namespace SortedRun

def Ordered [LT key] (keyOf : row → key) (rows : List row) : Prop :=
  rows.Pairwise (fun a b => keyOf a < keyOf b)

/-- Finite specification. This list is never constructed by the producer. -/
def merge [LT key] [DecidableLT key] (keyOf : row → key) (newer older : List row) : List row :=
  match newer, older with
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs =>
    if keyOf a < keyOf b then a :: merge keyOf as (b :: bs)
    else if keyOf b < keyOf a then b :: merge keyOf (a :: as) bs
    else a :: merge keyOf as bs
termination_by newer.length + older.length

@[simp] theorem merge_nil [LT key] [DecidableLT key] (keyOf : row → key) (rows : List row) :
    merge keyOf rows [] = rows := by cases rows <;> simp [merge]

theorem mem_merge [LT key] [DecidableLT key] (keyOf : row → key)
    {newer older : List row} {entry : row} (member : entry ∈ merge keyOf newer older) :
    entry ∈ newer ∨ entry ∈ older := by
  cases newer with
  | nil => exact Or.inr (by simpa [merge] using member)
  | cons a as =>
    cases older with
    | nil => exact Or.inl (by simpa [merge] using member)
    | cons b bs =>
      rw [merge] at member
      split at member
      · rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl (by simp)
        · exact (mem_merge keyOf member).imp (List.mem_cons_of_mem _) id
      · split at member
        · rcases List.mem_cons.mp member with rfl | member
          · exact Or.inr (by simp)
          · exact (mem_merge keyOf member).imp id (List.mem_cons_of_mem _)
        · rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl (by simp)
          · exact (mem_merge keyOf member).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
termination_by newer.length + older.length

section Order

variable [LT key] [DecidableLT key] [Trans (α := key) (· < ·) (· < ·) (· < ·)]
  [Std.Trichotomous (α := key) (· < ·)] [Std.Irrefl (α := key) (· < ·)]

omit [DecidableLT key] [Trans (α := key) (· < ·) (· < ·) (· < ·)]
  [Std.Irrefl (α := key) (· < ·)] in
private theorem tie {a b : key} (left : ¬ a < b) (right : ¬ b < a) : a = b :=
  (Std.lt_trichotomy a b).resolve_left left |>.resolve_right right

omit [DecidableLT key] [Std.Trichotomous (α := key) (· < ·)]
  [Std.Irrefl (α := key) (· < ·)] in
private theorem before_cons {keyOf : row → key} {x y : row} {ys : List row}
    (before : keyOf x < keyOf y) (later : Ordered keyOf (y :: ys)) :
    ∀ z ∈ y :: ys, keyOf x < keyOf z := by
  intro z member
  rcases List.mem_cons.mp member with rfl | tail
  · exact before
  · exact Std.lt_trans before ((List.pairwise_cons.mp later).1 z tail)

omit [Std.Irrefl (α := key) (· < ·)] in
theorem merge_ordered (keyOf : row → key) {newer older : List row}
    (left : Ordered keyOf newer) (right : Ordered keyOf older) :
    Ordered keyOf (merge keyOf newer older) := by
  cases newer with
  | nil => simpa [merge] using right
  | cons a as =>
    cases older with
    | nil => simpa [merge] using left
    | cons b bs =>
      have ⟨aBefore, aTail⟩ := List.pairwise_cons.mp left
      have ⟨bBefore, bTail⟩ := List.pairwise_cons.mp right
      rw [merge]
      split
      · rename_i lt
        exact List.pairwise_cons.mpr ⟨fun _ member =>
          (mem_merge keyOf member).elim (aBefore _) (before_cons lt right _),
          merge_ordered keyOf aTail right⟩
      · rename_i notLt
        split
        · rename_i gt
          exact List.pairwise_cons.mpr ⟨fun _ member =>
            (mem_merge keyOf member).elim (before_cons gt left _) (bBefore _),
            merge_ordered keyOf left bTail⟩
        · rename_i notGt
          exact List.pairwise_cons.mpr ⟨fun _ member =>
            (mem_merge keyOf member).elim (aBefore _) (fun inRight =>
              (tie notLt notGt).symm ▸ bBefore _ inRight),
            merge_ordered keyOf aTail bTail⟩
termination_by newer.length + older.length

/-- Lookup returns the complete row, so the equation also compares the value. -/
def lookup [DecidableEq key] (keyOf : row → key) (rows : List row) (query : key) : Option row :=
  rows.find? (fun row => decide (keyOf row = query))

omit [DecidableLT key] [Trans (α := key) (· < ·) (· < ·) (· < ·)]
  [Std.Trichotomous (α := key) (· < ·)] in
private theorem lookup_below [DecidableEq key] (keyOf : row → key) (rows : List row)
    (query : key) (below : ∀ r ∈ rows, query < keyOf r) : lookup keyOf rows query = none := by
  apply List.find?_eq_none.mpr
  intro r member
  have different : keyOf r ≠ query := fun eq => Std.lt_irrefl (eq ▸ below r member)
  simp [different]

theorem merge_lookup [DecidableEq key] (keyOf : row → key) {newer older : List row}
    (left : Ordered keyOf newer) (right : Ordered keyOf older) (query : key) :
    lookup keyOf (merge keyOf newer older) query =
      (lookup keyOf newer query).or (lookup keyOf older query) := by
  cases newer with
  | nil => simp [merge, lookup]
  | cons a as =>
    cases older with
    | nil => simp [lookup]
    | cons b bs =>
      have aTail := (List.pairwise_cons.mp left).2
      have bTail := (List.pairwise_cons.mp right).2
      rw [merge]
      split
      · by_cases hit : keyOf a = query
        · simp [lookup, hit]
        · simpa [lookup, hit] using merge_lookup keyOf aTail right query
      · rename_i notLt
        split
        · rename_i gt
          by_cases hit : keyOf b = query
          · have absent := lookup_below keyOf (a :: as) query (hit ▸ before_cons gt left)
            simp [lookup, hit, show (a :: as).find? _ = none from absent]
          · simpa [lookup, hit] using merge_lookup keyOf left bTail query
        · rename_i notGt
          have same := tie notLt notGt
          by_cases hit : keyOf a = query
          · simp [lookup, hit]
          · have miss : keyOf b ≠ query := same ▸ hit
            simpa [lookup, hit, miss] using merge_lookup keyOf aTail bTail query
termination_by newer.length + older.length

omit [DecidableLT key] [Trans (α := key) (· < ·) (· < ·) (· < ·)]
  [Std.Trichotomous (α := key) (· < ·)] in
theorem Ordered.unique_keys {keyOf : row → key} {rows : List row}
    (ordered : Ordered keyOf rows) : (rows.map keyOf).Nodup := by
  unfold Ordered at ordered
  rw [List.Nodup, List.pairwise_map]
  apply ordered.imp
  intro a b lt eq
  exact Std.lt_irrefl (eq ▸ lt)

theorem merge_keys [DecidableEq key] (keyOf : row → key) {newer older : List row}
    (left : Ordered keyOf newer) (right : Ordered keyOf older) (query : key) :
    query ∈ (merge keyOf newer older).map keyOf ↔
      query ∈ newer.map keyOf ∨ query ∈ older.map keyOf := by
  have found (rows : List row) :
      (lookup keyOf rows query).isSome = true ↔ query ∈ rows.map keyOf := by
    simp [lookup, List.find?_isSome, List.mem_map, and_comm]
  rw [← found, ← found, ← found, merge_lookup keyOf left right]
  cases lookup keyOf newer query <;> cases lookup keyOf older query <;> simp [Option.or]

end Order

/-- Logical suffix of a frontier. Buffered EOF represents the empty suffix. -/
def Front.remaining (suffix : cursor → List row) : Front cursor row → List row
  | .unread pos => suffix pos
  | .buffered none => []
  | .buffered (some (row, pos)) => row :: suffix pos

def Frontier.remaining [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : left → List row) (older : right → List row) (front : Frontier left right row) :
    List row :=
  merge keyOf (front.newer.remaining newer) (front.older.remaining older)

/-- Model the real slot reads and writes alongside arbitrary source effects. -/
abbrev EffectState (left right row σ : Type) := Frontier left right row × σ

def effectSlot : Slot (EStateM ε (EffectState left right row σ)) (Frontier left right row) where
  get := fun state => .ok state.1 state
  set front := fun state => .ok () (front, state.2)

def liftEffect (action : EStateM ε σ α) : EStateM ε (front × σ) α := fun state =>
  match action state.2 with
  | .ok item reached => .ok item (state.1, reached)
  | .error error reached => .error error (state.1, reached)

def liftPull (read : Pull (EStateM ε σ) cursor row) :
    Pull (EStateM ε (front × σ)) cursor row :=
  fun pos => liftEffect (read pos)

theorem liftEffect_ok {action : EStateM ε σ α} {before after : front × σ}
    (ran : liftEffect action before = .ok value after) :
    after.1 = before.1 ∧ action before.2 = .ok value after.2 := by
  unfold liftEffect at ran
  split at ran
  · rename_i done
    cases ran
    exact ⟨rfl, done⟩
  · cases ran

def Pull.Exact (read : Pull (EStateM ε σ) cursor row) (suffix : cursor → List row) : Prop :=
  ∀ pos start item reached, read pos start = .ok item reached →
    (Front.buffered item).remaining suffix = suffix pos

theorem fill_exact {read : Pull (EStateM ε σ) cursor row}
    {suffix : cursor → List row} (exact : read.Exact suffix) {front : Front cursor row}
    {start reached : σ} {item : Option (row × cursor)}
    (ran : front.fill read start = .ok item reached) :
    (Front.buffered item).remaining suffix = front.remaining suffix := by
  cases front with
  | unread cursor => exact exact cursor start item reached ran
  | buffered item =>
    cases ran
    rfl

/-- Errors retain the underlying state and each previously buffered head.
This equation is for the callback executed by the consumer. -/
theorem next_effect [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : Pull (EStateM ε σ) left row) (older : Pull (EStateM ε σ) right row)
    (front : Frontier left right row) (start : σ) :
    next keyOf (liftPull newer) (liftPull older) effectSlot (front, start) =
      match front.newer.fill newer start with
      | .error error reached => .error error (front, reached)
      | .ok a middle =>
        match front.older.fill older middle with
        | .error error reached => .error error ({ front with newer := .buffered a }, reached)
        | .ok b reached =>
          let (item, after) := choose keyOf a b
          .ok item (after, reached) := by
  rcases front with ⟨a, b⟩
  cases a with
  | unread cursorA =>
    cases first : newer cursorA start with
    | error => cases b <;> simp [next, effectSlot, Front.fill, Bind.bind, EStateM.bind, liftPull, liftEffect, first]
    | ok itemA middle =>
      cases b with
      | unread cursorB =>
        cases second : older cursorB middle <;>
          simp [next, effectSlot, Front.fill, Bind.bind, EStateM.bind, liftPull, liftEffect, first, second,
            Pure.pure, EStateM.pure]
      | buffered itemB =>
        simp [next, effectSlot, Front.fill, Bind.bind, EStateM.bind, liftPull, liftEffect, first,
          Pure.pure, EStateM.pure]
  | buffered itemA =>
    cases b with
    | unread cursorB =>
      cases second : older cursorB start <;>
        simp [next, effectSlot, Front.fill, Bind.bind, EStateM.bind, liftPull, liftEffect, second,
          Pure.pure, EStateM.pure]
    | buffered itemB => rfl

theorem next_preserves [LT key] [DecidableLT key] (keyOf : row → key)
    {newer : Pull (EStateM ε σ) left row} {older : Pull (EStateM ε σ) right row}
    (observe : σ → α)
    (newFrame : ∀ pos start item reached, newer pos start = .ok item reached →
      observe reached = observe start)
    (oldFrame : ∀ pos start item reached, older pos start = .ok item reached →
      observe reached = observe start)
    {front after : Frontier left right row} {start reached : σ} {item : Option row}
    (ran : next keyOf (liftPull newer) (liftPull older) effectSlot (front, start) =
      .ok item (after, reached)) :
    observe reached = observe start := by
  have frame {cursor : Type} {read : Pull (EStateM ε σ) cursor row}
      (law : ∀ pos s item t, read pos s = .ok item t → observe t = observe s)
      (head : Front cursor row) {s t : σ} {item : Option (row × cursor)}
      (ran : head.fill read s = .ok item t) : observe t = observe s := by
    cases head with
    | unread pos => exact law pos s item t ran
    | buffered value => cases ran; rfl
  rw [next_effect] at ran
  cases first : front.newer.fill newer start with
  | error => simp [first] at ran
  | ok a middle =>
    cases second : front.older.fill older middle with
    | error => simp [first, second] at ran
    | ok b last =>
      simp only [first, second] at ran
      cases ran
      exact (frame oldFrame _ second).trans (frame newFrame _ first)

theorem choose_exact [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : left → List row) (older : right → List row)
    (a : Option (row × left)) (b : Option (row × right)) :
    let before : Frontier left right row := ⟨.buffered a, .buffered b⟩
    let (item, after) := choose keyOf a b
    (item = (before.remaining keyOf newer older).head? ∧
      after.remaining keyOf newer older = (before.remaining keyOf newer older).tail) ∧
    (item = none → before.newer.remaining newer = [] ∧ before.older.remaining older = []) ∧
    (item.isSome →
      (after.newer.remaining newer).length + (after.older.remaining older).length <
        (before.newer.remaining newer).length + (before.older.remaining older).length) := by
  rcases a with _ | ⟨rowA, cursorA⟩ <;> rcases b with _ | ⟨rowB, cursorB⟩
  · simp [choose, Frontier.remaining, Front.remaining]
  · simp [choose, Frontier.remaining, Front.remaining, merge]
  · simp [choose, Frontier.remaining, Front.remaining]
  · by_cases ab : keyOf rowA < keyOf rowB
    · simp [choose, Frontier.remaining, Front.remaining, merge, ab]
    · by_cases ba : keyOf rowB < keyOf rowA
      · simp [choose, Frontier.remaining, Front.remaining, merge, ab, ba]
      · simp [choose, Frontier.remaining, Front.remaining, merge, ab, ba]
        omega

/-- The exact transition of the two input suffixes. A buffered loser is
still part of its input suffix. -/
inductive Consumes [LT key] (keyOf : row → key) :
    List row → List row → Option row → List row → List row → Prop where
  | eof : Consumes keyOf [] [] none [] []
  | newerOnly : Consumes keyOf (a :: as) [] (some a) as []
  | olderOnly : Consumes keyOf [] (b :: bs) (some b) [] bs
  | newer : keyOf a < keyOf b → Consumes keyOf (a :: as) (b :: bs) (some a) as (b :: bs)
  | older : keyOf b < keyOf a → Consumes keyOf (a :: as) (b :: bs) (some b) (a :: as) bs
  | tie : ¬ keyOf a < keyOf b → ¬ keyOf b < keyOf a →
      Consumes keyOf (a :: as) (b :: bs) (some a) as bs

private theorem choose_consumes [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : left → List row) (older : right → List row)
    (a : Option (row × left)) (b : Option (row × right)) :
    let (item, after) := choose keyOf a b
    Consumes keyOf ((Front.buffered a).remaining newer) ((Front.buffered b).remaining older)
      item (after.newer.remaining newer) (after.older.remaining older) := by
  rcases a with _ | ⟨rowA, cursorA⟩ <;> rcases b with _ | ⟨rowB, cursorB⟩
  · exact .eof
  · exact .olderOnly
  · exact .newerOnly
  · by_cases ab : keyOf rowA < keyOf rowB
    · simpa [choose, ab, Front.remaining] using
        (Consumes.newer (as := newer cursorA) (bs := older cursorB) ab)
    · by_cases ba : keyOf rowB < keyOf rowA
      · simpa [choose, ab, ba, Front.remaining] using
          (Consumes.older (as := newer cursorA) (bs := older cursorB) ba)
      · simpa [choose, ab, ba, Front.remaining] using
          (Consumes.tie (as := newer cursorA) (bs := older cursorB) ab ba)

/-- Every successful row consumes exactly the chosen head(s). EOF requires
both original suffixes to be empty. The sum of suffix lengths decreases
on every emitted row, including ties. -/
theorem next_exact [LT key] [DecidableLT key] (keyOf : row → key)
    {newer : Pull (EStateM ε σ) left row} {older : Pull (EStateM ε σ) right row}
    {newRows : left → List row} {oldRows : right → List row}
    (newExact : newer.Exact newRows) (oldExact : older.Exact oldRows)
    {front after : Frontier left right row} {start reached : σ} {item : Option row}
    (ran : next keyOf (liftPull newer) (liftPull older) effectSlot (front, start) =
      .ok item (after, reached)) :
    (item = (front.remaining keyOf newRows oldRows).head? ∧
      after.remaining keyOf newRows oldRows = (front.remaining keyOf newRows oldRows).tail) ∧
    (item = none → front.newer.remaining newRows = [] ∧ front.older.remaining oldRows = []) ∧
    (item.isSome →
      (after.newer.remaining newRows).length + (after.older.remaining oldRows).length <
        (front.newer.remaining newRows).length + (front.older.remaining oldRows).length) ∧
    Consumes keyOf (front.newer.remaining newRows) (front.older.remaining oldRows)
      item (after.newer.remaining newRows) (after.older.remaining oldRows) := by
  rw [next_effect] at ran
  cases first : front.newer.fill newer start with
  | error => simp [first] at ran
  | ok a middle =>
    cases second : front.older.fill older middle with
    | error => simp [first, second] at ran
    | ok b last =>
      have newEq := fill_exact newExact first
      have oldEq := fill_exact oldExact second
      simp only [first, second] at ran
      cases chosen : choose keyOf a b with
      | mk selected final =>
        rw [chosen] at ran
        cases ran
        have facts := choose_exact keyOf newRows oldRows a b
        have consumed := choose_consumes keyOf newRows oldRows a b
        simp only [chosen, Frontier.remaining] at facts consumed ⊢
        rw [← newEq, ← oldEq]
        exact ⟨facts.1, facts.2.1, facts.2.2, consumed⟩

end SortedRun
