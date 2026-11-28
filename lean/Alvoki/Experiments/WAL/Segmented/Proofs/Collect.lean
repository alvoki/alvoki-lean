import Alvoki.Experiments.WAL.Segmented.Proofs.Publication

namespace WalRecoverySlice.Segmented.Model

/-- Collection removes only retired names. It leaves all segment objects and
cursors intact. A directory barrier can make the live catalog durable. -/
structure CollectionFrame (first : Nat) (before after : Disk) : Prop where
  liveControl : after.liveControl = before.liveControl
  durableControl : after.durableControl = before.durableControl ∨ after.durableControl = before.liveControl
  staged : after.staged = before.staged
  stagedDurable : after.stagedDurable = before.stagedDurable
  segment : after.segment = before.segment
  cursor : after.cursor = before.cursor
  liveSubset : ∀ id ∈ after.liveNames, id ∈ before.liveNames
  keepsNamed : ∀ id, first ≤ id → id ∈ before.liveNames → id ∈ before.durableNames →
    id ∈ after.liveNames ∧ id ∈ after.durableNames

private theorem CollectionFrame.refl (first : Nat) (disk : Disk) : CollectionFrame first disk disk :=
  ⟨rfl, .inl rfl, rfl, rfl, rfl, rfl, fun _ h => h, fun _ _ h₁ h₂ => ⟨h₁, h₂⟩⟩

private theorem CollectionFrame.trans (one : CollectionFrame first before middle)
    (two : CollectionFrame first middle after) : CollectionFrame first before after := by
  refine ⟨two.liveControl.trans one.liveControl, ?_, two.staged.trans one.staged,
    two.stagedDurable.trans one.stagedDurable, two.segment.trans one.segment,
    two.cursor.trans one.cursor, fun id hi => one.liveSubset id (two.liveSubset id hi), ?_⟩
  · rcases two.durableControl with old | live
    · rw [old]; exact one.durableControl
    · exact .inr (live.trans one.liveControl)
  · intro id keep live durable
    obtain ⟨live, durable⟩ := one.keepsNamed id keep live durable
    exact two.keepsNamed id keep live durable

private theorem CollectionFrame.remove (before : Disk) {id first : Nat} (retired : id < first) (persist : Bool) :
    CollectionFrame first before (before.remove id persist) := by
  refine ⟨rfl, .inl rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro n member
    exact (List.mem_filter.mp member).1
  · intro n keep live durable
    have other : n ≠ id := Nat.ne_of_gt (Nat.lt_of_lt_of_le retired keep)
    cases persist <;> simp [Disk.remove, other, live, durable]

private theorem CollectionFrame.syncRoot (first : Nat) (before : Disk) :
    CollectionFrame first before before.syncRoot :=
  ⟨rfl, .inr rfl, rfl, rfl, rfl, rfl, fun _ h => h, fun _ _ h _ => ⟨h, h⟩⟩

private theorem mapPost {result : Result α} {ok next : α → Disk → Prop} {stop later : Disk → Prop}
    (h : DiskPost ok stop result) (success : ∀ value disk, ok value disk → next value disk)
    (failure : ∀ disk, stop disk → later disk) : DiskPost next later result := by
  cases result with
  | error _ s => exact failure s.disk h
  | ok result s => cases result with
    | error _ => exact failure s.disk h
    | ok value => exact success value s.disk h

structure CollectionEffects (callbacks : Ops M) : Prop where
  list : ∀ s, DiskPost
    (fun ids d => (∀ id ∈ s.disk.liveNames, id ∈ ids) ∧ d = s.disk)
    (· = s.disk) (callbacks.listSegments.run s)
  remove : ∀ id s, DiskPost (fun _ d => ∃ p, d = s.disk.remove id p)
    (fun d => d = s.disk ∨ ∃ p, d = s.disk.remove id p)
    ((callbacks.removeSegment id).run s)
  sync : ∀ s, DiskPost (fun _ d => d = s.disk.syncRoot)
    (fun d => d = s.disk ∨ d = s.disk.syncRoot) (callbacks.syncRoot.run s)

theorem modelCollectionEffects (effects : Effects) : CollectionEffects (ops effects) where
  list s := by
    change DiskPost _ _ (read (effects.listing s.step) (.ok s.disk.liveNames) s)
    cases effects.listing s.step with
    | none => exact ⟨fun _ h => h, rfl⟩
    | some fault => cases fault <;> rfl
  remove id s := by
    apply namespacePost (effects.remove s.step id) (fun d p => d.remove id p) s
    · exact .inl rfl
    · exact fun p => .inr ⟨p, rfl⟩
    · exact fun p => ⟨p, rfl⟩
  sync s := by
    apply barrierPost (effects.root s.step) Disk.syncRoot s
    · exact .inl rfl
    · exact .inr rfl
    · rfl

private theorem removeRetired_cases {callbacks : Ops M} (effects : CollectionEffects callbacks) (first : Nat) (ids : List Nat) (s : State) :
    DiskPost (fun _ after => CollectionFrame first s.disk after ∧
      ∀ id ∈ ids, id < first → id ∉ after.liveNames)
      (CollectionFrame first s.disk) (((Segmented.removeRetired callbacks.toRootOps first ids).run s)) := by
  induction ids generalizing s with
  | nil => exact ⟨.refl first s.disk, by simp⟩
  | cons id ids ih =>
    by_cases retired : id < first
    · simp only [Segmented.removeRetired, retired, ↓reduceIte]
      apply bindPost (P := fun _ after => ∃ p, after = s.disk.remove id p)
      · apply mapPost (effects.remove id s)
        · exact fun _ _ h => h
        · intro d h
          rcases h with rfl | ⟨p, rfl⟩
          · exact .refl first s.disk
          · exact .remove s.disk retired p
      intro _ removed ⟨persist, exactRemoved⟩
      have initialFrame : CollectionFrame first s.disk removed.disk := by
        rw [exactRemoved]
        exact .remove s.disk retired persist
      apply mapPost (ih removed)
      · intro _ after ⟨tail, gone⟩
        refine ⟨initialFrame.trans tail, ?_⟩
        intro n member old survived
        rcases List.mem_cons.mp member with equal | member
        · subst n
          have still := tail.liveSubset id survived
          simp [exactRemoved, Disk.remove] at still
        · exact gone n member old survived
      · intro _ tail
        exact initialFrame.trans tail
    · apply mapPost (result := ((Segmented.removeRetired callbacks.toRootOps first (id :: ids)).run s))
        (ok := fun _ after => CollectionFrame first s.disk after ∧
          ∀ n ∈ ids, n < first → n ∉ after.liveNames)
      · simpa [Segmented.removeRetired, retired] using ih s
      · intro _ _ ⟨frame, gone⟩
        refine ⟨frame, ?_⟩
        intro n member old
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (retired old)
        · exact gone n member old
      · exact fun _ h => h

/-- The actual listing and removal loop preserve selected names even on an
error or interruption. On success, exactly the live names remaining after
those removals are durable, and every remaining name is at least `firstNeeded`. -/
theorem collectWith_cases {callbacks : Ops M} (effects : CollectionEffects callbacks) (c : Control) (s : State) :
    DiskPost (fun _ after => CollectionFrame c.firstNeeded s.disk after ∧
      after.durableControl = after.liveControl ∧ after.durableNames = after.liveNames ∧
      ∀ id ∈ after.liveNames, c.firstNeeded ≤ id)
      (CollectionFrame c.firstNeeded s.disk) ((Segmented.collect callbacks.toRootOps c).run s) := by
  unfold Segmented.collect
  apply bindPost (P := fun ids after => (∀ id ∈ s.disk.liveNames, id ∈ ids) ∧ after = s.disk)
  · apply mapPost (effects.list s)
    · exact fun _ _ h => h
    · intro _ rfl; exact .refl _ _
  intro ids listed ⟨idsExact, listedExact⟩
  apply bindPost (P := fun _ after => CollectionFrame c.firstNeeded s.disk after ∧
    ∀ id ∈ after.liveNames, c.firstNeeded ≤ id)
  · apply mapPost (removeRetired_cases effects c.firstNeeded ids listed)
    · intro _ after ⟨frame, gone⟩
      rw [listedExact] at frame
      refine ⟨frame, ?_⟩
      intro id member
      have original := frame.liveSubset id member
      have original := idsExact id original
      exact Nat.le_of_not_gt (fun retired => gone id original retired member)
    · intro _ frame
      rw [listedExact] at frame
      exact frame
  intro _ pruned ⟨frame, gone⟩
  apply mapPost (effects.sync pruned)
  · intro _ _ rfl
    exact ⟨frame.trans (.syncRoot c.firstNeeded pruned.disk), rfl, rfl, gone⟩
  · intro _ h
    rcases h with eq | eq
    · rw [eq]; exact frame
    · rw [eq]; exact frame.trans (.syncRoot c.firstNeeded pruned.disk)

theorem collect_cases (effects : Effects) (c : Control) (s : State) :
    DiskPost (fun _ after => CollectionFrame c.firstNeeded s.disk after ∧
      after.durableControl = after.liveControl ∧ after.durableNames = after.liveNames ∧
      ∀ id ∈ after.liveNames, c.firstNeeded ≤ id)
      (CollectionFrame c.firstNeeded s.disk) ((Segmented.collect ((ops effects).toRootOps) c).run s) :=
  collectWith_cases (modelCollectionEffects effects) c s

private theorem run_bind_ok {a : M α} {next : α → M β} {before after : State} {value : α}
    (got : a.run before = .ok (.ok value) after) :
    (a >>= next).run before = (next value).run after := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind] at got ⊢
  rw [got]
  rfl

private theorem removeRetired_healthy (first : Nat) (ids : List Nat) (s : State) :
    ∃ after, ((Segmented.removeRetired ((ops healthy).toRootOps) first ids).run s) = .ok (.ok ()) after := by
  induction ids generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons id ids ih =>
    by_cases retired : id < first
    · simp only [Segmented.removeRetired, retired, ↓reduceIte]
      rw [run_bind_ok (show ((ops healthy).removeSegment id).run s =
        .ok (.ok ()) {s.tick with disk := s.disk.remove id false} from rfl)]
      exact ih _
    · simpa [Segmented.removeRetired, retired] using ih s

theorem collect_healthy (c : Control) (s : State) :
    ∃ after, ((Segmented.collect ((ops healthy).toRootOps) c).run s) = .ok (.ok ()) after := by
  unfold Segmented.collect
  rw [run_bind_ok (show (ops healthy).listSegments.run s = .ok (.ok s.disk.liveNames) s.tick from rfl)]
  obtain ⟨pruned, removed⟩ := removeRetired_healthy c.firstNeeded s.disk.liveNames s.tick
  rw [run_bind_ok removed]
  exact ⟨_, rfl⟩

end WalRecoverySlice.Segmented.Model
