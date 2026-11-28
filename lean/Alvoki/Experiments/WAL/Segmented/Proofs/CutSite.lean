import Alvoki.Experiments.WAL.Segmented.Proofs.CutFrameMemory

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Alvoki.NativePost (W)
open Model (Disk)

private structure Located (a : Observed α) (b : W → Observed α) : Prop where
  same : ∀ last, (b last).run = a.run
  find : ∀ w d, a.cuts w d → ∃ last, (b last).cuts w d

private theorem Located.bind {a : Observed α} {f : α → Observed β} {next : W → α → Observed β} (first : Located a tagged)
    (more : ∀ x, Located (f x) (fun t => next t x)) :
    Located (a >>= f) (fun t => tagged t >>= next t) := by
  constructor
  · intro t
    change ((tagged t).run >>= fun x => (next t x).run) = (a.run >>= fun x => (f x).run)
    rw [first.same]
    exact congrArg (Bind.bind a.run) (funext fun x => (more x).same t)
  · rintro w d (here | ⟨x, u, ran, there⟩)
    · obtain ⟨t, cut⟩ := first.find w d here
      exact ⟨t, Or.inl cut⟩
    · obtain ⟨t, cut⟩ := (more x).find u d there
      exact ⟨t, Or.inr ⟨x, u, (first.same t) ▸ ran, cut⟩⟩

private theorem Located.handle {a : Observed α} {f : IO.Error → Observed α} {next : W → IO.Error → Observed α} (first : Located a tagged)
    (more : ∀ e, Located (f e) (fun t => next t e)) :
    Located (tryCatchThe IO.Error a f) (fun t => tryCatchThe IO.Error (tagged t) (next t)) := by
  constructor
  · intro t
    change tryCatchThe IO.Error (tagged t).run _ = tryCatchThe IO.Error a.run _
    rw [first.same]
    exact congrArg (tryCatchThe IO.Error a.run) (funext fun e => (more e).same t)
  · rintro w d (here | ⟨e, u, ran, there⟩)
    · obtain ⟨t, cut⟩ := first.find w d here
      exact ⟨t, Or.inl cut⟩
    · obtain ⟨t, cut⟩ := (more e).find u d there
      exact ⟨t, Or.inr ⟨e, u, (first.same t) ▸ ran, cut⟩⟩

private theorem Located.leaf {cuts : W → Disk → Prop} {timed : W → W → Disk → Prop} (h : ∀ w d, cuts w d → ∃ t, timed t w d) :
    Located (Observed.mk run cuts) (fun t => ⟨run, timed t⟩) := ⟨fun _ => rfl, h⟩

private theorem Located.pure (x : α) : Located (pure x) (fun _ => pure x) :=
  ⟨fun _ => rfl, fun _ _ cut => False.elim cut⟩

private theorem Located.throw (e : IO.Error) : Located (throw e : Observed α) (fun _ => throw e) :=
  ⟨fun _ => rfl, fun _ _ cut => False.elim cut⟩

private theorem ChildStop.located (cut : ChildStop stop h batch w d) :
    ∃ t, ChildStop (tagAt stop t) h batch w d := by
  cases cut with
  | entry site stopped => exact ⟨_, .entry site ⟨rfl, stopped⟩⟩
  | before operand site stopped => exact ⟨_, .before operand site ⟨rfl, stopped⟩⟩
  | inside r => exact ⟨r.atCall, .inside {r with stopped := ⟨rfl, r.stopped⟩}⟩
  | after r => exact ⟨r.atCall, .after {r with cut := ⟨rfl, r.cut⟩}⟩

private theorem bodyLocated (s : Store) (session : Session) (batch : Bytes) (stop : Stop) :
    Located ((sites s session stop).appendSession session batch)
      (fun t => (sites s session (tagAt stop t)).appendSession session batch) := by
  unfold Sites.appendSession appendOwnedWith
  apply Located.bind (Located.leaf (fun _ _ bad => False.elim bad))
  intro _
  dsimp only
  by_cases full : session.activeCount = session.control.capacity
  · simp only [full, ↓reduceIte]
    refine Located.bind (Located.leaf ?_) ?_
    · rintro w d ⟨α,a,t,site,cut⟩
      exact ⟨t, α,a,t,site,rfl,cut⟩
    intro _
    unfold withActiveChild
    refine Located.bind (Located.leaf ?_) ?_
    · rintro w d (⟨pt,t,α,a,seen,issued,cut⟩ | ⟨v,leaf,t,seen,issued,cut⟩)
      · exact ⟨t, .inl ⟨pt,t,α,a,seen,issued,rfl,cut⟩⟩
      · exact ⟨t, .inr ⟨v,leaf,t,seen,issued,rfl,cut⟩⟩
    intro h
    unfold cleanupOnError
    apply Located.handle
    · apply Located.bind (Located.leaf fun w _ cut => ⟨w,rfl,cut⟩)
      intro _
      refine Located.bind (Located.leaf ?_) ?_
      · rintro w d ⟨pt,t,α,a,k,seen,issued,cut⟩
        exact ⟨t,pt,t,α,a,k,seen,issued,rfl,cut⟩
      intro _
      apply Located.bind (Located.leaf fun _ _ cut => ChildStop.located cut)
      intro _
      apply Located.bind (Located.leaf fun w _ cut => ⟨w,rfl,cut⟩)
      exact fun _ => Located.pure _
    · intro e
      apply Located.bind
      · apply Located.handle (Located.leaf ?_) (fun _ => Located.pure _)
        rintro w d ⟨α,a,t,site,cut⟩
        exact ⟨t,α,a,t,site,rfl,cut⟩
      exact fun _ => Located.throw e
  · simp only [full, ↓reduceIte]
    apply Located.bind (Located.leaf fun w _ cut => ⟨w,rfl,cut⟩)
    rintro (none | ⟨id,h⟩)
    · exact Located.throw _
    · dsimp only
      split
      · apply Located.bind (Located.leaf fun _ _ cut => ChildStop.located cut)
        exact fun _ => Located.pure _
      · apply Located.bind (Located.throw _)
        intro _
        apply Located.bind (Located.leaf fun _ _ cut => ChildStop.located cut)
        exact fun _ => Located.pure _

/-- Recording the actual issuing world does not discard any admitted cut. -/
theorem PublicStop.located (cut : PublicStop cell mutex store session batch w stop d) :
    ∃ last, PublicStop cell mutex store session batch w (tagAt stop last) d := by
  cases cut with
  | lock h => exact ⟨_, .lock ⟨rfl,h⟩⟩
  | read h => exact ⟨_, .read ⟨rfl,h⟩⟩
  | poison h => exact ⟨_, .poison ⟨rfl,h⟩⟩
  | worker h =>
    obtain ⟨last, atLast⟩ := (bodyLocated store session batch stop).find _ _ h
    exact ⟨last, .worker atLast⟩
  | install ran h => exact ⟨_, .install ran ⟨rfl,h⟩⟩
  | leave ran h => exact ⟨_, .leave ran ⟨rfl,h⟩⟩
  | fail ran h => exact ⟨_, .fail ran ⟨rfl,h⟩⟩

theorem BeforeWorker.located (cut : BeforeWorker cell mutex store w stop d) :
    ∃ last, BeforeWorker cell mutex store w (tagAt stop last) d := by
  cases cut with
  | lock h => exact ⟨_, .lock ⟨rfl,h⟩⟩
  | read h => exact ⟨_, .read ⟨rfl,h⟩⟩
  | poison h => exact ⟨_, .poison ⟨rfl,h⟩⟩

theorem AfterSuccess.located (cut : AfterSuccess cell mutex store session batch w stop d) :
    ∃ last, AfterSuccess cell mutex store session batch w (tagAt stop last) d := by
  cases cut with
  | install ran h => exact ⟨_, .install ran ⟨rfl,h⟩⟩
  | leave ran h => exact ⟨_, .leave ran ⟨rfl,h⟩⟩

end WalRecoverySlice.Segmented.Native.AppendCut
