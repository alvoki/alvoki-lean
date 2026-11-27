import Alvoki.Experiments.WAL.Segmented.Proofs.Child
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Segmented.Proofs.Collect

namespace WalRecoverySlice.Segmented.Model

/-- The root barrier commits the observed name map before any child repair. -/
private structure Opening (c : Control) (known : List Bytes) (pending : Option Bytes)
    (active : DataImage) (disk : Disk) : Prop where
  live : disk.liveControl = some c
  durable : disk.durableControl = some c
  selected : Readable c known pending disk
  sameActive : disk.segment c.active = active

private theorem Opening.recoverable {c h p active d known req} (o : Opening c h p active d)
    (allowed : ∀ v, WalRecoverySlice.Contract.Permitted h p v → PermittedView known req (historyView c v)) :
    Recoverable known req d := by
  have choice : RecoveryChoice known req c d := ⟨h, p, o.selected, allowed⟩
  exact ⟨⟨c, o.live, choice⟩, ⟨c, o.durable, choice⟩⟩

/-- A choice in the active child extends the global history by precisely the
same pending batch. Every sealed segment keeps its original byte interval. -/
private theorem resolve_active {c h p disk decoded} (r : Readable c h p disk)
    (choice : WalRecoverySlice.Contract.Permitted (segmentHistory c.capacity c.active h) p decoded)
    (bounded : ∀ b ∈ decoded, b.length ≤ 32) :
    ∃ final, WalRecoverySlice.Contract.Permitted h p final ∧
      segmentHistory c.capacity c.active final = decoded ∧
      (∀ i, i < c.active → segmentHistory c.capacity i final = segmentHistory c.capacity i h) ∧
      (∀ other, Layout c h other → Layout c final other) := by
  rcases choice with rfl | rfl
  · exact ⟨h, .inl rfl, rfl, fun _ _ => rfl, fun _ orig => orig⟩
  cases p with
  | none => exact ⟨h, .inl rfl, by simp, fun _ _ => rfl, fun _ orig => orig⟩
  | some batch =>
    have room := r.room rfl
    have earlier (i : Nat) (lt : i < c.active) :
        segmentHistory c.capacity i (h ++ [batch]) = segmentHistory c.capacity i h :=
      segmentHistory_before_append _ (Nat.le_trans (Nat.mul_le_mul_right _ lt) r.layout.lower)
    refine ⟨h ++ [batch], .inr rfl, segmentHistory_append _ r.layout.lower room, earlier, ?_⟩
    exact fun _ orig => orig.extend batch (bounded batch (by simp)) room

private theorem outcome_reached {α : Type} {result : Result α} {expected : α}
    {inv failure : State → Prop}
    (ok : ∀ v, returned result = some v → inv (reached result) ∧ v = expected)
    (fail : returned result = none → failure (reached result)) :
    readOutcome inv failure expected result := by
  cases result with
  | error => exact fail rfl
  | ok val _ =>
    cases val with
    | error => exact fail rfl
    | ok v => exact ok v rfl

private theorem sealed_step {c h p active} (e : Effects) {s : State} {id : Nat}
    (o : Opening c h p active s.disk) (low : c.firstNeeded ≤ id) (lt : id < c.active) :
    let result := ((ops e).openSegment c.policy id).run s
    Opening c h p active (reached result).disk ∧
      (∀ v, returned result = some v → v = segmentHistory c.capacity id h) ∧
      (e = healthy → ∃ v, returned result = some v) := by
  have selects : c.selects id := ⟨low, Nat.le_of_lt lt⟩
  have named := (o.selected.layout.names id selects).1
  obtain ⟨ready, clean⟩ := o.selected.layout.sealed id selects lt
  have bs := segmentHistory_bounded o.selected.layout id
  have fits := Nat.le_trans (segmentHistory_fits c.capacity id h) o.selected.layout.capacityFits
  have result := openSegment_settled e named ready clean bs fits
  dsimp only at result ⊢
  let call := openChild e s.step id c.policy
  have frame := child_reached named call Decoded.cursor Decoded.batches
  change reached (((ops e).openSegment c.policy id).run s) = _ at frame
  have files (i : Nat) : (reached (((ops e).openSegment c.policy id).run s)).disk.segment i = s.disk.segment i := by
    by_cases same : i = id
    · subst i; exact result.1
    · rw [frame]; exact Disk.setSegment_other _ _ _ same
  refine ⟨⟨by rw [frame]; exact o.live, by rw [frame]; exact o.durable,
    o.selected.frame (by rw [frame]; exact o.selected.layout.names) (fun i _ => files i),
    (files _).trans o.sameActive⟩, fun v ret => (result.2 v ret).1, ?_⟩
  intro eqn; subst e
  exact openSegment_healthy named (Persistence.ready_dirty c.policy _ _ ready clean bs fits)

private structure Opened (c : Control) (history : List Bytes) (d : Disk) : Prop where
  ready : ReadyLayout c history d
  live : d.liveControl = some c
  durable : d.durableControl = some c

private theorem Opened.recoverable {c final d known req} (o : Opened c final d)
    (perm : PermittedView known req (historyView c final)) : Recoverable known req d :=
  ⟨⟨c, o.live, o.ready.choice perm⟩, ⟨c, o.durable, o.ready.choice perm⟩⟩

private theorem active_step {c h p active final known req} (e : Effects) {s : State}
    (o : Opening c h p active s.disk)
    (allow : ∀ v, WalRecoverySlice.Contract.Permitted h p v → PermittedView known req (historyView c v))
    (layout : ∀ disk, Layout c h disk → Layout c final disk)
    (canonical : ∀ fx sched ret, Persistence.acknowledged
        ((WalRecoverySlice.reopen (Persistence.scheduledOps (Persistence.ops fx) sched) c.policy).run active) = some ret →
        ret.batches = segmentHistory c.capacity c.active final) :
    readOutcome (fun t => Opened c final t.disk)
      (fun t => Recoverable known req t.disk ∧ e ≠ healthy)
      (segmentHistory c.capacity c.active final) (((ops e).openSegment c.policy c.active).run s) := by
  let id := c.active
  let out := ((ops e).openSegment c.policy id).run s
  let later := (reached out).disk
  have named := (o.selected.layout.names id c.selectsActive).1
  let run := openChild e s.step id c.policy
  have frame := child_reached named run Decoded.cursor Decoded.batches
  change reached out = _ at frame
  have ret := child_returned named run Decoded.cursor Decoded.batches
  change returned out = _ at ret
  have ⟨retry, markers, success⟩ := openSegment_dirty e named o.selected.active
  have names : ∀ i, c.selects i → i ∈ later.liveNames ∧ i ∈ later.durableNames := by
    dsimp only [later]; rw [frame]; exact o.selected.layout.names
  have closed (i : Nat) (_ : c.selects i) (lt : i < id) : later.segment i = s.disk.segment i := by
    dsimp only [later]; rw [frame]; exact Disk.setSegment_other _ _ _ (Nat.ne_of_lt lt)
  have oldLayout := o.selected.layout.frame names closed
  have lh : later.liveControl = some c := by dsimp only [later]; rw [frame]; exact o.live
  have dh : later.durableControl = some c := by dsimp only [later]; rw [frame]; exact o.durable
  apply outcome_reached
  · intro v ack
    change returned out = some v at ack
    obtain ⟨_, cursor, ready, _, _, clean⟩ := success v ack
    rw [ret] at ack
    obtain ⟨d, inner, rfl⟩ := Option.map_eq_some_iff.mp ack
    change Persistence.acknowledged ((WalRecoverySlice.reopen (Persistence.scheduledOps (Persistence.ops _) _) c.policy).run (s.disk.segment id)) = _ at inner
    rw [o.sameActive] at inner
    have chosen := canonical _ _ d inner
    rw [chosen] at ready cursor
    refine ⟨⟨⟨layout later oldLayout, ready, clean ?_, cursor⟩, lh, dh⟩, chosen⟩
    cases hpolicy : c.policy with
    | logOnly => exact .inr (o.selected.logMarkers hpolicy)
    | boundary => exact .inl rfl
  · intro no
    have available : e ≠ healthy := by
      intro he; subst e
      obtain ⟨v, ret⟩ := openSegment_healthy named o.selected.active
      rw [no] at ret
      contradiction
    let r : Readable c h p later := ⟨oldLayout, o.selected.room, retry, fun branch => markers (o.selected.logMarkers branch)⟩
    have choice : RecoveryChoice known req c later := ⟨h, p, r, allow⟩
    exact ⟨⟨⟨c, lh, choice⟩, ⟨c, dh, choice⟩⟩, available⟩

private theorem collect_step {c h k req} (e : Effects) (s : State) (o : Opened c h s.disk)
    (permit : PermittedView k req (historyView c h)) :
    readOutcome (fun t => Opened c h t.disk) (fun t => Recoverable k req t.disk ∧ e ≠ healthy)
      () ((Segmented.collect (ops e) c).run s) := by
  have keep {d} (f : CollectionFrame c.firstNeeded s.disk d) : Opened c h d := by
    refine ⟨o.ready.frame (fun id chosen => ?_) (fun _ _ => by rw [f.segment]) (by rw [f.cursor]),
      f.liveControl.trans o.live, f.durableControl.elim (·.trans o.durable) (·.trans o.live)⟩
    obtain ⟨live, durable⟩ := o.ready.layout.names id chosen
    exact f.keepsNamed id chosen.1 live durable
  have frame := collect_cases e c s
  have available : e = healthy → ∃ t, (Segmented.collect (ops e) c).run s = .ok (.ok ()) t := by
    rintro rfl; exact collect_healthy c s
  cases eqn : (Segmented.collect (ops e) c).run s with
  | error _ t =>
    rw [eqn] at frame available
    exact ⟨(keep frame).recoverable permit, fun eq => by obtain ⟨_, a⟩ := available eq; cases a⟩
  | ok val t =>
    cases val with
    | error cause =>
      rw [eqn] at frame available
      exact ⟨(keep frame).recoverable permit, fun eq => by obtain ⟨_, a⟩ := available eq; cases a⟩
    | ok u =>
      rw [eqn] at frame
      exact ⟨keep frame.1, rfl⟩

private theorem reopen_source {k req} (e : Effects) (s : State) (prior : Recoverable k req s.disk) :
    ∃ c final, PermittedView k req (historyView c final) ∧
      readOutcome (fun t => Opened c final t.disk) (fun t => Recoverable k req t.disk ∧ e ≠ healthy)
        (sessionOf c final) ((Segmented.reopen (ops e)).run s) := by
  obtain ⟨c, found, h, p, r, allow⟩ := prior.live
  obtain ⟨d, after, good⟩ := r.active.healthy_reopen
  have ack : Persistence.acknowledged ((WalRecoverySlice.reopen (Persistence.ops Persistence.healthyReopen)
      c.policy).run (s.disk.segment c.active)) = some d := by rw [good]; rfl
  obtain ⟨choice, _, _, bounded, _⟩ := (r.active.reopen Persistence.healthyReopen).2.2 d ack
  obtain ⟨final, permitted, slice, earlier, lift⟩ := resolve_active r choice bounded
  have finish := lift _ r.layout
  obtain ⟨marker, sel, _⟩ := Persistence.healthy_reopen_selection good
  refine ⟨c, final, allow final permitted, ?_⟩
  simp only [sessionOf, segmentHistory_active_length finish.upper, historyView]
  apply reopen_spec (ops e) c final s (fun t => t.disk = s.disk)
    (fun t => Opening c h p (s.disk.segment c.active) t.disk) (fun t => Opened c final t.disk)
    _ _ ⟨finish.capacityPositive, finish.capacityFits⟩ finish.lower finish.upper finish.discardedFits
  · change readOutcome _ _ _ (read (e.controlRead s.step) _ s)
    rw [found]
    cases fx : e.controlRead s.step with
    | none => exact ⟨rfl, rfl⟩
    | some a =>
      have ne : e ≠ healthy := by rintro rfl; cases fx
      cases a <;> exact ⟨prior, ne⟩
  · intro t same
    have synced : Opening c h p (s.disk.segment c.active) t.disk.syncRoot := by
      rw [same]
      exact ⟨found, found, r.frame (fun id chosen =>
        ⟨(r.layout.names id chosen).1, (r.layout.names id chosen).1⟩) (fun _ _ => rfl), rfl⟩
    change readOutcome _ _ _ (barrier (e.root t.step) Disk.syncRoot t)
    cases fx : e.root t.step with
    | before a =>
      have ne : e ≠ healthy := by rintro rfl; cases fx
      cases a <;> exact ⟨same.symm ▸ prior, ne⟩
    | after a =>
      cases a with
      | none => exact ⟨synced, rfl⟩
      | some a =>
        have ne : e ≠ healthy := by rintro rfl; cases fx
        cases a <;> exact ⟨synced.recoverable allow, ne⟩
  · intro id low lt t o
    have result := sealed_step e o low lt
    apply outcome_reached
    · exact fun v ret => ⟨result.1, (result.2.1 v ret).trans (earlier id lt).symm⟩
    · intro no
      refine ⟨result.1.recoverable allow, fun eq => ?_⟩
      obtain ⟨v, ok⟩ := result.2.2 eq
      rw [no] at ok
      contradiction
  · intro t o
    apply active_step e o allow lift
    intro fx sched ret ack
    exact (congrArg Decoded.batches (scheduledReopen_selected sel fx sched ret ack)).trans slice.symm
  · exact fun t o => collect_step e t o (allow final permitted)

/-- A successful source reopen installs the exact permitted view. Every reported
I/O error or interruption leaves a state from which the same request can recover. -/
theorem reopen_refines {k req} (e : Effects) (s : State) (prior : Recoverable k req s.disk) :
    DiskPost (fun next disk => Installed next disk ∧ PermittedView k req next.view)
      (Recoverable k req) ((Segmented.reopen (ops e)).run s) := by
  obtain ⟨c, final, permit, post⟩ := reopen_source e s prior
  cases hr : (Segmented.reopen (ops e)).run s with
  | error _ _ => rw [hr] at post; exact post.1
  | ok result t =>
    cases result with
    | error => rw [hr] at post; exact post.1
    | ok next =>
      rw [hr] at post
      obtain ⟨opened, rfl⟩ := post
      exact ⟨⟨final, rfl, opened.ready, opened.live, opened.durable⟩, permit⟩

/-- Once faults cease, the actual source reopen finishes after any permitted prefix. -/
theorem reopen_healthy {k req} (s : State) (prior : Recoverable k req s.disk) :
    ∃ next after, ((Segmented.reopen (ops healthy)).run s) = .ok (.ok next) after := by
  obtain ⟨_, _, _, post⟩ := reopen_source healthy s prior
  cases hr : (Segmented.reopen (ops healthy)).run s with
  | error _ _ => rw [hr] at post; exact False.elim (post.2 rfl)
  | ok result t =>
    cases result with
    | error => rw [hr] at post; exact False.elim (post.2 rfl)
    | ok v => exact ⟨v, t, rfl⟩

end WalRecoverySlice.Segmented.Model
