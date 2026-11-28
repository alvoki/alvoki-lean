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

/-- Local effects of an open on one named child. Both interpreters construct
these facts for the actual returned result before composing the root schedule. -/
structure OpenChildEffects (call : Policy → Nat → M (List Bytes)) (healthyCall : Prop) : Prop where
  frame : ∀ policy id (s : State), id ∈ s.disk.liveNames →
    ∃ image cursor, (reached ((call policy id).run s)).disk = s.disk.setSegment id image cursor
  settled : ∀ {policy id s history}, id ∈ s.disk.liveNames →
    Child.Settled policy (s.disk.segment id) history →
    (∀ b ∈ history, b.length ≤ 32) → history.length ≤ 255 →
    let r := (call policy id).run s
    (reached r).disk.segment id = s.disk.segment id ∧
      (∀ batches, returned r = some batches → batches = history)
  dirty : ∀ {policy id s known pending}, id ∈ s.disk.liveNames →
    Child.Recoverable policy known pending (s.disk.segment id) →
    let r := (call policy id).run s
    Child.Recoverable policy known pending ((reached r).disk.segment id) ∧
      ∀ batches, returned r = some batches →
        WalRecoverySlice.Contract.Permitted known pending batches ∧
        Child.Installed policy ((reached r).disk.segment id) ((reached r).disk.cursor id) batches
  selected : ∀ {policy id s batches known pending}, id ∈ s.disk.liveNames →
    Child.Recoverable policy known pending (s.disk.segment id) →
    Child.Selects policy (s.disk.segment id) batches →
    ∀ observed, returned ((call policy id).run s) = some observed → observed = batches
  healthy : ∀ {policy id s known pending}, id ∈ s.disk.liveNames →
    Child.Recoverable policy known pending (s.disk.segment id) →
    healthyCall → ∃ batches, returned ((call policy id).run s) = some batches

private theorem modelChildEffects (e : Effects) : OpenChildEffects (ops e).openSegment (e = healthy) where
  frame _ _ _ named := openSegment_frame e _ named
  settled named entry bounded fits :=
    let facts := openSegment_settled e named entry bounded fits
    ⟨facts.1, fun batches observed => (facts.2 batches observed).1⟩
  dirty named entry := openSegment_dirty e named entry
  selected named _ chosen _ observed := openSegment_selected e named chosen observed
  healthy named entry h := by subst e; exact openSegment_healthy named entry

private theorem sealed_step {c h p active} {call} {healthyCall : Prop}
    (effects : OpenChildEffects call healthyCall) {s : State} {id : Nat}
    (o : Opening c h p active s.disk) (low : c.firstNeeded ≤ id) (lt : id < c.active) :
    let result := (call c.policy id).run s
    Opening c h p active (reached result).disk ∧
      (∀ v, returned result = some v → v = segmentHistory c.capacity id h) ∧
      (healthyCall → ∃ v, returned result = some v) := by
  have selects : c.selects id := ⟨low, Nat.le_of_lt lt⟩
  have named := (o.selected.layout.names id selects).1
  have settled := o.selected.layout.sealed id selects lt
  have bs := segmentHistory_bounded o.selected.layout id
  have fits := Nat.le_trans (segmentHistory_fits c.capacity id h) o.selected.layout.capacityFits
  have result := effects.settled named settled bs fits
  dsimp only at result ⊢
  obtain ⟨image, cursor, frame⟩ := effects.frame c.policy id s named
  have files (i : Nat) : (reached ((call c.policy id).run s)).disk.segment i = s.disk.segment i := by
    by_cases same : i = id
    · subst i; exact result.1
    · rw [frame]; exact Disk.setSegment_other _ _ _ same
  exact ⟨⟨by rw [frame]; exact o.live, by rw [frame]; exact o.durable,
    o.selected.frame (by rw [frame]; exact o.selected.layout.names) (fun i _ => files i),
    (files _).trans o.sameActive⟩, result.2, effects.healthy named (settled.recoverable bs fits)⟩

private structure Opened (c : Control) (history : List Bytes) (d : Disk) : Prop where
  ready : ReadyLayout c history d
  live : d.liveControl = some c
  durable : d.durableControl = some c

private theorem Opened.recoverable {c final d known req} (o : Opened c final d)
    (perm : PermittedView known req (historyView c final)) : Recoverable known req d :=
  ⟨⟨c, o.live, o.ready.choice perm⟩, ⟨c, o.durable, o.ready.choice perm⟩⟩

private theorem active_step {c h p active final known req} {call} {healthyCall : Prop}
    (effects : OpenChildEffects call healthyCall) {s : State}
    (o : Opening c h p active s.disk)
    (allow : ∀ v, WalRecoverySlice.Contract.Permitted h p v → PermittedView known req (historyView c v))
    (layout : ∀ disk, Layout c h disk → Layout c final disk)
    (canonical : Child.Selects c.policy active (segmentHistory c.capacity c.active final)) :
    readOutcome (fun t => Opened c final t.disk)
      (fun t => Recoverable known req t.disk ∧ ¬ healthyCall)
      (segmentHistory c.capacity c.active final) ((call c.policy c.active).run s) := by
  let id := c.active
  let out := (call c.policy id).run s
  let later := (reached out).disk
  have named := (o.selected.layout.names id c.selectsActive).1
  obtain ⟨image, cursor, frame⟩ := effects.frame c.policy id s named
  change later = _ at frame
  have ⟨retry, success⟩ := effects.dirty named o.selected.active
  have names : ∀ i, c.selects i → i ∈ later.liveNames ∧ i ∈ later.durableNames := by
    rw [frame]; exact o.selected.layout.names
  have closed (i : Nat) (_ : c.selects i) (lt : i < id) : later.segment i = s.disk.segment i := by
    rw [frame]; exact Disk.setSegment_other _ _ _ (Nat.ne_of_lt lt)
  have oldLayout := o.selected.layout.frame names closed
  have lh : later.liveControl = some c := by rw [frame]; exact o.live
  have dh : later.durableControl = some c := by rw [frame]; exact o.durable
  apply outcome_reached
  · intro v ack
    change returned out = some v at ack
    obtain ⟨_, installed⟩ := success v ack
    have chosen := effects.selected named o.selected.active (o.sameActive ▸ canonical) v ack
    rw [chosen] at installed
    exact ⟨⟨⟨layout later oldLayout, installed⟩, lh, dh⟩, chosen⟩
  · intro no
    have available : ¬ healthyCall := by
      intro he
      obtain ⟨v, ret⟩ := effects.healthy named o.selected.active he
      rw [no] at ret
      contradiction
    let r : Readable c h p later := ⟨oldLayout, o.selected.room, retry⟩
    have choice : RecoveryChoice known req c later := ⟨h, p, r, allow⟩
    exact ⟨⟨⟨c, lh, choice⟩, ⟨c, dh, choice⟩⟩, available⟩

structure OpenRootEffects (callbacks : Ops M) (healthyRoot : Prop) : Prop where
  collection : CollectionEffects callbacks
  control : ∀ s c, s.disk.liveControl = some c →
    DiskPost (fun value d => value = c ∧ d = s.disk)
      (· = s.disk) (callbacks.readControl.run s)
  syncHealthy : ∀ s, healthyRoot → ∃ t, callbacks.syncRoot.run s = .ok (.ok ()) t
  collectHealthy : ∀ c s, healthyRoot →
    ∃ t, (Segmented.collect callbacks.toRootOps c).run s = .ok (.ok ()) t

private theorem collect_step {c h k req callbacks healthyRoot}
    (root : OpenRootEffects callbacks healthyRoot) (s : State) (o : Opened c h s.disk)
    (permit : PermittedView k req (historyView c h)) :
    readOutcome (fun t => Opened c h t.disk) (fun t => Recoverable k req t.disk ∧ ¬ healthyRoot)
      () ((Segmented.collect callbacks.toRootOps c).run s) := by
  have keep {d} (f : CollectionFrame c.firstNeeded s.disk d) : Opened c h d := by
    refine ⟨o.ready.frame (fun id chosen => ?_) (fun _ _ => by rw [f.segment]) (by rw [f.cursor]),
      f.liveControl.trans o.live, f.durableControl.elim (·.trans o.durable) (·.trans o.live)⟩
    obtain ⟨live, durable⟩ := o.ready.layout.names id chosen
    exact f.keepsNamed id chosen.1 live durable
  have frame := collectWith_cases root.collection c s
  have available := root.collectHealthy c s
  cases eqn : (Segmented.collect callbacks.toRootOps c).run s with
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

def reopenOps (root : Effects) (openChild : Policy → Nat → M (List Bytes)) : Ops M :=
  { ops root with openSegment := openChild }

private theorem collect_reopenOps (root : Effects) (openChild : Policy → Nat → M (List Bytes))
    (c : Control) : Segmented.collect ((reopenOps root openChild).toRootOps) c = Segmented.collect ((ops root).toRootOps) c := rfl

private theorem modelRootEffects (e : Effects) (call : Policy → Nat → M (List Bytes)) :
    OpenRootEffects (reopenOps e call) (e = healthy) where
  collection := ⟨(modelCollectionEffects e).list, (modelCollectionEffects e).remove,
    (modelCollectionEffects e).sync⟩
  control s c found := by
    change DiskPost _ _ (read (e.controlRead s.step) _ s)
    rw [found]
    cases fx : e.controlRead s.step with
    | none => exact ⟨rfl, rfl⟩
    | some fault => cases fault <;> rfl
  syncHealthy s := by rintro rfl; exact ⟨_, rfl⟩
  collectHealthy c s eq := by
    rw [collect_reopenOps]
    subst e
    exact collect_healthy c s

private theorem reopen_prefix_source {k req callbacks healthyRoot healthyCall}
    (root : OpenRootEffects callbacks healthyRoot)
    (effects : OpenChildEffects callbacks.openSegment healthyCall) (s : State)
    (prior : Recoverable k req s.disk) {c h p final}
    (found : s.disk.liveControl = some c) (r : Readable c h p s.disk)
    (allow : ∀ v, WalRecoverySlice.Contract.Permitted h p v → PermittedView k req (historyView c v))
    (finish : Layout c final s.disk)
    (earlier : ∀ id, id < c.active → segmentHistory c.capacity id final = segmentHistory c.capacity id h) :
    readOutcome (fun t => Opening c h p (s.disk.segment c.active) t.disk)
      (fun t => Recoverable k req t.disk ∧ ¬ (healthyRoot ∧ healthyCall ∧
        ∃ c, returned (callbacks.readControl.run s) = some c))
      (c, (segmentWindow c.capacity c.firstNeeded (c.active - c.firstNeeded) final).toArray)
      ((Segmented.reopenPrefix callbacks).run s) := by
  apply reopenPrefix_spec callbacks c final s (fun t => t.disk = s.disk) _ _
    ⟨finish.capacityPositive, finish.capacityFits⟩ finish.lower finish.upper finish.discardedFits
  · have facts := root.control s c found
    cases ran : callbacks.readControl.run s with
    | error => rw [ran] at facts; exact ⟨facts.symm ▸ prior, fun h => by obtain ⟨_, impossible⟩ := h.2.2; cases impossible⟩
    | ok value _ =>
      rw [ran] at facts
      cases value with
      | error => exact ⟨facts.symm ▸ prior, fun h => by obtain ⟨_, impossible⟩ := h.2.2; cases impossible⟩
      | ok => exact ⟨facts.2, facts.1⟩
  · intro t same
    have synced : Opening c h p (s.disk.segment c.active) t.disk.syncRoot := by
      rw [same]
      exact ⟨found, found, r.frame (fun id chosen =>
        ⟨(r.layout.names id chosen).1, (r.layout.names id chosen).1⟩) (fun _ _ => rfl), rfl⟩
    have facts := root.collection.sync t
    have available := root.syncHealthy t
    have failed {d} (h : d = t.disk ∨ d = t.disk.syncRoot) : Recoverable k req d := by
      rcases h with rfl | rfl
      · exact same.symm ▸ prior
      · exact synced.recoverable allow
    cases ran : callbacks.syncRoot.run t with
    | error =>
      rw [ran] at facts available
      exact ⟨failed facts, fun h => by obtain ⟨_, a⟩ := available h.1; cases a⟩
    | ok value _ =>
      rw [ran] at facts available
      cases value with
      | error => exact ⟨failed facts, fun h => by obtain ⟨_, a⟩ := available h.1; cases a⟩
      | ok =>
        refine ⟨?_, rfl⟩
        change Opening _ _ _ _ _
        rw [facts]
        exact synced
  · intro id low lt t o
    have result := sealed_step effects o low lt
    apply outcome_reached
    · exact fun v ret => ⟨result.1, (result.2.1 v ret).trans (earlier id lt).symm⟩
    · intro no
      refine ⟨result.1.recoverable allow, fun eq => ?_⟩
      obtain ⟨v, ok⟩ := result.2.2 eq.2.1
      change returned ((callbacks.openSegment c.policy id).run t) = none at no
      rw [no] at ok
      contradiction

/-- A successful prefix still has the exact live active image and the
single-file precondition for opening its selected child. -/
theorem reopenPrefix_active {k req callbacks healthyRoot healthyCall}
    (root : OpenRootEffects callbacks healthyRoot)
    (effects : OpenChildEffects callbacks.openSegment healthyCall)
    {s t : State} (prior : Recoverable k req s.disk) {c : Control} {sealed : Array Bytes}
    (prefixResult : (Segmented.reopenPrefix callbacks).run s = .ok (.ok (c, sealed)) t) :
    t.disk.liveControl = some c ∧ c.active ∈ t.disk.liveNames ∧
      ∃ known pending, Child.Recoverable c.policy known pending (t.disk.segment c.active) := by
  obtain ⟨original, found, h, p, readable, allowed⟩ := prior.live
  have proof := reopen_prefix_source root effects s prior found readable allowed readable.layout (fun _ _ => rfl)
  rw [prefixResult] at proof
  have same : c = original := congrArg Prod.fst proof.2
  subst c
  exact ⟨proof.1.live, (proof.1.selected.layout.names original.active original.selectsActive).1, _, _, proof.1.selected.active⟩

private theorem reopen_source {k req} {callbacks healthyRoot} (root : OpenRootEffects callbacks healthyRoot) {healthyCall : Prop}
    (effects : OpenChildEffects callbacks.openSegment healthyCall) (s : State) (prior : Recoverable k req s.disk) :
    ∃ c final, PermittedView k req (historyView c final) ∧
      readOutcome (fun t => Opened c final t.disk) (fun t => Recoverable k req t.disk ∧ ¬ (healthyRoot ∧ healthyCall ∧
        ∃ c, returned (callbacks.readControl.run s) = some c))
        (sessionOf c final) ((Segmented.reopen callbacks).run s) := by
  obtain ⟨c, found, h, p, r, allow⟩ := prior.live
  obtain ⟨_, choice, bounded, selected⟩ := r.active.selectedBatches
  obtain ⟨final, permitted, slice, earlier, lift⟩ := resolve_active r choice bounded
  have finish := lift _ r.layout
  refine ⟨c, final, allow final permitted, ?_⟩
  simp only [sessionOf, segmentHistory_active_length finish.upper, historyView]
  apply reopen_spec callbacks c final s
    (fun t => Opening c h p (s.disk.segment c.active) t.disk) (fun t => Opened c final t.disk)
    _ _ finish.lower finish.upper finish.discardedFits
  · exact reopen_prefix_source root effects s prior found r allow finish earlier
  · intro t o
    have proof := active_step effects o allow lift (slice.symm ▸ selected)
    cases h : (callbacks.openSegment c.policy c.active).run t with
    | error => rw [h] at proof; exact ⟨proof.1, fun h => proof.2 h.2.1⟩
    | ok value _ =>
      rw [h] at proof
      cases value with
      | error => exact ⟨proof.1, fun h => proof.2 h.2.1⟩
      | ok => exact proof
  · intro t o
    have proof := collect_step root t o (allow final permitted)
    cases h : (Segmented.collect callbacks.toRootOps c).run t with
    | error => rw [h] at proof; exact ⟨proof.1, fun h => proof.2 h.1⟩
    | ok value _ =>
      rw [h] at proof
      cases value with
      | error => exact ⟨proof.1, fun h => proof.2 h.1⟩
      | ok => exact proof

/-- A successful source reopen installs the exact permitted view. Every reported
I/O error or interruption leaves a state from which the same request can recover. -/
theorem reopenWithEffects_refines {k req callbacks healthyRoot} (root : OpenRootEffects callbacks healthyRoot)
    {healthyCall : Prop}
    (effects : OpenChildEffects callbacks.openSegment healthyCall) (s : State) (prior : Recoverable k req s.disk) :
    DiskPost (fun next disk => Installed next disk ∧ PermittedView k req next.view)
      (Recoverable k req) ((Segmented.reopen callbacks).run s) := by
  obtain ⟨c, final, permit, post⟩ := reopen_source root effects s prior
  cases hr : (Segmented.reopen callbacks).run s with
  | error _ _ => rw [hr] at post; exact post.1
  | ok result t =>
    cases result with
    | error => rw [hr] at post; exact post.1
    | ok next =>
      rw [hr] at post
      obtain ⟨opened, rfl⟩ := post
      exact ⟨⟨final, rfl, opened.ready, opened.live, opened.durable⟩, permit⟩

theorem reopenWithChild_refines {k req} (e : Effects) {call} {healthyCall : Prop}
    (effects : OpenChildEffects call healthyCall) (s : State) (prior : Recoverable k req s.disk) :
    DiskPost (fun next disk => Installed next disk ∧ PermittedView k req next.view)
      (Recoverable k req) ((Segmented.reopen (reopenOps e call)).run s) :=
  reopenWithEffects_refines (modelRootEffects e call) effects s prior

theorem reopen_refines {k req} (e : Effects) (s : State) (prior : Recoverable k req s.disk) :
    DiskPost (fun next disk => Installed next disk ∧ PermittedView k req next.view)
      (Recoverable k req) ((Segmented.reopen (ops e)).run s) :=
  reopenWithChild_refines e (modelChildEffects e) s prior

/-- Local progress premises lift through the same schedule proof as safety. -/
theorem reopenWithEffects_healthy {k req callbacks healthyRoot healthyCall}
    (root : OpenRootEffects callbacks healthyRoot)
    (child : OpenChildEffects callbacks.openSegment healthyCall)
    (s : State) (prior : Recoverable k req s.disk)
    (rootOK : healthyRoot) (childrenOK : healthyCall)
    (readOK : ∃ c, returned (callbacks.readControl.run s) = some c) :
    ∃ next after, (Segmented.reopen callbacks).run s = .ok (.ok next) after := by
  obtain ⟨_, _, _, post⟩ := reopen_source root child s prior
  cases hr : (Segmented.reopen callbacks).run s with
  | error _ _ => rw [hr] at post; exact False.elim (post.2 ⟨rootOK, childrenOK, readOK⟩)
  | ok result t =>
    cases result with
    | error => rw [hr] at post; exact False.elim (post.2 ⟨rootOK, childrenOK, readOK⟩)
    | ok v => exact ⟨v, t, rfl⟩

/-- Once faults cease, the actual source reopen finishes after any permitted prefix. -/
theorem reopen_healthy {k req} (s : State) (prior : Recoverable k req s.disk) :
    ∃ next after, ((Segmented.reopen (ops healthy)).run s) = .ok (.ok next) after := by
  apply reopenWithEffects_healthy (modelRootEffects healthy _) (modelChildEffects healthy) s prior rfl rfl
  obtain ⟨c, found, _⟩ := prior.live
  refine ⟨c, ?_⟩
  change returned (read none (match s.disk.liveControl with
    | some c => .ok c
    | none => .error "missing control") s) = _
  rw [found]
  rfl

end WalRecoverySlice.Segmented.Model
