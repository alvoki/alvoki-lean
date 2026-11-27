import Alvoki.Experiments.WAL.Segmented.Proofs.Model

namespace WalRecoverySlice.Segmented.Model

/-- Checked result of a schedule, with separate postconditions for a return
and an I/O error or interrupted primitive. The trace counter remains private
to the effects interpreter and never constrains the choice at its next step. -/
def DiskPost {α} (ok : α → Disk → Prop) (stop : Disk → Prop) : Result α → Prop
  | .ok (.ok v) s => ok v s.disk
  | .ok (.error _) s | .error _ s => stop s.disk

theorem bindPost {α β} {a : M α} {b : α → M β} {s : State} {P : α → Disk → Prop}
    {Q : β → Disk → Prop} {F : Disk → Prop} (one : DiskPost P F (a.run s))
    (next : ∀ v t, P v t.disk → DiskPost Q F ((b v).run t)) :
    DiskPost Q F ((a >>= b).run s) := by
  change DiskPost P F (a s) at one
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind]
  cases h : a s with
  | error _ t => rw [h] at one; exact one
  | ok x t => cases x with
    | error _ => rw [h] at one; exact one
    | ok v => rw [h] at one; exact next v t one

theorem namespacePost (e : NamespaceEffect) (change : Disk → Bool → Disk) (s : State)
    {P : Unit → Disk → Prop} {F : Disk → Prop} (old : F s.disk)
    (stopped : ∀ persists, F (change s.disk persists))
    (done : ∀ persists, P () (change s.disk persists)) :
    DiskPost P F (namespaceChange e change s) := by
  cases e with
  | before fault => cases fault <;> exact old
  | after p f => cases f with
    | none => exact done p
    | some fault => cases fault <;> exact stopped p

theorem barrierPost (e : Primitive) (change : Disk → Disk) (s : State)
    {P : Unit → Disk → Prop} {F : Disk → Prop} (old : F s.disk)
    (stopped : F (change s.disk)) (done : P () (change s.disk)) :
    DiskPost P F (barrier e change s) := by
  cases e with
  | before fault => cases fault <;> exact old
  | after f => cases f with
    | none => exact done
    | some fault => cases fault <;> exact stopped

def Disk.syncedControlStage (d : Disk) (c : Control) := (d.stage c false).syncStage

def Disk.published (d : Disk) (c : Control) := ((d.syncedControlStage c).rename c false).syncRoot

/-- Exact effect prefix of writing, syncing and publishing a new control. -/
inductive PublishCut (d : Disk) (c : Control) : Disk → Prop where
  | before : PublishCut d c d
  | staged (persist : Bool) : PublishCut d c (d.stage c persist)
  | synced : PublishCut d c (d.syncedControlStage c)
  | renamed (persist : Bool) : PublishCut d c ((d.syncedControlStage c).rename c persist)
  | settled : PublishCut d c (d.published c)

theorem publish_cases (effects : Effects) (c : Control) (s : State) :
    DiskPost (fun _ d => d = s.disk.published c) (PublishCut s.disk c)
      ((Segmented.publish (ops effects) c).run s) := by
  unfold Segmented.publish
  apply bindPost (P := fun _ d => ∃ p, d = s.disk.stage c p)
  · apply namespacePost (effects.stage s.step) (fun d flag => d.stage c flag) s
    · exact .before
    · exact PublishCut.staged
    · exact fun p => ⟨p, rfl⟩
  intro _ t ⟨p, staged⟩
  apply bindPost (P := fun _ d => d = s.disk.syncedControlStage c)
  · apply barrierPost
    · rw [staged]; exact .staged p
    · rw [staged]; exact .synced
    · rw [staged]; rfl
  intro _ u synced
  apply bindPost (P := fun _ d => ∃ p, d = (s.disk.syncedControlStage c).rename c p)
  · change DiskPost _ _ (match u.disk.staged with | none => _ | some _ => _)
    have selected : u.disk.staged = some c := by rw [synced]; rfl
    rw [selected]
    apply namespacePost
    · rw [synced]; exact .synced
    · intro persist; rw [synced]; exact .renamed persist
    · intro persist; exact ⟨persist, by rw [synced]⟩
  intro _ v ⟨persist, renamed⟩
  apply barrierPost
  · rw [renamed]; exact .renamed persist
  · rw [renamed]; exact .settled
  · rw [renamed]; rfl

/-- The new control can be selected only after the rename. Before it the
original live and durable controls remain paired. A successful directory
barrier also preserves whichever file bindings were live at that instant. -/
theorem PublishCut.frames {d c reached} (cut : PublishCut d c reached) :
    reached.segment = d.segment ∧ reached.cursor = d.cursor ∧ reached.liveNames = d.liveNames ∧
    (reached.durableNames = d.durableNames ∨ reached.durableNames = d.liveNames) ∧
    ((reached.liveControl = d.liveControl ∧ reached.durableControl = d.durableControl) ∨
      (reached.liveControl = some c ∧ (reached.durableControl = d.durableControl ∨ reached.durableControl = some c))) := by
  cases cut with
  | renamed persist => cases persist <;> simp [Disk.syncedControlStage, Disk.rename, Disk.stage, Disk.syncStage]
  | _ => simp [Disk.syncedControlStage, Disk.published, Disk.rename, Disk.stage, Disk.syncStage, Disk.syncRoot]

def successor (ss : Session) : Control := {ss.control with active := ss.control.active + 1}

def Disk.preparedSuccessor (d : Disk) (ss : Session) := (d.prepare (successor ss).active false).syncRoot

/-- A stopped rotation has either not published or reached a cut of
publication from a *durably named* fresh successor. -/
inductive RotationCut (d : Disk) (ss : Session) : Disk → Prop where
  | before : RotationCut d ss d
  | prepared (persist : Bool) : RotationCut d ss (d.prepare (successor ss).active persist)
  | publishing {after} : PublishCut (d.preparedSuccessor ss) (successor ss) after → RotationCut d ss after

theorem rotateIfFull_cases (e : Effects) (ss : Session) (s : State) :
    DiskPost (fun pair after =>
      if ss.activeCount = ss.control.capacity then
        pair = ((successor ss), 0) ∧ after = (s.disk.preparedSuccessor ss).published (successor ss)
      else pair = (ss.control, ss.activeCount) ∧ after = s.disk)
      (RotationCut s.disk ss) ((Segmented.rotateIfFull (ops e) ss).run s) := by
  by_cases full : ss.activeCount = ss.control.capacity
  · simp only [Segmented.rotateIfFull, full, ↓reduceIte]
    apply bindPost (P := fun _ d => ∃ p, d = s.disk.prepare (successor ss).active p)
    · apply namespacePost (e.prepare s.step (successor ss).active) (fun d flag => d.prepare (successor ss).active flag) s
      · exact .before
      · exact RotationCut.prepared
      · exact fun p => ⟨p, rfl⟩
    intro _ t ⟨p, prepared⟩
    apply bindPost (P := fun _ d => d = s.disk.preparedSuccessor ss)
    · apply barrierPost
      · rw [prepared]; exact .prepared p
      · rw [prepared]; exact .publishing .before
      · rw [prepared]; rfl
    intro _ u named
    have h := publish_cases e (successor ss) u
    apply bindPost (P := fun _ d => d = u.disk.published (successor ss))
    · change DiskPost _ _ ((Segmented.publish (ops e) (successor ss)).run u)
      generalize hres : (Segmented.publish (ops e) (successor ss)).run u = res at h ⊢
      cases res with
      | error _ t => exact RotationCut.publishing (named ▸ h)
      | ok x t => cases x with
        | error _ => exact RotationCut.publishing (named ▸ h)
        | ok _ => exact h
    intro _ v published
    exact ⟨rfl, published.trans (congrArg (fun d => Disk.published d (successor ss)) named)⟩
  · simp only [Segmented.rotateIfFull, full, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem successor_ne (ss : Session) : ss.control ≠ successor ss := by
  intro h
  have eqn := congrArg Control.active h
  change ss.control.active = ss.control.active + 1 at eqn
  omega

theorem RotationCut.retains {d ss after} (cut : RotationCut d ss after)
    (settled : d.durableNames = d.liveNames) (id : Nat) (old : id ≠ (successor ss).active) :
    after.segment id = d.segment id ∧ after.cursor id = d.cursor id ∧
      (id ∈ after.liveNames ↔ id ∈ d.liveNames) ∧ (id ∈ after.durableNames ↔ id ∈ d.durableNames) := by
  cases cut with
  | before => simp
  | prepared flag =>
    cases flag <;> simp [Disk.prepare, Disk.setSegment, old]
  | publishing cut =>
    obtain ⟨seg, curs, live, durable, _⟩ := cut.frames
    rw [seg, curs, live]
    rcases durable with eqn | eqn <;> rw [eqn] <;>
      simp [Disk.preparedSuccessor, Disk.prepare, Disk.setSegment, Disk.syncRoot, old, settled]

/-- Whichever namespace a restart observes, selecting the successor implies
that its fresh image and cursor are available through both directory maps. -/
theorem RotationCut.successor_ready {d ss after} (cut : RotationCut d ss after)
    (live : d.liveControl = some ss.control) (disk : d.durableControl = some ss.control)
    (selected : after.liveControl = some (successor ss) ∨ after.durableControl = some (successor ss)) :
    (successor ss).active ∈ after.liveNames ∧ (successor ss).active ∈ after.durableNames ∧
      after.segment (successor ss).active = Persistence.freshImage ∧ after.cursor (successor ss).active = {} := by
  cases cut with
  | before => simp [live, disk, successor_ne ss] at selected
  | prepared flag => simp [Disk.prepare, Disk.setSegment, live, disk, successor_ne ss] at selected
  | publishing cut =>
    obtain ⟨segments, cursors, names, durable, _⟩ := cut.frames
    rw [segments, cursors, names]
    rcases durable with eqn | eqn <;> rw [eqn] <;>
      simp [Disk.preparedSuccessor, Disk.prepare, Disk.syncRoot, Disk.setSegment]

end WalRecoverySlice.Segmented.Model
