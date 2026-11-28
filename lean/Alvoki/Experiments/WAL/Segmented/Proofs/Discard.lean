import Alvoki.Experiments.WAL.Segmented.Proofs.Collect
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

/-! Release authority controls when reclamation stops protecting old files. -/

namespace WalRecoverySlice.Segmented

open Model (Disk State DiskPost PublishCut CollectionFrame)

private theorem preservePublication {c h before after next} (ready : ReadyLayout c h before)
    (cut : PublishCut before next after) : ReadyLayout c h after := by
  obtain ⟨segment, cursor, names, durable, _⟩ := cut.frames
  apply ready.frame
  · intro id selected
    obtain ⟨live, disk⟩ := ready.layout.names id selected
    rw [names]
    exact ⟨live, durable.elim (fun same => same.symm ▸ disk) (fun same => same.symm ▸ live)⟩
  · intro id _
    exact congrFun segment id
  · exact congrFun cursor c.active

private theorem preserveCollection {c h before after} (ready : ReadyLayout c h before)
    (frames : CollectionFrame c.firstNeeded before after) : ReadyLayout c h after := by
  apply ready.frame
  · intro id selected
    obtain ⟨live, durable⟩ := ready.layout.names id selected
    exact frames.keepsNamed id selected.1 live durable
  · intro id _
    exact congrFun frames.segment id
  · exact congrFun frames.cursor c.active

private theorem discardApplied {v : Contract.View} {k : Nat} (fits : k ≤ v.tail) :
    (Contract.Request.discardThrough k).apply v = some (v.discardThrough k) := by
  simp [Contract.Request.apply, fits]

/-- The source release publishes the new frontier before the first unlink.
If the call stops during publication, either actual control can be reopened.
If cleanup has begun, the new frontier is already durable. -/
theorem discard_refines (effects : Model.Effects) (session : Session) (k : Nat) (state : State)
    (installed : Installed session state.disk) :
    DiskPost
      (fun next disk => Installed next disk ∧ (Contract.Request.discardThrough k).apply session.view = some next.view)
      (Recoverable session.view (some (.discardThrough k)))
      ((discardThrough (Model.ops effects) session k).run state) := by
  obtain ⟨history, shaped, ready, live, durable⟩ := installed
  have entry : Installed session state.disk := ⟨history, shaped, ready, live, durable⟩
  have view : session.view = historyView session.control history := congrArg Session.view shaped
  have seek : session.view.tail = history.length := by rw [view, historyView_tail ready.layout.discardedFits]
  have base : session.view.base = session.control.discarded := congrArg Contract.View.base view
  by_cases beyond : session.view.tail < k
  · simp only [discardThrough, discardControl, bind_assoc, pure_bind, beyond, ↓reduceIte]
    exact entry.offline (request := some (.discardThrough k)) (known := session.view) (.inl rfl)
  · have fits : k ≤ session.view.tail := Nat.le_of_not_gt beyond
    by_cases unchanged : k ≤ session.view.base
    · have same : session.view.discardThrough k = session.view := by
        simp only [Contract.View.discardThrough, Nat.max_eq_right unchanged, Nat.sub_eq_zero_of_le unchanged,
          List.drop_zero]
      simpa [discardThrough, discardControl, bind_assoc, pure_bind, beyond, unchanged, DiskPost, Pure.pure, ExceptT.pure, EStateM.pure, same] using
        And.intro entry (discardApplied fits |>.trans (congrArg some same))
    · let next := {session.control with discarded := k}
      have advance : session.control.discarded ≤ k := by rw [← base]; omega
      have nextValid : k ≤ history.length := seek ▸ fits
      have nextView : historyView next history = session.view.discardThrough k := by
        rw [view]
        exact historyView_release advance
      have applied : (Contract.Request.discardThrough k).apply session.view = some (historyView next history) := by
        rw [nextView]
        exact discardApplied fits
      have oldAllowed : PermittedView session.view (some (.discardThrough k)) (historyView session.control history) :=
        .inl view.symm
      have newAllowed : PermittedView session.view (some (.discardThrough k)) (historyView next history) :=
        .inr applied
      have recoveryDuring {after : Disk} (cut : PublishCut state.disk next after) :
          Recoverable session.view (some (.discardThrough k)) after := by
        have oldReady := preservePublication ready cut
        have newReady : ReadyLayout next history after := oldReady.release advance nextValid
        obtain ⟨_, _, _, _, outcomes⟩ := cut.frames
        rcases outcomes with ⟨liveSame, durableSame⟩ | ⟨liveNew, durableChoice⟩
        · exact ⟨⟨session.control, liveSame.trans live, oldReady.choice oldAllowed⟩,
            ⟨session.control, durableSame.trans durable, oldReady.choice oldAllowed⟩⟩
        · refine ⟨⟨next, liveNew, newReady.choice newAllowed⟩, ?_⟩
          rcases durableChoice with old | new
          · exact ⟨session.control, old.trans durable, oldReady.choice oldAllowed⟩
          · exact ⟨next, new, newReady.choice newAllowed⟩
      simp only [discardThrough, discardControl, bind_assoc, pure_bind, beyond, unchanged, ↓reduceIte]
      apply Model.bindPost (P := fun _ d => d = state.disk.published next)
      · have cases := Model.publish_cases effects next state
        change DiskPost _ _ ((publish ((Model.ops effects).toRootOps) next).run state)
        cases result : (publish ((Model.ops effects).toRootOps) next).run state with
        | error _ s =>
          rw [result] at cases
          exact recoveryDuring cases
        | ok answer s =>
          rw [result] at cases
          cases answer with
          | error _ => exact recoveryDuring cases
          | ok _ => exact cases
      intro _ published exactDisk
      have layout : ReadyLayout next history published.disk := by
        rw [exactDisk]
        exact preservePublication (ready.release advance nextValid) .settled
      have liveNew : published.disk.liveControl = some next := by rw [exactDisk]; rfl
      have diskNew : published.disk.durableControl = some next := by rw [exactDisk]; rfl
      have install {after : Disk} (collected : CollectionFrame next.firstNeeded published.disk after) :
          Installed (sessionOf next history) after := by
        refine ⟨history, rfl, preserveCollection layout collected, collected.liveControl.trans liveNew, ?_⟩
        exact collected.durableControl.elim (fun same => same.trans diskNew) (fun same => same.trans liveNew)
      apply Model.bindPost (P := fun _ disk => Installed (sessionOf next history) disk)
      · have cases := Model.collect_cases effects next published
        change DiskPost _ _ ((collect ((Model.ops effects).toRootOps) next).run published)
        cases result : (collect ((Model.ops effects).toRootOps) next).run published with
        | error _ s =>
          rw [result] at cases
          exact (install cases).offline newAllowed
        | ok answer s =>
          rw [result] at cases
          cases answer with
          | error _ => exact (install cases).offline newAllowed
          | ok _ => exact install cases.1
      intro _ final installedNext
      have count : session.activeCount = (segmentHistory session.control.capacity session.control.active history).length :=
        congrArg Session.activeCount shaped
      change Installed {session with control := next, view := session.view.discardThrough k} final.disk ∧ _
      have returned : {session with control := next, view := session.view.discardThrough k} = sessionOf next history := by
        rw [← nextView]
        change Session.mk next session.activeCount (historyView next history) =
          Session.mk next (segmentHistory next.capacity next.active history).length (historyView next history)
        rw [count]
      rw [returned]
      exact ⟨installedNext, applied⟩

end WalRecoverySlice.Segmented
