import Alvoki.Experiments.WAL.Segmented.Proofs.Child
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Segmented.Proofs.Rotation

namespace WalRecoverySlice.Segmented

open Model (Disk State DiskPost)

/-- Lift the reached active-file image into the directory invariant. Earlier
    sealed files keep their exact bytes and both control names keep their binding. -/
theorem appendActive_refines (effects : Model.Effects) (c : Control) (history : List Bytes)
    (p : Bytes) (s : State) (ready : ReadyLayout c history s.disk)
    (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity) (size : p.length ≤ 32) :
    DiskPost (fun _ after => ReadyLayout c (history ++ [p]) after ∧
      after.liveControl = some c ∧ after.durableControl = some c)
      (Recoverable (historyView c history) (some (.append p)))
      (((Model.ops effects).appendSegment c.policy c.active p).run s) := by
  let run := ((Model.ops effects).appendSegment c.policy c.active p).run s
  let after := (Model.reached run).disk
  let leaf := segmentHistory c.capacity c.active history
  have named := (ready.layout.names _ c.selectsActive).1
  have fits : leaf.length < 255 := by
    have capacity := ready.layout.capacityFits
    have upper := ready.layout.upper
    have lower := ready.layout.lower
    have len := segmentHistory_active_length upper
    change (segmentHistory c.capacity c.active history).length < 255
    rw [len]
    rw [Nat.add_mul, Nat.one_mul] at room
    omega
  have bounded := segmentHistory_bounded ready.layout c.active
  have child := Model.appendSegment_dirty effects named ready.active bounded fits size
  obtain ⟨dirty, success⟩ := child
  obtain ⟨image, cursor, hframe⟩ := Model.appendSegment_frame effects c.policy p named
  change after = _ at hframe
  have layout : Layout c history after := ready.layout.frame
    (fun id selected => by rw [hframe]; exact ready.layout.names id selected)
    (fun id _ sealed => by rw [hframe, Model.Disk.setSegment_other _ _ _ (Nat.ne_of_lt sealed)])
  have authority : after.liveControl = some c ∧ after.durableControl = some c := by
    rw [hframe]; exact ⟨live, durable⟩
  have readable : Readable c history (some p) after :=
    ⟨layout, fun _ => room, dirty⟩
  have choice : RecoveryChoice (historyView c history) (some (.append p)) c after := by
    refine ⟨history, some p, readable, ?_⟩
    intro selected permitted
    rcases permitted with rfl | rfl
    · exact .inl rfl
    · exact .inr (by simp [Contract.Request.apply, historyView_append layout.discardedFits])
  have stop : Recoverable (historyView c history) (some (.append p)) after :=
    ⟨⟨c, authority.1, choice⟩, ⟨c, authority.2, choice⟩⟩
  have ack (ok : Model.returned run = some ()) : ReadyLayout c (history ++ [p]) after := by
    have endRows := segmentHistory_append p layout.lower room
    exact ⟨layout.extend p size room, endRows.symm ▸ success ok⟩
  change DiskPost _ _ run
  cases h : run with
  | error _ => exact (by simpa [DiskPost, after, h, Model.reached] using stop)
  | ok value t =>
    cases value with
    | error _ => exact (by simpa [DiskPost, after, h, Model.reached] using stop)
    | ok u =>
      have good := ack (by simp [h, Model.returned])
      exact (by simpa [DiskPost, after, h, Model.reached] using And.intro good authority)

/-- Refinement of one public source call, including the guard, optional
    rotation, active append and exactly the session returned to the caller. -/
theorem append_refines (effects : Model.Effects) (session : Session) (p : Bytes)
    (state : State) (installed : Installed session state.disk) :
    DiskPost (fun next disk => Installed next disk ∧
      (Contract.Request.append p).apply session.view = some next.view)
      (Recoverable session.view (some (.append p)))
      ((Segmented.append (Model.ops effects) session p).run state) := by
  obtain ⟨history, canonical, ready, live, durable⟩ := installed
  generalize hc : session.control = c at canonical ready live durable
  subst session
  by_cases tooBig : p.length > 32
  · have choice := ready.choice (known := historyView c history) (request := some (.append p)) (.inl rfl)
    simp only [Segmented.append, tooBig, ↓reduceIte]
    exact (show Recoverable (historyView c history) (some (.append p)) state.disk from
      ⟨⟨c, live, choice⟩, ⟨c, durable, choice⟩⟩)
  · simp only [Segmented.append, tooBig, ↓reduceIte]
    apply Model.bindPost (rotateIfFull_refines effects c history p state ready live durable)
    intro pair t mid
    obtain ⟨entry, boundLive, boundDurable, count, view, room⟩ := mid
    have active := appendActive_refines effects pair.1 history p t entry boundLive boundDurable room (by omega)
    rw [view] at active
    apply Model.bindPost active
    intro _ last post
    obtain ⟨newEntry, newLive, newDurable⟩ := post
    have extend := segmentHistory_append p entry.layout.lower room
    have extendedView := historyView_append entry.layout.discardedFits p
    have exactSession :
        (⟨pair.1, pair.2 + 1, (historyView c history).append p⟩ : Session) = sessionOf pair.1 (history ++ [p]) := by
      simp [sessionOf, extend, extendedView, view, count]
    refine And.intro ?_ rfl
    exact ⟨history ++ [p], exactSession, newEntry, newLive, newDurable⟩

/-- The position projected from an acknowledged source append is the next
absolute batch position, including after rotation or prefix release. -/
theorem append_returned_position (effects : Model.Effects) (session : Session) (p : Bytes)
    (state after : State) (next : Session) (installed : Installed session state.disk)
    (returned : (Segmented.append (Model.ops effects) session p).run state = .ok (.ok next) after) :
    next.control.active * next.control.capacity + next.activeCount = session.view.tail + 1 := by
  have result := append_refines effects session p state installed
  rw [returned] at result
  obtain ⟨⟨history, shape, ready, _, _⟩, same⟩ := result
  have lower := ready.layout.lower
  have count := segmentHistory_active_length (active := next.control.active) ready.layout.upper
  have position : next.control.active * next.control.capacity + next.activeCount = next.view.tail := by
    rw [shape]
    simp only [sessionOf] at *
    rw [count, historyView_tail ready.layout.discardedFits]
    omega
  rw [position]
  simp [Contract.Request.apply] at same
  rw [← same]
  simp [Contract.View.tail, Contract.View.append]
  omega

end WalRecoverySlice.Segmented
