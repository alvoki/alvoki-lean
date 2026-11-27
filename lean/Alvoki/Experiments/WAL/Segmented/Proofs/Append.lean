import Alvoki.Experiments.WAL.Segmented.Proofs.Child
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Segmented.Proofs.Rotation

namespace WalRecoverySlice.Segmented

open Model (Disk State DiskPost)
open Persistence (historyCursor)

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
  have child := Model.appendSegment_dirty effects named ready.active ready.clean ready.cursor bounded fits size
  obtain ⟨dirty, markers, success⟩ := child
  let fileRun := effects.appendRun s.step c.active c.policy (s.disk.cursor c.active) p
  have frame := Model.child_reached named fileRun (fun x => x) (fun _ => ())
  have hframe : after = s.disk.setSegment c.active
      (Persistence.reached (fileRun.run (s.disk.segment c.active)))
      ((Persistence.acknowledged (fileRun.run (s.disk.segment c.active))).getD (s.disk.cursor c.active)) := by
    change (Model.reached (Model.child s c.active fileRun _ _)).disk = _
    rw [frame]
    simp
  have layout : Layout c history after := ready.layout.frame
    (fun id selected => by rw [hframe]; exact ready.layout.names id selected)
    (fun id _ sealed => by rw [hframe, Model.Disk.setSegment_other _ _ _ (Nat.ne_of_lt sealed)])
  have authority : after.liveControl = some c ∧ after.durableControl = some c := by
    rw [hframe]; exact ⟨live, durable⟩
  have readable : Readable c history (some p) after :=
    ⟨layout, fun _ => room, dirty, markers⟩
  have choice : RecoveryChoice (historyView c history) (some (.append p)) c after := by
    refine ⟨history, some p, readable, ?_⟩
    intro selected permitted
    rcases permitted with rfl | rfl
    · exact .inl rfl
    · exact .inr (by simp [Contract.Request.apply, historyView_append layout.discardedFits])
  have stop : Recoverable (historyView c history) (some (.append p)) after :=
    ⟨⟨c, authority.1, choice⟩, ⟨c, authority.2, choice⟩⟩
  have ack (ok : Model.returned run = some ()) : ReadyLayout c (history ++ [p]) after := by
    obtain ⟨cursor, installed, clean⟩ := success ok
    have endRows := segmentHistory_append p layout.lower room
    exact ⟨layout.extend p size room, endRows.symm ▸ installed, clean, endRows.symm ▸ cursor⟩
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

end WalRecoverySlice.Segmented
