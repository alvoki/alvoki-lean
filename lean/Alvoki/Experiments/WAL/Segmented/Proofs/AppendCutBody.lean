import Alvoki.Experiments.WAL.Segmented.Proofs.CutSchedule
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRotationIO

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Model (Disk)
open AppendIO (Rotation InPlace Reports Work)
open Alvoki.NativePost (W IOReturns)

/-- Every ordinary edge uses the same returning producer as the public
append. Its intermediate model state is used solely on a returned edge. -/
private theorem observe {act : IO α} {model : AppendIO.M σ β}
    (pair : AppendIO.At act model w s ok bad) (cuts : W → Disk → Prop)
    (abrupt : ∀ d, cuts w d → stop d) :
    Safe ⟨act, cuts⟩ w (fun x t => ∃ y u, ok x y t u) (fun t => ∃ u, bad t u) stop := by
  refine ⟨?_, abrupt⟩
  unfold AppendIO.At at pair
  change IOReturns act _ _ _
  unfold IOReturns
  cases a : act w <;> cases b : model.run s <;> rw [a,b] at pair
  case ok.ok x t y u => cases y <;> first | contradiction | exact ⟨_,_,pair⟩
  case error.ok e t y u => cases y <;> first | contradiction | exact ⟨_,pair⟩
  all_goals contradiction

private theorem safePure {x : α} (h : ok x w) : Safe (pure x) w ok bad stop := ⟨h, fun _ => False.elim⟩
private theorem safeThrow (e : IO.Error) (h : bad w) : Safe (throw e : Observed α) w ok bad stop :=
  ⟨h, fun _ => False.elim⟩

private theorem Safe.weaken (a : Safe act w ok bad stop) (left : ∀ x t, ok x t → ok' x t)
    (right : ∀ t, bad t → bad' t) : Safe act w ok' bad' stop := by
  refine ⟨?_, a.cut⟩
  have h := a.returned
  unfold IOReturns at *
  cases ran : act.run w <;> rw [ran] at h
  · exact left _ _ h
  · exact right _ h

private theorem check (session : Session) (batch : Bytes) (size : batch.length ≤ 32)
    (position : session.view.tail < Contract.maxPosition) :
    checked (checkAppend session batch) = pure () := by
  funext t
  simp [checkAppend, Nat.not_lt_of_ge size, Nat.not_le_of_lt position, checked]
  rfl

structure InPlaceCuts (sites : Sites s) (r : Reports batch) (io : InPlace s session r w st done bad)
    (stop : Disk → Prop) : Prop where
  slot : ∀ d, sites.slotRead w d → stop d
  write : ∀ h t u, io.owned h t u → ∀ d, sites.write h batch t d → stop d

structure RotationCuts (sites : Sites s) (r : Reports batch) (io : Rotation s session r w st done bad)
    (stop : Disk → Prop) : Prop where
  close : ∀ d, sites.oldClose w d → stop d
  prepare : ∀ t u, io.cleared t u →
    ∀ d, sites.prepare session.control.policy (Model.successor session).active t d → stop d
  sync : ∀ h t u, io.prepared h t u → ∀ d, sites.sync t d → stop d
  publish : ∀ h t u, io.synced h t u → ∀ d, sites.publish (Model.successor session) t d → stop d
  write : ∀ h t u, io.published h t u → ∀ d, sites.write h batch t d → stop d
  slot : ∀ h t u, io.written h t u → ∀ d, sites.slotSet (some ((Model.successor session).active,h)) t d → stop d
  unwind : ∀ h t u, io.drop h t u → ∀ d, sites.close h t d → stop d

private theorem cutoff_masked (a : Observed α) (release : Observed Unit)
    (worker : Safe a w ok drop stop)
    (unwind : ∀ t, drop t → ∀ d, release.cuts t d → stop d) :
    ∀ d, (cleanupOnError (error := IO.Error) a release).cuts w d → stop d := by
  rintro d (early | ⟨e,t,ran,later⟩)
  · exact worker.cut d early
  · have reached := worker.returned
    rw [IOReturns,ran] at reached
    rcases later with (cut | ⟨_,_,_,impossible⟩) | ⟨_,_,_,impossible⟩
    · exact unwind t reached d cut
    · contradiction
    · contradiction

/-- Lift the strict native prefix through the full ordinary append source,
including errors followed by an interrupted close of the unpublished child. -/
theorem body (sites : Sites s) (r : Reports batch) (size : batch.length ≤ 32)
    (position : session.view.tail < Contract.maxPosition)
    (little : ∀ _ : session.activeCount ≠ session.control.capacity,
      ∃ op : InPlace s session r w st done bad, InPlaceCuts sites r op stop)
    (big : ∀ _ : session.activeCount = session.control.capacity,
      ∃ op : Rotation s session r w st done bad, RotationCuts sites r op stop) :
    ∀ d, (sites.appendSession session batch).cuts w d → stop d := by
  unfold Sites.appendSession appendOwnedWith
  rw [check session batch size position]
  intro d cut
  rcases cut with early | ⟨_,t,ran,cut⟩
  · contradiction
  obtain rfl : w = t := (EST.Out.ok.inj ran).2
  dsimp only at cut
  by_cases full : session.activeCount = session.control.capacity
  · obtain ⟨io, laws⟩ := big full
    simp only [full, ↓reduceIte] at cut
    let close := observe io.closeOld sites.oldClose laws.close
    rcases cut with early | ⟨_,t,ran,cut⟩
    · exact close.cut _ early
    change s.closeChild w = _ at ran
    have reached := close.returned
    change IOReturns s.closeChild w _ _ at reached
    rw [IOReturns,ran] at reached
    obtain ⟨_,st',cleared⟩ := reached
    unfold withActiveChild at cut
    let made := observe (io.prepare t st' cleared) _ (laws.prepare t st' cleared)
    rcases cut with early | ⟨child,t',ran',cut⟩
    · exact made.cut _ early
    change s.prepareChild session.control.policy (Model.successor session).active t = _ at ran'
    have after := made.returned
    change IOReturns (s.prepareChild _ _) _ _ _ at after
    rw [IOReturns,ran'] at after
    obtain ⟨_,n,_,prepared⟩ := after
    apply cutoff_masked _ _ (drop := fun v => ∃ u, io.drop child v u) (ok := fun _ _ => True) _ _ d cut
    · apply (observe (io.sync child t' n prepared) sites.sync (laws.sync child t' n prepared)).bind
      rintro _ v ⟨_,u,synced⟩
      apply (observe (io.publish child v u synced) _ (laws.publish child v u synced)).bind
      rintro _ v ⟨_,u,published⟩
      apply (observe (io.write child v u published) _ (laws.write child v u published)).bind
      rintro _ v ⟨_,u,written⟩
      apply (observe (io.register child v u written) _ (laws.slot child v u written)).bind
      exact fun _ _ _ => safePure trivial
    · rintro v ⟨u,unwind⟩
      exact laws.unwind child v u unwind
  · obtain ⟨io,laws⟩ := little full
    simp only [full, ↓reduceIte] at cut
    let got := observe io.slot _ laws.slot
    rcases cut with early | ⟨slot,t,ran,cut⟩
    · exact got.cut _ early
    change (s.active.get : IO _) w = _ at ran
    have after := got.returned
    change IOReturns (s.active.get : IO _) _ _ _ at after
    rw [IOReturns,ran] at after
    obtain ⟨_,u,h,rfl,_,held⟩ := after
    dsimp only at cut
    simp only [BEq.rfl, ↓reduceIte] at cut
    rcases cut with early | ⟨_,_,_,impossible⟩
    · exact laws.write h t u held _ early
    · contradiction

end WalRecoverySlice.Segmented.Native.AppendCut
