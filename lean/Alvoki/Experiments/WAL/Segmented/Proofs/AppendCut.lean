import Alvoki.Experiments.WAL.Segmented.Proofs.Execution
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendSlotIO
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendDiskIO

namespace WalRecoverySlice.Segmented.Native.AppendCut

open Model (Disk)
open Alvoki.NativePost (W)

/-- A process exit retains visible bytes. A power cut replaces the visible
namespace and every file by their previously durable images. Either can
follow arbitrary file writebacks between the interruption and restart. -/
def Survivor (d : Disk) (mode : Restart) (after : Disk) : Prop :=
  ∃ persisted, Writebacks d persisted ∧ after = match mode with
    | .processExit => persisted
    | .powerLoss => persisted.powerLoss

theorem Survivor.recoverable (cut : Survivor d mode after) (entry : Recoverable known request d) :
    Recoverable known request after := by
  obtain ⟨saved, writes, rfl⟩ := cut
  cases mode
  · exact writes.recoverable entry
  · exact (writes.recoverable entry).powerLoss

theorem allowPending (entry : Recoverable known none d) (req : Contract.Request) :
    Recoverable known (some req) d := by
  have widen c (old : RecoveryChoice known none c d) : RecoveryChoice known (some req) c d := by
    obtain ⟨hist, bytes, prior, permit⟩ := old
    exact ⟨hist, bytes, prior, fun actual allowed => .inl (by simpa [PermittedView] using permit actual allowed)⟩
  obtain ⟨c, live, old⟩ := entry.live
  obtain ⟨c', durable, other⟩ := entry.durable
  exact ⟨⟨_, live, widen _ old⟩, ⟨_, durable, widen _ other⟩⟩

/-- While the active descriptor writes, only that file's image and
cursor may advance. Untouched files may independently write back. -/
structure ActiveFiles (c : Control) (before after : Disk) : Prop where
  live : after.liveControl = before.liveControl
  durable : after.durableControl = before.durableControl
  names : ∀ i, c.selects i → (i ∈ before.liveNames → i ∈ after.liveNames) ∧
    (i ∈ before.durableNames → i ∈ after.durableNames)
  sealed : ∀ i, c.selects i → i < c.active → after.segment i = before.segment i

theorem ActiveFiles.refl (c : Control) (d : Disk) : ActiveFiles c d d :=
  ⟨rfl, rfl, fun _ _ => ⟨id,id⟩, fun _ _ _ => rfl⟩

theorem ActiveFiles.trans (a : ActiveFiles c before middle) (b : ActiveFiles c middle after) :
    ActiveFiles c before after :=
  ⟨b.live.trans a.live, b.durable.trans a.durable,
   fun i sel => ⟨(b.names i sel).1 ∘ (a.names i sel).1, (b.names i sel).2 ∘ (a.names i sel).2⟩,
   fun i sel lt => (b.sealed i sel lt).trans (a.sealed i sel lt)⟩

theorem ActiveFiles.recoverable (files : ActiveFiles c before after) (entry : ReadyLayout c history before)
    (live : before.liveControl = some c) (durable : before.durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity)
    (position : (historyView c history).tail < Contract.maxPosition)
    (child : Child.Recoverable c.policy (segmentHistory c.capacity c.active history) (some batch)
      (after.segment c.active)) : Recoverable (historyView c history) (some (.append batch)) after := by
  have layout := entry.layout.frame (after := after) (fun i sel =>
    ⟨(files.names i sel).1 (entry.layout.names i sel).1, (files.names i sel).2 (entry.layout.names i sel).2⟩) files.sealed
  have choice : RecoveryChoice (historyView c history) (some (.append batch)) c after := by
    refine ⟨history, some batch, ⟨layout, fun _ => room, child⟩, ?_⟩
    rintro _ (rfl | rfl)
    · exact .inl rfl
    · exact .inr (by simp [Contract.Request.apply, position, historyView_append layout.discardedFits])
  exact ⟨⟨c, files.live.trans live, choice⟩, ⟨c, files.durable.trans durable, choice⟩⟩

/-- Both child append and child close begin at this mutex and its phase
reference. A cut in either instruction needs no result from the read. -/
inductive ChildEntry (h : SingleFile.Handle) (w : W) : {α : Type} → IO α → W → Prop where
  | mutex : h.Binds cell mutex → ChildEntry h w (liftM mutex.lock : IO Unit) w
  | read : h.Binds cell mutex → ChildEntry h w (cell.get : IO _) (mutex.lock w).state

/-- Concrete steps of closing an owned child. All steps other than the
filesystem unlock use the indicated child's mutex or its private phase ref. -/
inductive ClosePoint (h : SingleFile.Handle) (fd : IO.FS.Handle) (w : W)
    (op : AppendIO.CloseOperand h fd w) : {α : Type} → IO α → W → Prop where
  | close : ClosePoint h fd w op (op.cell.set .closed : IO _)
      ((op.cell.get : BaseIO _) (op.mutex.lock w).state).state
  | unlock : ClosePoint h fd w op fd.unlock op.issue
  | leave : ClosePoint h fd w op (liftM op.mutex.unlock) (returnedWorld (fd.unlock op.issue))

inductive CloseSite (h : SingleFile.Handle) (w : W) : {α : Type} → IO α → W → Prop where
  | entry : ChildEntry h w action t → CloseSite h w action t
  | observed (op : AppendIO.CloseOperand h fd w) : ClosePoint h fd w op action t → CloseSite h w action t

/-- The actual old slot is taken before any old-child close instruction.
An unregistered successor close uses the same close-point definition,
starting at the reached error world. -/
inductive OldClose (store : Store) (w : W) : {α : Type} → IO α → W → Prop where
  | detach : OldClose store w (store.active.swap none : IO _) w
  | child {id : Nat} : ((store.active.swap none : BaseIO _) w).val = some (id, h) →
      CloseSite h ((store.active.swap none : BaseIO _) w).state action t → OldClose store w action t

end WalRecoverySlice.Segmented.Native.AppendCut
