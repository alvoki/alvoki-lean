import Alvoki.Experiments.WAL.Segmented.Proofs.PublicAppendCut

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Alvoki.NativePost (W IOReturns)
open AppendIO (LocalIO Active issuedWorld sourceState inputContext)

/-- Keep the origin of the primitive which did not return. -/
def tagAt (stop : Stop) (last : W) : Stop := fun action w d => w = last ∧ stop action w d

def VolatileFrame (P : W → Prop) : Prop :=
  ∀ {α : Type} (a : IO α), Volatile a → ∀ w, P w → P (returnedWorld (a w))

private theorem baseWorld (a : BaseIO α) (w : W) : returnedWorld ((liftM a : IO α) w) = (a w).state := by
  change returnedWorld (BaseIO.toEIO a w) = _
  cases run : a w
  simp [BaseIO.toEIO, returnedWorld,run]

theorem VolatileFrame.lock (f : VolatileFrame P) (m : Std.BaseMutex) (pw : P w) : P (m.lock w).state := by
  simpa only [baseWorld] using f _ (.lock m) w pw

theorem VolatileFrame.get (f : VolatileFrame P) (ref : IO.Ref α) (pw : P w) :
    P ((ref.get : BaseIO _) w).state := f _ (.get ref) w pw

theorem VolatileFrame.set (f : VolatileFrame P) (ref : IO.Ref α) (v : α) (pw : P w) :
    P ((ref.set v : BaseIO _) w).state := f _ (.set ref v) w pw

theorem VolatileFrame.swap (f : VolatileFrame P) (ref : IO.Ref α) (v : α) (pw : P w) :
    P ((ref.swap v : BaseIO _) w).state := f _ (.swap ref v) w pw

theorem VolatileFrame.entry (f : VolatileFrame P) (site : ChildEntry h w a t) (pw : P w) : P t := by
  cases site with
  | mutex => exact pw
  | read => exact f.lock _ pw

theorem VolatileFrame.close (f : VolatileFrame P) (site : CloseSite h w a t) (pw : P w) : P t := by
  cases site with
  | entry site => exact f.entry site pw
  | closed _ _ => exact f.get _ (f.lock _ pw)
  | observed op site =>
    have read := f.get op.cell (f.lock op.mutex pw)
    have cleared := f.set op.cell .closed read
    cases site with
    | close => exact read
    | unlock => exact cleared
    | leave => exact f _ (.release _) _ cleared

theorem VolatileFrame.oldClose (f : VolatileFrame P) (site : OldClose store w a t) (pw : P w) : P t := by
  cases site with
  | detach => exact pw
  | child _ site => exact f.close site (f.swap store.active none pw)

theorem frameBefore (f : VolatileFrame P) (pw : P w)
    (cut : BeforeWorker cell mutex store w (tagAt stop last) d) : P last := by
  cases cut with
  | lock stopped => exact stopped.1 ▸ pw
  | read stopped => exact stopped.1 ▸ f.lock mutex pw
  | poison stopped => exact stopped.1 ▸ f.get cell (f.lock mutex pw)

private theorem protectedAfter {disk : W → Model.Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (active : Active mem heap wal reg w) (q : Q w)
    (size : batch.length ≤ 32) (room : reg.session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    IOReturns (reg.store.appendSession reg.session batch) (issuedWorld op.cell op.mutex reg.store w)
      (fun _ t => Q t) Q := by
  obtain ⟨phase,ready,typed⟩ := op.begin active q
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk w reg phase
  have bounds := Model.successor_controlRepresentable ready.installed room
  have tied := AppendIO.appendSession (s := s) op.reports reg.store reg.session size room
    (done := c.Done batch) (bad := c.Failed)
    (fun ne => (op.inside phase ne typed).assemble typed.1 rfl ne)
    (fun eq => (op.rotate phase eq typed).assemble typed bounds.1 bounds.2 eq linux)
  unfold AppendIO.At at tied
  unfold IOReturns
  cases ran : reg.store.appendSession reg.session batch (issuedWorld op.cell op.mutex reg.store w) <;>
    cases model : (op.reports.action reg.store reg.session).run s with
    | error => rw [ran,model] at tied; contradiction
    | ok report after =>
      rw [ran,model] at tied
      cases report <;> try contradiction
      first
      | obtain ⟨_,_,_,base,_⟩ := tied; exact base.1
      | obtain ⟨_,base,_⟩ := tied; exact base.1

theorem frameAfterSuccess {disk : W → Model.Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (f : VolatileFrame P) (fromQ : ∀ t, Q t → P t)
    (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : AfterSuccess op.cell op.mutex reg.store reg.session batch w (tagAt stop last) d) : P last := by
  have kept := protectedAfter op active q size room linux
  unfold IOReturns at kept
  cases cut with
  | install ran stopped => rw [ran] at kept; exact stopped.1 ▸ fromQ _ kept
  | leave ran stopped => rw [ran] at kept; exact stopped.1 ▸ f.set op.cell _ (fromQ _ kept)

theorem frameAfterFailure {P : W → Prop} {disk : W → Model.Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (fromQ : ∀ t, Q t → P t)
    (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (run : reg.store.appendSession reg.session batch (issuedWorld op.cell op.mutex reg.store w) = .error e t) : P t := by
  have kept := protectedAfter op active q size room linux
  rw [IOReturns,run] at kept
  exact fromQ t kept

end WalRecoverySlice.Segmented.Native.AppendCut
