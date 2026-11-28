import Alvoki.Experiments.WAL.Segmented.Proofs.CutRuntime

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Model (Disk)
open AppendIO (LocalIO Active sourceState inputContext issuedWorld installedWorld)
open Alvoki.NativePost (W IOReturns)

inductive PublicStop (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store)
    (session : Session) (batch : Bytes) (w : W) (stop : Stop) (d : Disk) : Prop where
  | lock : stop (liftM mutex.lock : IO Unit) w d → PublicStop cell mutex store session batch w stop d
  | read : stop (cell.get : IO _) (mutex.lock w).state d → PublicStop cell mutex store session batch w stop d
  | poison : stop (cell.set (.poisoned store) : IO _) ((cell.get : BaseIO _) (mutex.lock w).state).state d →
      PublicStop cell mutex store session batch w stop d
  | worker : ((sites store session stop).appendSession session batch).cuts
      (issuedWorld cell mutex store w) d → PublicStop cell mutex store session batch w stop d
  | install : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (cell.set (.ready store next) : IO _) t d → PublicStop cell mutex store session batch w stop d
  | leave : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (liftM mutex.unlock : IO Unit) (installedWorld cell store next t) d → PublicStop cell mutex store session batch w stop d
  | fail : store.appendSession session batch (issuedWorld cell mutex store w) = .error e t →
      stop (liftM mutex.unlock : IO Unit) t d → PublicStop cell mutex store session batch w stop d

/-- The physical pending state is already available upon ordinary worker
return, before updating the outer WAL phase or releasing its mutex. -/
private theorem afterWorker {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (active : Active mem heap wal reg w) (q : Q w)
    (size : batch.length ≤ 32) (room : reg.session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    let retry t := Recoverable reg.session.view (some (.append batch)) (disk t)
    IOReturns (reg.store.appendSession reg.session batch) (issuedWorld op.cell op.mutex reg.store w)
      (fun _ t => retry t) retry := by
  obtain ⟨phase,ready,typed⟩ := op.begin active q
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk w reg phase
  let begin := issuedWorld op.cell op.mutex reg.store w
  have bounds := Model.successor_controlRepresentable ready.installed room
  have tied := AppendIO.appendSession (w := begin) (s := s) op.reports reg.store reg.session size room
    (done := c.Done batch) (bad := c.Failed)
    (fun ne => (op.inside phase ne typed).assemble typed.1 rfl ne)
    (fun full => (op.rotate phase full typed).assemble typed bounds.1 bounds.2 full linux)
  let r := op.reports
  have model := Model.nativeAppendModel_refines reg.store.root r.directory r.removal r.effects r.create r.close
    reg.session (r.append reg.session.control.policy) s ready rfl size room linux
  dsimp only at model
  unfold AppendIO.At at tied
  dsimp only
  change IOReturns (reg.store.appendSession reg.session batch) begin _ _
  unfold IOReturns
  cases ar : reg.store.appendSession reg.session batch begin <;> cases mr : (r.action reg.store reg.session).run s with
    | error => rw [ar,mr] at tied; contradiction
    | ok response after =>
      rw [ar,mr] at tied
      unfold AppendIO.Reports.action at mr
      rw [mr] at model
      cases response <;> try contradiction
      first
      | obtain ⟨shape,rfl,child,base,_⟩ := tied
        apply base.2.1.recoverable
        exact (Model.appendLostAck model.2.1.installed model.1.2.1).1
      | obtain ⟨slot,base,_⟩ := tied
        exact base.2.1.recoverable model.1

theorem recoverPublic {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (prim : CutRuntime disk reg.store reg.session stop)
    (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : PublicStop op.cell op.mutex reg.store reg.session batch w stop d) : Recoverable reg.session.view (some (.append batch)) d := by
  obtain ⟨_,ready,_⟩ := op.begin active q
  have prior : Recoverable reg.session.view (some (.append batch)) (disk w) := ready.installed.offline (.inl rfl)
  have returned := afterWorker op active q size room linux
  dsimp only at returned
  cases cut with
  | lock cut => exact (prim.volatile.stopped _ (.lock _) _ _ cut).recoverable prior
  | read cut =>
    exact ((prim.volatile.lock op.mutex w).trans (prim.volatile.stopped _ (.get _) _ _ cut)).recoverable prior
  | poison cut =>
    exact (((prim.volatile.lock op.mutex w).trans (prim.volatile.get op.cell _)).trans
      (prim.volatile.stopped _ (.set _ _) _ _ cut)).recoverable prior
  | worker cut => exact recoverBody op prim active q size room linux cut
  | install ran cut =>
    rw [IOReturns,ran] at returned
    exact (prim.volatile.stopped _ (.set _ _) _ _ cut).recoverable returned
  | leave ran cut =>
    rw [IOReturns,ran] at returned
    exact ((prim.volatile.set op.cell _ _).trans (prim.volatile.stopped _ (.leave _) _ _ cut)).recoverable returned
  | fail ran cut =>
    rw [IOReturns,ran] at returned
    exact (prim.volatile.stopped _ (.leave _) _ _ cut).recoverable returned

end WalRecoverySlice.Segmented.Native.AppendCut
