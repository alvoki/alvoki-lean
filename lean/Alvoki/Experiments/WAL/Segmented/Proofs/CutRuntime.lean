import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCutBody
import Alvoki.Experiments.WAL.Segmented.Proofs.ChildHeapCut
import Alvoki.Experiments.WAL.Segmented.Proofs.CreateCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.PreparedFile
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRuntime
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendPrefixLayout

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Model (Disk successor AppendReady)
open Alvoki.NativePost (W)
open AppendIO (Context Reports Work LocalIO Active inputContext issuedWorld sourceState)

abbrev Stop := ControlCutIO.Stops

/-- This cut carries a witness from the actual child heap prefix, the
append IO worker prefix, or the final phase update after that worker. -/
inductive ChildStop (stop : Stop) (h : SingleFile.Handle) (batch : Bytes) (w : W) (d : Disk) : Prop where
  | entry : ChildEntry h w action u → stop action u d → ChildStop stop h batch w d
  | before (a : ChildCutIO.Operand h w) : ChildCutIO.Before a action u → stop action u d → ChildStop stop h batch w d
  | inside (r : ChildCutIO.Receipt (fun a => stop a) h batch w d) : ChildStop stop h batch w d
  | after (r : ChildCutIO.Complete stop h batch w d) : ChildStop stop h batch w d

def sites (store : Store) (session : Session) (stop : Stop) : Sites store where
  slotRead w d := stop (store.active.get : IO _) w d
  oldClose w d := ∃ (α : Type) (a : IO α) (t : W), OldClose store w a t ∧ stop a t d
  close h w d := ∃ (α : Type) (a : IO α) (t : W), CloseSite h w a t ∧ stop a t d
  prepare _ _ w d := (∃ (p : PrepareCutIO.Point) (t : W) (α : Type) (a : IO α), PrepareCutIO.Prefix (PrepareCutIO.successorDir store session.control) w p t ∧
    PrepareCutIO.Issued (PrepareCutIO.successorDir store session.control) p a ∧ stop a t d) ∨
    ∃ origin leaf t, PrepareCutIO.Prefix (PrepareCutIO.successorDir store session.control) w .create origin ∧
      (CreateCutIO.program (PrepareCutIO.successorDir store session.control) session.control.policy).visits origin leaf t ∧
      stop leaf.action t d
  sync w d := stop (syncHandle store.directory) w d
  publish _ w d := ∃ (p : ControlCutIO.Point) (t : W) (α : Type) (a : IO α) (k : ControlCutIO.OpKind), ControlCutIO.Prefix store session.control w p t ∧
    ControlCutIO.Issued store session.control p a k ∧ stop a t d
  write := ChildStop stop
  slotSet slot w d := stop (store.active.set slot : IO _) w d

/-- A rotation operation is reached by the same concrete store and
session, through the returned prefix of an admitted full-segment append. -/
def Reached (disk : W → Disk) (store : Store) (session : Session) (point : AppendIO.Point) (origin : W) : Prop :=
  ∃ (c : Context disk) (batch : Bytes) (r : Reports batch) (begin : W) (initial : Work) (child : Option SingleFile.Handle) (st : Work),
    c.store = store ∧ c.session = session ∧ AppendReady session initial ∧
    session.activeCount = session.control.capacity ∧ AppendIO.Prefix c r begin initial point child origin st ∧
    AppendIO.PrefixFrame c point child origin st

/-- The receipt belongs to this file only when its phase cell, mutex,
private descriptors and role bindings are the actual acquired objects. -/
structure OwnedOperand (disk : W → Disk) (store : Store) (c : Control) (operand : ChildCutIO.Operand h w) : Prop where
  source : ∃ (mem : ChildMemory disk) (auth : AppendIO.ChildAuthority mem (segmentPath store.root c.active) c.active operand.policy h),
    operand.policy = c.policy ∧ operand.cell = auth.ref ∧ operand.mutex = auth.mutex ∧ operand.fd = auth.fd ∧
      operand.files = auth.files ∧ auth.Live w (.active .lock (SingleFile.appendBindings operand.policy)
        (Persistence.historyCursor operand.known) operand.known)

structure CutRuntime (disk : W → Disk) (store : Store) (session : Session) (stop : Stop) where
  volatile : VolatileIO disk stop
  prepare : ∀ origin, Reached disk store session .cleared origin → Installed session (disk origin) →
    PrepareCutIO.Primitives store session.control origin disk stop
  create : ∀ w, Reached disk store session .cleared w → Installed session (disk w) → ∀ origin,
    PrepareCutIO.Prefix (PrepareCutIO.successorDir store session.control) w .create origin →
    CreateCutIO.Primitives store session.control origin disk stop
  beforePublish : ∀ w, Reached disk store session .prepared w → Installed session (disk w) →
    PrepareIO.PreparedFile disk (successor session).active w → ∀ d, stop (syncHandle store.directory) w d → PrepareCutIO.Frame session.control (disk w) d
  control : ∀ origin, Reached disk store session .synced origin → Installed session (disk origin) →
    PrepareIO.PreparedFile disk (successor session).active origin → (successor session).active ∈ (disk origin).durableNames →
    ControlCutIO.Primitives store session.control origin disk stop
  child : ∀ {h batch w d} (r : ChildCutIO.Receipt (fun a => stop a) h batch w d) c,
    (disk w).liveControl = some c → (disk w).durableControl = some c → OwnedOperand disk store c r.operand → ChildCutIO.Primitives disk c r
  finished : ∀ {h batch w d} (r : ChildCutIO.Complete stop h batch w d) c,
    (disk w).liveControl = some c → (disk w).durableControl = some c → OwnedOperand disk store c r.operand → ChildCutIO.ReturnPrimitives disk c r

private theorem owner {disk : W → Disk} {c : Context disk} (head : Control)
    (same : head.policy = c.session.control.policy) (operand : ChildCutIO.Operand h w)
    (auth : AppendIO.ChildAuthority c.mem (segmentPath c.store.root head.active) head.active c.session.control.policy h)
    (alive : auth.Live w (.active .lock (SingleFile.appendBindings head.policy) pos bs))
    (read : (SingleFile.ConcreteAppend.readAt auth.ref auth.mutex w).val = .active auth.fd auth.files pos bs) :
    OwnedOperand disk c.store head operand ∧ operand.policy = head.policy ∧ operand.known = bs := by
  cases operand with
  | mk policy known cell mutex fd files assembled actual =>
    rcases assembled.unique auth.assembled with ⟨rfl,rfl,rfl⟩
    rcases SingleFile.Phase.active.inj (actual.symm.trans read) with ⟨rfl,rfl,rfl,rfl⟩
    rw [same] at alive
    exact ⟨⟨c.mem, auth, same.symm, rfl, rfl, rfl, rfl, alive⟩,same.symm,rfl⟩

private theorem write {disk : W → Disk} {c : Context disk} {r : Reports batch}
    (prim : CutRuntime disk c.store c.session stop) {head : Control} (sameP : head.policy = c.session.control.policy)
    (steps : AppendIO.WriteSteps c slot head.active h r w st)
    (entry : c.ReadyFile slot head.active h w st)
    (layout : ReadyLayout head hist st.1.disk) (live : st.1.disk.liveControl = some head)
    (durable : st.1.disk.durableControl = some head)
    (phase : st.2 = .active .lock (SingleFile.appendBindings head.policy) (st.1.disk.cursor head.active)
      (segmentHistory head.capacity head.active hist))
    (view : c.session.view = historyView head hist)
    (spare : hist.length < (head.active+1)*head.capacity) (room : c.session.view.tail < Contract.maxPosition)
    (size : batch.length ≤ 32) (cut : ChildStop stop h batch w d) :
    Recoverable c.session.view (some (.append batch)) d := by
  obtain ⟨base,⟨a,held⟩,_⟩ := entry
  have reached := steps.steps a _ _ held (sameP ▸ phase) rfl
  have owns := (fun operand => owner (c := c) head sameP operand a (phase ▸ held) reached.read)
  obtain ⟨valid,l,r',cursorEq⟩ := base.2.1.readyLayout layout live durable
  rw [view]
  have prior : Recoverable (historyView head hist) (some (.append batch)) (disk w) :=
    (show Installed (sessionOf head hist) (disk w) from ⟨hist,rfl,valid,l,r'⟩).offline (.inl rfl)
  cases cut with
  | entry site stopped => exact (prim.volatile.childEntry site stopped).recoverable prior
  | before operand site stopped =>
    have wb := site.writes prim.volatile stopped
    exact wb.recoverable prior
  | inside receipt =>
    obtain ⟨guard,p,known⟩ := owns receipt.operand
    exact ChildCutIO.recoverable receipt (prim.child _ _ l r' guard) p
      known valid l r' spare (view ▸ room) size
  | after receipt =>
    obtain ⟨guard,p,known⟩ := owns receipt.operand
    exact ChildCutIO.returned receipt (prim.finished _ _ l r' guard) prim.volatile known p
      valid l r' spare (view ▸ room) size

theorem recoverBody {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch issued) (prim : CutRuntime disk reg.store reg.session stop)
    (active : Active mem heap wal reg issued) (q : Q issued) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : ((sites reg.store reg.session stop).appendSession reg.session batch).cuts
      (issuedWorld op.cell op.mutex reg.store issued) d) :
    Recoverable reg.session.view (some (.append batch)) d := by
  obtain ⟨phase,ready,held⟩ := op.begin active q
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk issued reg phase
  let w := issuedWorld op.cell op.mutex reg.store issued
  have bounds := Model.successor_controlRepresentable ready.installed room
  apply body (st := s) (done := c.Done batch) (bad := c.Failed) (sites reg.store reg.session stop) op.reports size room _ _ _ cut
  · intro small
    let io := op.inside phase small held
    refine ⟨io.assemble held.1 rfl small, ?_⟩
    constructor
    · intro after stopped
      exact (prim.volatile.stopped _ (.get _) _ _ stopped).recoverable
        ((held.1.2.1.installed ready.installed).offline (.inl rfl))
    · rintro child t st ⟨rfl,rfl,rfl⟩ after stopped
      obtain ⟨hist,shape,layout,l,dur,phaseEq⟩ := ready
      have count := congrArg Session.activeCount shape
      change reg.session.activeCount = (segmentHistory _ _ hist).length at count
      have spare : hist.length < (reg.session.control.active+1)*reg.session.control.capacity := by
        rw [segmentHistory_active_length layout.layout.upper] at count
        have up := layout.layout.upper
        rw [Nat.add_mul,Nat.one_mul] at up ⊢; omega
      exact write (c := c) prim (head := reg.session.control) rfl io.write io.readFrame layout l dur phaseEq
        (congrArg Session.view shape) spare room size stopped
  · intro full
    let io := op.rotate phase full held
    refine ⟨io.assemble held bounds.1 bounds.2 full linux, ?_⟩
    have visit {p child t st} (path : AppendIO.Prefix c op.reports w s p child t st) :
        Reached disk reg.store reg.session p t :=
      ⟨c,batch,op.reports,w,s,child,st,rfl,rfl,ready,full,path,io.frame_of_prefix held ready room full linux path⟩
    constructor
    · rintro after ⟨_,_,_,site,stopped⟩
      exact (prim.volatile.oldClose site stopped).recoverable
        ((held.1.2.1.installed ready.installed).offline (.inl rfl))
    · rintro t st ⟨path,base⟩ after interrupted
      have installed := base.2.1.installed (path.layout ready size room full linux)
      obtain ⟨hist,shape,layout,l,dur⟩ := installed
      have frame : PrepareCutIO.Frame reg.session.control (disk t) after := by
        rcases interrupted with ⟨p,u,_,a,visited,site,stopped⟩ | ⟨v,leaf,u,entered,issued,stopped⟩
        · exact PrepareCutIO.interrupted (prim.prepare t (visit path) ⟨hist,shape,layout,l,dur⟩) visited site stopped
        · exact CreateCutIO.interrupted (prim.prepare t (visit path) ⟨hist,shape,layout,l,dur⟩) entered (prim.create t (visit path) ⟨hist,shape,layout,l,dur⟩ v entered) issued stopped
      exact congrArg Session.view shape ▸ allowPending (frame.survivor layout l dur).2.2.1 _
    · rintro child t st ⟨path,entry,file⟩ after stopped
      have model := path.layout ready size room full linux
      obtain ⟨hist,shape,layout,l,dur⟩ := entry.1.2.1.installed model.1
      exact congrArg Session.view shape ▸ allowPending ((prim.beforePublish t (visit path) ⟨hist,shape,layout,l,dur⟩ file after stopped).survivor layout l dur).2.2.1 _
    · rintro child t st ⟨path,entry,file,named⟩ after ⟨p,u,_,a,k,visited,site,stopped⟩
      have model := path.layout ready size room full linux
      obtain ⟨hist,shape,layout,l,dur⟩ := entry.1.2.1.installed model.1
      have count := (congrArg Session.activeCount shape).symm.trans full
      obtain ⟨names,empty⟩ := file.namedChild named reg.session.control.policy
      have facts := ControlCutIO.survivor (prim.control t (visit path) ⟨hist,shape,layout,l,dur⟩ file named) visited site stopped ⟨l,dur⟩ layout count names empty
      exact congrArg Session.view shape ▸ allowPending facts.2.1 _
    · rintro child t st ⟨path,entry,file,named⟩ after stopped
      obtain ⟨hist,view,layout,l,dur,empty,spare,shape⟩ := path.layout ready size room full linux
      have ceq := layout.active.position
      rw [empty] at ceq
      refine write (c := c) prim (head := successor reg.session) rfl (io.write child t st path entry file named)
        entry layout l dur ?_ view spare room size stopped
      change segmentHistory (successor reg.session).capacity (successor reg.session).active hist = [] at empty
      change st.1.disk.cursor (successor reg.session).active = _ at ceq
      rw [empty,ceq]
      exact shape
    · rintro child t st ⟨path,candidate,live⟩ after stopped
      exact (prim.volatile.stopped _ (.set _ _) _ _ stopped).recoverable
        (candidate.1.2.1.recoverable (path.layout ready size room full linux))
    · rintro child t st ⟨path,candidate⟩ after ⟨_,_,_,site,stopped⟩
      exact (prim.volatile.closeSite site stopped).recoverable
        (candidate.1.2.1.recoverable (path.layout ready size room full linux))

end WalRecoverySlice.Segmented.Native.AppendCut
