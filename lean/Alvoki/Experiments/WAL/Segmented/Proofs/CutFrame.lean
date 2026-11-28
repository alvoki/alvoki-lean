import Alvoki.Experiments.WAL.Segmented.Proofs.CutFrameMemory
import Alvoki.Experiments.WAL.Segmented.Proofs.CutLeafFrames

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Alvoki.NativePost (W)
open AppendIO (Context Reports Work LocalIO Active inputContext issuedWorld sourceState)
open SingleFile.ConcreteAppend (poisonAt)
open SingleFile.ConcreteRecovery (programOps)
open Persistence (historyCursor)

/-- Independent file/namespace state is transported only across returned
instructions. The interrupted primitive itself has not returned. -/
structure FrameRuntime (disk : W → Model.Disk) (store : Store) (session : Session) (P : W → Prop) : Prop where
  volatile : VolatileFrame P
  prepare : ∀ w, Reached disk store session .cleared w →
    CutLeafFrames.Prepare P (PrepareCutIO.successorDir store session.control) w
  create : ∀ w, Reached disk store session .cleared w → ∀ v,
    PrepareCutIO.Prefix (PrepareCutIO.successorDir store session.control) w .create v →
    CutLeafFrames.Create P (PrepareCutIO.successorDir store session.control) session.control.policy v
  control : ∀ w, Reached disk store session .synced w →
    CutLeafFrames.Control P store session.control w
  child : ∀ {h w} (a : ChildCutIO.Operand h w) (c : Control), OwnedOperand disk store c a → ∀ batch,
    CutLeafFrames.ProgramFrame P a.files (appendBatch programOps a.policy (historyCursor a.known) batch)
      (poisonAt a.cell a.fd a.mutex w)

private theorem finishFrame (f : VolatileFrame P) (site : ChildCutIO.After a batch w result action t)
    (start : P w) : P t := by
  cases site with
  | install | failed | rejected => exact start
  | leave => exact f.set a.cell _ start

/-- For an early stop only the mutex or phase-reference instructions
strictly preceding the stopped instruction are traversed. -/
private theorem frameChild {disk : W → Model.Disk} {c : Context disk} {r : Reports batch}
    (frames : FrameRuntime disk c.store c.session P) {head : Control} (same : head.policy = c.session.control.policy)
    (steps : AppendIO.WriteSteps c slot head.active h r w st) (held : c.ReadyFile slot head.active h w st)
    (canonical : ∃ bs, st.2 = .active .lock (SingleFile.appendBindings head.policy)
      (Persistence.historyCursor bs) bs)
    (pw : P w) (cut : Nonempty (ChildCutIO.Operand h w) → ChildStop (tagAt stop last) h batch w d) : P last := by
  have before (a : ChildCutIO.Operand h w) : P (poisonAt a.cell a.fd a.mutex w) :=
    VolatileFrame.set frames.volatile a.cell _ (VolatileFrame.get frames.volatile a.cell (VolatileFrame.lock frames.volatile a.mutex pw))
  have owns (operand : ChildCutIO.Operand h w) : OwnedOperand disk c.store head operand := by
    obtain ⟨_,⟨auth,live⟩,pos,bs,phase,cursor⟩ := held
    have reached := steps.steps auth pos bs live phase cursor
    have active : auth.Live w (.active .lock (SingleFile.appendBindings head.policy) pos bs) :=
      by rw [same, ← phase]; exact live
    exact (owner (c := c) head same operand auth active reached.read).1
  obtain ⟨old,state⟩ := canonical
  obtain ⟨_,⟨key,live⟩,pos,bs,phase,cursor⟩ := held
  rw [same] at state
  obtain ⟨_,_,rfl,rfl⟩ := SingleFile.Phase.active.inj (phase.symm.trans state)
  have issued := (steps.steps key _ _ live phase cursor).read
  have cut := cut ⟨⟨_,_,_,_,_,_,key.assembled,issued⟩⟩
  cases cut with
  | entry site stopped => exact stopped.1 ▸ VolatileFrame.entry frames.volatile site pw
  | before a site stopped =>
    cases site
    exact stopped.1 ▸ VolatileFrame.get frames.volatile a.cell (VolatileFrame.lock frames.volatile a.mutex pw)
  | inside r =>
    have io := frames.child r.operand head (owns r.operand) batch
    exact r.stopped.1 ▸ CutLeafFrames.atSite io r.path r.site (before r.operand)
  | after r =>
    have io := frames.child r.operand head (owns r.operand) batch
    have kept := CutLeafFrames.terminal io r.path r.last (before r.operand)
    have finish := finishFrame frames.volatile r.site kept
    exact r.cut.1 ▸ finish

theorem frameBody {disk : W → Model.Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch issued) (frames : FrameRuntime disk reg.store reg.session P)
    (fromQ : ∀ t, Q t → P t) (active : Active mem heap wal reg issued) (q : Q issued) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : ((sites reg.store reg.session (tagAt stop last)).appendSession reg.session batch).cuts
      (issuedWorld op.cell op.mutex reg.store issued) d) : P last := by
  obtain ⟨phase,ready,held⟩ := op.begin active q
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk issued reg phase
  let w := issuedWorld op.cell op.mutex reg.store issued
  have bounds := Model.successor_controlRepresentable ready.installed room
  apply body (st := s) (done := c.Done batch) (bad := c.Failed) (stop := fun _ => P last)
    (sites reg.store reg.session (tagAt stop last)) op.reports size room _ _ _ cut
  · intro small
    let io := op.inside phase small held
    refine ⟨io.assemble held.1 rfl small, ?_⟩
    constructor
    · intro d stopped
      exact stopped.1 ▸ fromQ _ held.1.1
    · rintro child t st ⟨rfl,rfl,rfl⟩ d stopped
      obtain ⟨hist,_,layout,_,_,form⟩ := ready
      rw [layout.active.position] at form
      exact frameChild (c := c) frames (head := reg.session.control) rfl io.write io.readFrame ⟨_,form⟩
        (fromQ _ io.readFrame.1.1) stopped
  · intro full
    let io := op.rotate phase full held
    refine ⟨io.assemble held bounds.1 bounds.2 full linux, ?_⟩
    have visit {p child t st} (path : AppendIO.Prefix c op.reports w s p child t st) :
        Reached disk reg.store reg.session p t :=
      ⟨c,batch,op.reports,w,s,child,st,rfl,rfl,ready,full,path,io.frame_of_prefix held ready room full linux path⟩
    constructor
    · rintro d ⟨_,_,_,site,stopped⟩
      exact stopped.1 ▸ VolatileFrame.oldClose frames.volatile site (fromQ _ held.1.1)
    · rintro t st ⟨earlier,base⟩ d interrupted
      have reached := visit earlier
      rcases interrupted with ⟨_,_,_,_,path,_,tag,_⟩ | ⟨v,_,_,path,site,tag,_⟩
      · exact tag ▸ CutLeafFrames.prepare (frames.prepare t reached) path (fromQ t base.1)
      · have created := CutLeafFrames.prepare (frames.prepare t reached) path (fromQ t base.1)
        exact tag ▸ CutLeafFrames.create (frames.create t reached v path) site created
    · rintro child t st ⟨_,entry,_⟩ d cut
      exact cut.1 ▸ fromQ _ entry.1.1
    · rintro child t st ⟨earlier,entry,_,_⟩ d ⟨_,_,_,_,_,path,_,tag,_⟩
      exact tag ▸ CutLeafFrames.control (frames.control t (visit earlier)) path (fromQ _ entry.1.1)
    · rintro child t st ⟨earlier,entry,file,named⟩ d stopped
      obtain ⟨_,_,_,_,_,_,_,form⟩ := earlier.layout ready size room full linux
      exact frameChild (c := c) frames (head := Model.successor reg.session) rfl
        (io.write child t st earlier entry file named) entry ⟨[],form⟩ (fromQ _ entry.1.1) stopped
    · rintro child t st ⟨_,candidate,_⟩ d stopped
      exact stopped.1 ▸ fromQ _ candidate.1.1
    · rintro child t st ⟨_,candidate⟩ d ⟨_,_,_,site,stopped⟩
      exact stopped.1 ▸ VolatileFrame.close frames.volatile site (fromQ _ candidate.1.1)

theorem framePublic {disk : W → Model.Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (frames : FrameRuntime disk reg.store reg.session P)
    (fromQ : ∀ t, Q t → P t) (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : PublicStop op.cell op.mutex reg.store reg.session batch w (tagAt stop last) d) : P last := by
  cases cut with
  | lock tag => exact tag.1 ▸ fromQ _ q
  | read tag => exact tag.1 ▸ VolatileFrame.lock frames.volatile _ (fromQ _ q)
  | poison tag => exact tag.1 ▸ VolatileFrame.get frames.volatile _ (VolatileFrame.lock frames.volatile _ (fromQ _ q))
  | worker cut => exact frameBody op frames fromQ active q size room linux cut
  | install run tag => exact frameAfterSuccess op frames.volatile fromQ active q size room linux (.install run tag)
  | leave run tag => exact frameAfterSuccess op frames.volatile fromQ active q size room linux (.leave run tag)
  | fail run tag => exact tag.1 ▸ frameAfterFailure op fromQ active q size room linux run

end WalRecoverySlice.Segmented.Native.AppendCut
