import Alvoki.Experiments.WAL.Segmented.Proofs.CutMemory

namespace WalRecoverySlice.Segmented.Native.ChildCutIO

open SingleFile (AppendFiles)
open SingleFile.ConcreteAppend (PhaseRef readAt poisonAt installAt nativeOps modeledOps)
open SingleFile.ConcreteAppendCut (Site Reports Issued Terminal)
open SingleFile.ConcreteRecovery (Op Program programOps)
open Alvoki.NativePost (W)
open Model (Disk)
open Persistence (historyCursor)

/-- The phase installed by this exact public child handle. -/
structure Operand (child : SingleFile.Handle) (w : W) where
  policy : Policy
  known : List Bytes
  cell : PhaseRef
  mutex : Std.BaseMutex
  fd : IO.FS.Handle
  files : AppendFiles IO.FS.Handle
  assembled : child.Assembled policy cell mutex
  active : (readAt cell mutex w).val = .active fd files (historyCursor known) known

def Receipt.operand (r : Receipt stop h batch w d) : Operand h w :=
  ⟨r.policy,r.known,r.cell,r.mutex,r.fd,r.files,r.assembled,r.active⟩

inductive Before (a : Operand h start) : {α : Type} → IO α → W → Prop where
  | poison : Before a (a.cell.set (.poisoned a.fd) : IO Unit) (readAt a.cell a.mutex start).state

inductive After (a : Operand h start) (batch : Bytes) (t : W) :
    Except IO.Error (Except String Cursor) → {α : Type} → IO α → W → Prop where
  | install : After a batch t (.ok (.ok next)) (a.cell.set (.active a.fd a.files next (a.known ++ [batch])) : IO _) t
  | leave : After a batch t (.ok (.ok next)) (liftM a.mutex.unlock)
      (installAt a.cell a.fd a.files next (a.known ++ [batch]) t)
  | failed : After a batch t (.error e) (liftM a.mutex.unlock) t
  | rejected : After a batch t (.ok (.error e)) (liftM a.mutex.unlock) t

structure Complete (stop : ControlCutIO.Stops) (h : SingleFile.Handle) (batch : Bytes) (w : W) (d : Disk) where
  operand : Operand h w
  rest : Program Cursor
  endStart : W
  path : Issued (nativeOps operand.files) (appendBatch programOps operand.policy (historyCursor operand.known) batch)
    (poisonAt operand.cell operand.fd operand.mutex w) rest endStart
  ended : W
  outcome : Except IO.Error (Except String Cursor)
  last : Terminal (nativeOps operand.files) rest endStart outcome ended
  resultType : Type
  action : IO resultType
  atCall : W
  site : After operand batch ended outcome action atCall
  cut : stop action atCall d

structure ReturnPrimitives (disk : W → Disk) (c : Control) (r : Complete stop h batch w d) where
  report : SingleFile.AppendReports r.operand.policy (historyCursor r.operand.known) batch
  completed : r.path.Earlier (fun op v a b =>
    (op.eval (modeledOps report)).run ((disk a).segment c.active) = .ok (.ok v) ((disk b).segment c.active))
  terminal : r.last.Report (modeledOps report) (fun u => (disk u).segment c.active)
  returnedFrame : r.path.Earlier (fun _ _ a b => AppendCut.ActiveFiles c (disk a) (disk b))
  finalFrame : AppendCut.ActiveFiles c (disk r.endStart) (disk r.ended)

theorem Before.writes (io : AppendCut.VolatileIO disk stop) {a : Operand h w} (visit : Before a action u)
    (cut : stop action u d) : Writebacks (disk w) d := by
  cases visit with
  | poison => exact ((io.lock _ _).trans (io.get _ _)).trans (io.stopped _ (.set _ _) _ _ cut)

theorem After.writes (io : AppendCut.VolatileIO disk stop) (visit : After a batch t outcome action u)
    (cut : stop action u d) : Writebacks (disk t) d := by
  cases visit with
  | install => exact io.stopped _ (.set _ _) _ _ cut
  | leave => exact (io.set _ _ _).trans (io.stopped _ (.leave _) _ _ cut)
  | failed | rejected => exact io.stopped _ (.leave _) _ _ cut

theorem returned (r : Complete stop child batch w cut) (localIO : ReturnPrimitives disk c r)
    (io : AppendCut.VolatileIO disk stop) (known : r.operand.known = segmentHistory c.capacity c.active hist)
    (policy : r.operand.policy = c.policy) (entry : ReadyLayout c hist (disk w))
    (live : (disk w).liveControl = some c) (durable : (disk w).durableControl = some c)
    (room : hist.length < (c.active+1)*c.capacity) (position : (historyView c hist).tail < Contract.maxPosition)
    (size : batch.length ≤ 32) : Recoverable (historyView c hist) (some (.append batch)) cut := by
  let a := r.operand
  have edge := ((io.lock a.mutex w).trans (io.get a.cell _)).trans (io.set a.cell (.poisoned a.fd) _)
  change Writebacks (disk w) (disk (poisonAt a.cell a.fd a.mutex w)) at edge
  have ready := edge.readyLayout entry
  have paired := Reports.of_earlier r.path (modeledOps localIO.report) (fun t => (disk t).segment c.active) localIO.completed
  have valid : Child.Installed r.operand.policy _ _ r.operand.known := policy ▸ known ▸ ready.active
  have bound : r.operand.known.length < 255 := by
    rw [known, segmentHistory_active_length entry.layout.upper]
    have cap := entry.layout.capacityFits
    rw [Nat.add_mul,Nat.one_mul] at room; omega
  obtain ⟨dirty,markers⟩ := SingleFile.ConcreteAppendCut.terminal localIO.report r.path
    (fun t => (disk t).segment c.active) paired r.last localIO.terminal valid.ready valid.clean
    (known ▸ segmentHistory_bounded entry.layout _) bound size
  have files := (earlierFrame r.path localIO.returnedFrame).trans localIO.finalFrame
  apply (r.site.writes io r.cut).recoverable
  apply files.recoverable ready (edge.live.trans live) (edge.durable.trans durable) room position
  exact policy ▸ known ▸ ⟨dirty,markers⟩

end WalRecoverySlice.Segmented.Native.ChildCutIO
