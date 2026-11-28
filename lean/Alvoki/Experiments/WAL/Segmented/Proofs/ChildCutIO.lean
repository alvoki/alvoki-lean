import Alvoki.Experiments.WAL.Proofs.ConcreteAppendCut
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCut

namespace WalRecoverySlice.Segmented.Native.ChildCutIO

open SingleFile (AppendFiles)
open SingleFile.ConcreteAppend (PhaseRef readAt poisonAt nativeOps modeledOps)
open SingleFile.ConcreteRecovery (Op Program programOps)
open SingleFile.ConcreteAppendCut (Issued Site Reports)
open Alvoki.NativePost (W)
open Model (Disk)
open Persistence (Image historyCursor)

/-- An interrupt at a syscall in an actual live child's append. The
record carries only native observations; the disk proof consumes it. -/
structure Receipt (stop : IO Unit → W → Disk → Prop) (h : SingleFile.Handle) (batch : Bytes) (start : W) (cut : Disk) where
  policy : Policy
  known : List Bytes
  cell : PhaseRef
  mutex : Std.BaseMutex
  fd : IO.FS.Handle
  files : AppendFiles IO.FS.Handle
  assembled : h.Assembled policy cell mutex
  active : (readAt cell mutex start).val = .active fd files (historyCursor known) known
  op : Op
  cont : op.Result → Program Cursor
  atOp : W
  path : Issued (nativeOps files) (appendBatch programOps policy (historyCursor known) batch)
    (poisonAt cell fd mutex start) (.call op cont) atOp
  action : IO Unit
  atCall : W
  site : Site files op atOp action atCall
  stopped : stop action atCall cut

/-- File and namespace effects are requested only for the exact descriptor
and syscall exposed by the receipt. Completed instructions pair their
own byte image with the original PR #26 reports. -/
structure Primitives (disk : W → Disk) (c : Control) (r : Receipt stop h batch start cut) where
  report : SingleFile.AppendReports r.policy (historyCursor r.known) batch
  poison : (disk (poisonAt r.cell r.fd r.mutex start)).segment c.active = (disk start).segment c.active
  completed : r.path.Earlier (fun op v a b =>
    (op.eval (modeledOps report)).run ((disk a).segment c.active) = .ok (.ok v) ((disk b).segment c.active))
  syscall : ∀ d, stop r.action r.atCall d →
    (r.op.eval (modeledOps report)).run ((disk r.atOp).segment c.active) = .error () (d.segment c.active)
  heapFrame : AppendCut.ActiveFiles c (disk start) (disk (poisonAt r.cell r.fd r.mutex start))
  returnedFrame : r.path.Earlier (fun _ _ a b => AppendCut.ActiveFiles c (disk a) (disk b))
  stoppedFrame : ∀ d, stop r.action r.atCall d → AppendCut.ActiveFiles c (disk r.atOp) d

private theorem earlierFrame {disk : W → Disk} {start : W} (path : Issued actual source start rest w)
    (frames : path.Earlier (fun _ _ a b => AppendCut.ActiveFiles c (disk a) (disk b))) :
    AppendCut.ActiveFiles c (disk start) (disk w) := by
  induction path with
  | start => exact .refl .. 
  | next _ _ ih => exact (ih frames.1).trans frames.2

theorem recoverable (r : Receipt stop h batch start cut) (prim : Primitives disk c r)
    (policy : r.policy = c.policy) (known : r.known = segmentHistory c.capacity c.active history)
    (entry : ReadyLayout c history (disk start))
    (live : (disk start).liveControl = some c) (durable : (disk start).durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity)
    (position : (historyView c history).tail < Contract.maxPosition) (size : batch.length ≤ 32) :
    Recoverable (historyView c history) (some (.append batch)) cut := by
  have paired := Reports.of_earlier r.path (modeledOps prim.report) (fun w => (disk w).segment c.active) prim.completed
  rw [prim.poison] at paired
  have ready : Child.Installed r.policy ((disk start).segment c.active) ((disk start).cursor c.active) r.known :=
    policy ▸ known ▸ entry.active
  have limit : r.known.length < 255 := by
    rw [known, segmentHistory_active_length entry.layout.upper]
    have cap := entry.layout.capacityFits
    rw [Nat.add_mul, Nat.one_mul] at room
    omega
  have child := SingleFile.ConcreteAppendCut.interrupted prim.report r.path paired r.site
    (fun a w child => ∃ d, stop a w d ∧ d.segment c.active = child)
    ⟨cut, r.stopped, rfl⟩ (fun _ _ ⟨d, stopped, eq⟩ => eq ▸ prim.syscall d stopped)
    ready.ready ready.clean (known ▸ segmentHistory_bounded entry.layout _) limit size
  have frame := (prim.heapFrame.trans (earlierFrame r.path prim.returnedFrame)).trans (prim.stoppedFrame _ r.stopped)
  apply frame.recoverable entry live durable room position
  rw [← policy, ← known]
  exact ⟨child.1, child.2⟩

end WalRecoverySlice.Segmented.Native.ChildCutIO
