import Alvoki.Storage.Disk.NativeOpenReadyTrace

namespace Alvoki.Storage.DiskSession

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- For a snapshot call, only the operand selection and the comparison
of the original live token need a report. The ready phase supplies the
guards, result and next state. -/
def NativeOpenedInstruction.SnapshotOperands (instruction : NativeOpenedInstruction)
    (start : NativeOpenedPosition opened) : Prop :=
  match instruction with
  | .acquire | .acquireAt _ | .advanceFloor _ => True
  | .releaseAt index | .readAt index _ =>
    index < start.pins.length ∧ opened.ptrEq opened.token opened.token start.reached = .ok true start.reached
  | .write _ | .checkpoint | .rewriteRun _ | .readSupplied _ _ | .releaseSupplied _ | .planWalCollection => False

theorem NativeOpenedInstruction.observesSnapshot
    (instruction : NativeOpenedInstruction) (start : NativeOpenedPosition opened)
    (operands : instruction.SnapshotOperands start) :
    Nonempty (NativeOpenedReport start instruction) := by
  cases instruction with
  | write | checkpoint | rewriteRun | readSupplied | releaseSupplied | planWalCollection => exact False.elim operands
  | acquire => exact ⟨.acquire⟩
  | acquireAt sequence =>
    cases acquired : start.current.ready.state.writer.installed.table.acquireAt sequence with
    | none => exact ⟨.acquireAtUnavailable sequence acquired⟩
    | some found =>
      obtain ⟨pin, table⟩ := found
      exact ⟨.acquireAt sequence acquired⟩
  | advanceFloor floor => exact ⟨.advanceFloor floor⟩
  | releaseAt index =>
    obtain ⟨inBounds, compared⟩ := operands
    let pin := start.pins[index]'inBounds
    exact ⟨.releaseAt index pin (List.getElem?_eq_getElem inBounds) compared⟩
  | readAt index request =>
    obtain ⟨inBounds, compared⟩ := operands
    let pin := start.pins[index]'inBounds
    exact ⟨.readAt index request pin (List.getElem?_eq_getElem inBounds) compared⟩

/-- Any finite snapshot-only continuation can be interpreted at the
exact opened table. Each read or release must name an existing entry in
the reached issuance list and report the live-token comparison there.
Acquisition and floor decisions come from the reached table. -/
theorem NativeOpenedTrace.executesSnapshots
    (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction)
    (operands : ∀ issued events reached instruction remaining,
      instructions = issued ++ instruction :: remaining →
      NativeOpenedTrace start issued events reached → instruction.SnapshotOperands reached) :
    ∃ events last, NativeOpenedTrace start instructions events last ∧
      NativeExecutionTrace start.current events last.current ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session := by
  apply executes start instructions
  intro issued events reached instruction remaining ordered previous
  exact instruction.observesSnapshot reached (operands issued events reached instruction remaining ordered previous)

/-- A snapshot and run rewrite block needs only selected pin operands
and token comparisons at the reached reads and releases. -/
def NativeOpenedTrace.SnapshotAndRewriteOperands
    (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction) : Prop :=
  ∀ issued events reached instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeOpenedTrace start issued events reached →
    match instruction with
    | .rewriteRun _ => True
    | instruction => instruction.SnapshotOperands reached

theorem NativeOpenedTrace.reportsSnapshotsAndRewrites
    {start : NativeOpenedPosition opened} {instructions : List NativeOpenedInstruction}
    (operands : SnapshotAndRewriteOperands start instructions) : Reports start instructions := by
  intro issued events reached instruction remaining ordered previous
  have reported := operands issued events reached instruction remaining ordered previous
  cases instruction with
  | rewriteRun request => exact ⟨.rewriteRun request⟩
  | _ => exact NativeOpenedInstruction.observesSnapshot _ reached reported

/-- The same finite continuation can include public run rewrites.
Their accept or refuse decisions use only the reached phase table. -/
theorem NativeOpenedTrace.executesSnapshotsAndRewrites
    (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction)
    (operands : SnapshotAndRewriteOperands start instructions) :
    ∃ events last, NativeOpenedTrace start instructions events last ∧
      NativeExecutionTrace start.current events last.current ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session :=
  executes start instructions (reportsSnapshotsAndRewrites operands)

end Alvoki.Storage.DiskSession
