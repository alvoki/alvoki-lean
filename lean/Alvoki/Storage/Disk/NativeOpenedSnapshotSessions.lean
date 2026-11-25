import Alvoki.Storage.Disk.NativeOpenSnapshotTrace
import Alvoki.Storage.Disk.NativeOpenedRestartSessions

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- Derive finite snapshot and run rewrite blocks at their reached
tables. Reopen steps retain their own local survivor or close reports,
so each later block starts at the exact new table and phase heap. -/
theorem NativeOpenedSessionTrace.executesSnapshotsAndRewrites
    (start : NativeOpenedSessionPoint heap) (actions : List NativeOpenedSessionAction)
    (observe : ∀ completed events reached action remaining,
      actions = completed ++ action :: remaining →
      NativeOpenedSessionTrace view names bytes start completed events reached →
      match action with
      | .calls instructions => NativeOpenedTrace.SnapshotAndRewriteOperands reached.position instructions
      | .quietRestart input => Nonempty (NativeQuietRestartReport reached input view names bytes)
      | .closeAndReopen input => Nonempty (NativeOpenedAlignedCloseReport reached.position input view)
      | .processExitAndReopen _ | .checkpointRenameReboot _ | .stoppedCheckpointReboot _
      | .uncertainWriteReboot _ _ | .uncertainWriteExitAndReopen _ _ | .stoppedWalWriteReboot _ _ => False) :
    ∃ events next, NativeOpenedSessionTrace view names bytes start actions events next ∧
      NativeExecutionTrace start.position.current events next.position.current ∧
      InstalledClientReplay next.position.current.submissions next.position.current.ready.reads next.position.current.history
        next.position.current.ready.state.writer.installed next.position.current.ready.state.session := by
  apply executes start actions
  intro completed events reached action remaining ordered prior
  have seen := observe completed events reached action remaining ordered prior
  cases action with
  | calls instructions =>
    exact ⟨.calls instructions (NativeOpenedTrace.reportsSnapshotsAndRewrites seen)⟩
  | quietRestart input =>
    obtain ⟨reported⟩ := seen
    exact ⟨.quiet input reported⟩
  | closeAndReopen input =>
    obtain ⟨reported⟩ := seen
    exact ⟨.close input reported⟩
  | processExitAndReopen _ | checkpointRenameReboot _ | stoppedCheckpointReboot _
  | uncertainWriteReboot _ _ | uncertainWriteExitAndReopen _ _ | stoppedWalWriteReboot _ _ => exact False.elim seen

end Alvoki.Storage.DiskSession
