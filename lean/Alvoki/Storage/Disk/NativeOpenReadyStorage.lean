import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeOpenReferences

namespace Alvoki.Storage.DiskSession

open System

/-- The ready phase and token allocations preserve settled files and the
visible keeper bytes that the next append uses. Their local frames start
at the repaired heap and end at the heap returned by the installer. -/
theorem OpenReferenceAllocations.framesReadyStorage {heap : Type}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)} {before : heap}
    {installed : Installed} {state : NativeReadyState}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken contents installed before)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (ready : NativeReadyStorage state (observe before))
    (keeperLive : ∀ inode, (observe before).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible before inode = state.writer.wal.active.bytes)
    (phaseFrame : (observe before).Frames state.crashPath (observe allocation.afterPhase))
    (tokenFrame : (observe allocation.afterPhase).Frames state.crashPath (observe allocation.afterToken))
    (phaseKeeper : ∀ inode, (observe before).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterPhase inode = visible before inode)
    (tokenKeeper : ∀ inode, (observe allocation.afterPhase).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = visible allocation.afterPhase inode) :
    NativeReadyStorage state (observe allocation.afterToken) ∧
    ∀ inode, (observe allocation.afterToken).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = state.writer.wal.active.bytes := by
  let path := state.session.directory.file (.walSegment state.writer.wal.active.first)
  have selected : state.crashPath path := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  refine ⟨ready.frame (phaseFrame.trans tokenFrame), ?_⟩
  intro inode bound
  have atPhase := ((tokenFrame.visible path selected).1).symm.trans bound
  have atRepair := ((phaseFrame.visible path selected).1).symm.trans atPhase
  exact (tokenKeeper inode atPhase).trans ((phaseKeeper inode atRepair).trans (keeperLive inode atRepair))

end Alvoki.Storage.DiskSession
