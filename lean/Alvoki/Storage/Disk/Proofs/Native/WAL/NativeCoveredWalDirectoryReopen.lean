import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeCoveredWalDirectoryStop
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeCoveredWalUnlinkReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeCoveredWalDirectoryStop

variable {state : NativeReadyState}

/-- The barrier settles deletion choices, leaving the already settled
manifest and WAL marker and the exact keeper intact. -/
theorem intact (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) :
    stop.after.visible.directory = state.writer.wal.directory ∧ stop.after.visible.active = state.writer.wal.active := by
  have frame := stop.unlinked.framesWal
  unfold after
  cases applied : stop.applied
  · exact frame
  · change stop.beforeSync.visible.directory.syncDirectory = state.writer.wal.directory ∧
      stop.beforeSync.visible.active = state.writer.wal.active
    refine ⟨?_, frame.2⟩
    rw [frame.1]
    change state.writer.wal.directory.syncDirectory = state.writer.wal.directory
    have settled := valid.retained.walDirectorySettled
    cases directory : state.writer.wal.directory
    rw [directory] at settled
    simp only [DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.mk.injEq, true_and, and_true]
    exact settled.symm

def crashCut (stop : NativeCoveredWalDirectoryStop state) : NativeCoveredWalCrashCut state where
  calls := stop.calls
  inventory := stop.inventory
  census := stop.census
  sameCensus := stop.sameCensus
  afterView := stop.view
  after := stop.after
  objects := stop.objects
  frameChild other := stop.unlinked.keepsOtherChild other
  intact := stop.intact
  survivorAllowed valid sealed survives := by
    obtain ⟨layout⟩ := (stop.selections valid).2 sealed survives
    exact layout.retained

end NativeCoveredWalDirectoryStop

abbrev NativeCoveredWalDirectoryCrash {state : NativeReadyState} (stop : NativeCoveredWalDirectoryStop state) :=
  NativeCoveredWalCrash stop.crashCut

/-- An effective directory fsync excludes every approved offset from
this one raw reboot namespace, even when its callback never returned. -/
theorem NativeCoveredWalDirectoryStop.removesOnReboot {state : NativeReadyState}
    (stop : NativeCoveredWalDirectoryStop state) (crash : NativeCoveredWalDirectoryCrash stop)
    (valid : state.Valid) (applied : stop.applied = true) :
    ∀ offset ∈ state.writer.wal.collectionOffsets,
      crash.observed.names (state.session.directory.file (.walSegment offset)) = none := by
  intro offset approved
  obtain ⟨target, sealed, start⟩ := (valid.retained.layout.collectionOffsets_approved approved).1
  have earlier := ((valid.retained.layout.collectionOffsets_approved approved).2 target sealed start).sealedBeforeActive
  have distinct : offset ≠ state.writer.wal.active.first := by
    rw [← start]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le earlier.1 earlier.2)
  have absent : offset ∉ crash.sealed.map WalSegment.first := by
    intro member
    obtain ⟨segment, present, address⟩ := List.mem_map.mp member
    exact ((stop.settled valid).2 applied).2 offset approved crash.sealed crash.survived segment present address
  rw [crash.walBindings, ite_eq_right (not_or.mpr ⟨distinct, absent⟩)]

/-- The exact directory stop and reported power loss feed the same
captured aligned opener as a stop within the unlink prefix. -/
structure NativeCoveredWalDirectoryReopen (current : NativeReadPosition history log)
    {stop : NativeCoveredWalDirectoryStop current.state} (crash : NativeCoveredWalDirectoryCrash stop) (input : FilePath) : Prop
    extends NativeCoveredWalReopened current crash input where
  stopped : NativeCoveredWalDirectoryStopped current stop
  removed : stop.applied = true → ∀ offset ∈ current.state.writer.wal.collectionOffsets,
    crash.observed.names (current.state.session.directory.file (.walSegment offset)) = none

theorem NativeReadPosition.recoversInterruptedCoveredWalDirectory (current : NativeReadPosition history log)
    (stop : NativeCoveredWalDirectoryStop current.state) (crash : NativeCoveredWalDirectoryCrash stop) {input : FilePath}
    (observe : crash.ReopenReports input) : NativeCoveredWalDirectoryReopen current crash input :=
  ⟨current.reopensCoveredWalCut crash observe, current.stopsAtCoveredWalDirectory stop,
    stop.removesOnReboot crash current.readPrefix.refines.1⟩

end Alvoki.Storage.DiskSession
