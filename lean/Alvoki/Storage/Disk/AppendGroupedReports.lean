import Alvoki.Storage.Disk.AppendLockHandoff
import Alvoki.Storage.Disk.WriteGroupFsync

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentCommit SyncHandleRouting

/-- Hide the native cache from the write interpreter while retaining the
original success or error and the file state reached by the shared group. -/
def withoutWriteGroupCache {handle : Type} :
    EStateM.Result IO.Error (Cache handle × WriteFiles) Unit → EStateM.Result IO.Error WriteFiles Unit
  | .ok value (_, after) => .ok value after
  | .error cause (_, after) => .error cause after

/-- The separate IO and reference observations for the actual reached
keeper and staged-marker syncs. The keeper callback's reached state is
also where the staged path and captured description are observed. -/
structure ReachedWriteGroup {handle : Type} (directory : DiskDirectory) (first : Nat) (bytes : ByteArray)
    (before : WriteFiles) (perform : Array FilePath → EStateM IO.Error WriteFiles Unit) where
  cache : Cache handle
  openRead : FilePath → EStateM IO.Error WriteFiles handle
  fsync : handle → EStateM IO.Error WriteFiles Unit
  description : handle → Nat
  inode : handle → Nat
  bindings : WriteFiles → FilePath → Option Nat
  keeperHandle : handle
  stagedHandle : handle
  keeperNotDirectory : directory.file (.walSegment first) ≠ directory.path
  stagedNotDirectory : directory.file .stagedWalBoundary ≠ directory.path
  keeperMiss : cache.pending.find? (fun entry => entry.1 == directory.file (.walSegment first)) = none
  active : cache.active = some (directory.file (.walSegment first), keeperHandle)
  pending : cache.pending.find? (fun entry => entry.1 == directory.file .stagedWalBoundary) =
    some (directory.file .stagedWalBoundary, stagedHandle)
  owned : cache.Agrees directory.path inode (bindings before)
  distinct : inode keeperHandle ≠ inode stagedHandle
  wal : WalSyncEffect
  stableStage : bindings (reachedState (fsync keeperHandle before)) (directory.file .stagedWalBoundary) =
    bindings before (directory.file .stagedWalBoundary)
  keeper : FsyncObservation description inode keeperHandle before (fun _ state => state.syncWal wal)
    (fsync keeperHandle before)
  complete : ∀ after, fsync keeperHandle before = .ok () after → wal = .complete
  staged : FsyncObservation description inode stagedHandle (reachedState (fsync keeperHandle before))
    (fun _ state => (state.stepMarker bytes .syncStaged).getD state)
    (fsync stagedHandle (reachedState (fsync keeperHandle before)))
  execution : perform #[directory.file (.walSegment first), directory.file .stagedWalBoundary] before =
    withoutWriteGroupCache (SyncPathGroup.run (sync directory.path openRead fsync)
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] (cache, before))

def ReachedWriteGroup.effects {handle directory first bytes before perform}
    (observed : ReachedWriteGroup (handle := handle) directory first bytes before perform)
    (initial : WriteEffects) : WriteEffects :=
  let keeper := observed.fsync observed.keeperHandle before
  let staged := observed.fsync observed.stagedHandle (reachedState keeper)
  let wal := if observed.keeper.effective then observed.wal else .incomplete initial.appendCrashTails
  { initial with sync := writeGroupOutcome keeper staged wal observed.staged.effective }

/-- The same two observed file syncs refine the grouped callback for any
append whose reached crash tails and staged marker match these inputs. -/
theorem ReachedWriteGroup.projected {handle directory first bytes before perform}
    (observed : ReachedWriteGroup (handle := handle) directory first bytes before perform)
    (initial : WriteEffects)
    (crashTails : before.crashTails = ByteArray.empty :: initial.appendCrashTails)
    (scratch : before.marker.staged = some (bytes, false)) :
    let result := SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] (observed.cache, before)
    (reachedState result).1 = observed.cache.consume (directory.file .stagedWalBoundary) ∧
      projectWriteGroup result = (observed.effects initial).markerStep bytes .syncStaged before := by
  exact (groupedWrite_effects directory.path (directory.file (.walSegment first))
    (directory.file .stagedWalBoundary) observed.cache before (observed.effects initial) bytes observed.openRead
    observed.fsync observed.description observed.inode observed.bindings observed.keeperNotDirectory
    observed.stagedNotDirectory observed.keeperMiss observed.active observed.pending observed.owned
    observed.distinct initial.appendCrashTails observed.wal crashTails scratch observed.stableStage
    observed.keeper observed.complete observed.staged rfl).2.2.2

/-- Report the modeled marker action directly from the actual grouped
observations. Only the preceding append and stage supply the input file
image. The group classification follows from its two syscall outcomes. -/
theorem ReachedWriteGroup.marker {handle directory first newBytes before perform}
    (observed : ReachedWriteGroup (handle := handle) directory first (WAL.Boundary.encode newBytes.toUInt64) before perform)
    (initial : WriteEffects) (event : WAL.Write) (write : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit)
    {starting appended : WriteFiles} (appendedReport : initial.appendFrame event starting = .ok () appended)
    (stagedReport : initial.markerStep (WAL.Boundary.encode newBytes.toUInt64) .writeStaged appended = .ok () before) :
    forgetError (performMarkerAt directory first newBytes write perform rename .syncStaged) before =
      (observed.effects initial).markerStep (WAL.Boundary.encode newBytes.toUInt64) .syncStaged before := by
  obtain ⟨crashTails, scratch⟩ := initial.reachedWriteGroup event _ appendedReport stagedReport
  have grouped := observed.projected initial crashTails scratch
  refine Eq.trans ?_ grouped.2
  change forgetError (perform #[directory.file (.walSegment first), directory.file .stagedWalBoundary]) before = _
  unfold forgetError
  rw [observed.execution]
  cases SyncPathGroup.run (sync directory.path observed.openRead observed.fsync)
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] (observed.cache, before) <;> rfl

/-- The grouped action has exactly one predecessor in the publication
schedule. Reuse the supplied reports for the other reached marker actions. -/
theorem AppendCommitReports.ofReachedWriteGroup {handle : Type} {directory : DiskDirectory}
    {first newBytes : Nat} {history : List WAL.Write} {event : WAL.Write} {scratch : Option (ByteArray × Bool)}
    (initial : WriteEffects) {append write : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit}
    {perform : Array FilePath → EStateM IO.Error WriteFiles Unit}
    {rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit} {appended staged : WriteFiles}
    (appendModel : initial.appendFrame event (WriteFiles.initial history scratch) = .ok () appended)
    (stageModel : initial.markerStep (WAL.Boundary.encode newBytes.toUInt64) .writeStaged appended = .ok () staged)
    (observed : ReachedWriteGroup (handle := handle) directory first (WAL.Boundary.encode newBytes.toUInt64) staged perform)
    (appendReport : forgetError (append (directory.file (.walSegment first)) (WAL.encodeFrame event))
      (WriteFiles.initial history scratch) = initial.appendFrame event (WriteFiles.initial history scratch))
    (other : ∀ opened, initial.appendFrame event (WriteFiles.initial history scratch) = .ok () opened →
      ∀ prior action remaining state, action ≠ .syncStaged → Publication.steps = prior ++ action :: remaining →
      (prior.forM ((observed.effects initial).markerStep (WAL.Boundary.encode newBytes.toUInt64))) opened = .ok () state →
      forgetError (performMarkerAt directory first newBytes write perform rename action) state =
        (observed.effects initial).markerStep (WAL.Boundary.encode newBytes.toUInt64) action state) :
    AppendCommitReports directory first history event newBytes (observed.effects initial) scratch
      append write perform rename := by
  refine ⟨appendReport, ?_⟩
  intro opened appendedReport prior action remaining state schedule reached
  by_cases grouped : action = .syncStaged
  · subst action
    have openedExact : opened = appended := EStateM.Result.ok.inj (appendedReport.symm.trans appendModel) |>.2
    subst opened
    have ordered : prior = [.writeStaged] := by
      rcases prior with _ | ⟨head, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _⟩⟩⟩⟩ <;>
        simp [Publication.steps] at schedule ⊢
      exact schedule.1.symm
    subst prior
    have stageRead : (observed.effects initial).markerStep (WAL.Boundary.encode newBytes.toUInt64) .writeStaged appended =
        .ok () staged := stageModel
    have stageExact : staged = state := by
      simpa [List.forM_cons, List.forM_nil, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, stageRead] using reached
    subst state
    exact observed.marker initial event write rename appendModel stageModel
  · exact other opened appendedReport prior action remaining state grouped schedule reached

end Alvoki.Storage.DiskSession
