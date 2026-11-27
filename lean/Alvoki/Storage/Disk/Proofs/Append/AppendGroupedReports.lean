import Alvoki.Storage.Disk.Proofs.Append.AppendLockHandoff
import Alvoki.Storage.Disk.Proofs.Write.WriteGroupFsync

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentCommit SyncHandleRouting

/-- Preserve the result, including its diagnostic, and project its reached heap. -/
def projectResult {heap files value : Type} (view : heap → files) :
    EStateM.Result IO.Error heap value → EStateM.Result IO.Error files value
  | .ok result reached => .ok result (view reached)
  | .error cause reached => .error cause (view reached)

/-- Hide the native cache from the write interpreter while retaining the
original success or error and the file state reached by the shared group. -/
def withoutWriteGroupCache {handle : Type} :
    EStateM.Result IO.Error (Cache handle × WriteFiles) Unit → EStateM.Result IO.Error WriteFiles Unit
  | .ok value (_, after) => .ok value after
  | .error cause (_, after) => .error cause after

theorem withoutWriteGroupCache_eq_projectResult {handle : Type}
    (result : EStateM.Result IO.Error (Cache handle × WriteFiles) Unit) :
    withoutWriteGroupCache result = projectResult Prod.snd result := by
  cases result with
  | ok value reached => cases reached; rfl
  | error cause reached => cases reached; rfl

private theorem markerRun_projects {source target : Type} (observe : source → target)
    (actual : Publication.Step → EStateM IO.Error source Unit)
    (projected : Publication.Step → EStateM IO.Error target Unit)
    (steps : List Publication.Step) (initial : source)
    (agrees : ∀ (prior : List Publication.Step) step remaining reached, steps = prior ++ step :: remaining →
      (prior.forM actual) initial = .ok () reached →
      projectResult observe (actual step reached) = projected step (observe reached)) :
    projectResult observe ((steps.forM actual) initial) = (steps.forM projected) (observe initial) := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step rest ih =>
    have first := agrees [] step rest initial rfl rfl
    change projectResult observe (EStateM.bind (actual step) (fun _ => rest.forM actual) initial) =
      EStateM.bind (projected step) (fun _ => rest.forM projected) (observe initial)
    unfold EStateM.bind
    rw [← first]
    cases next : actual step initial with
    | error cause reached => rfl
    | ok value after =>
      cases value
      change projectResult observe ((rest.forM actual) after) = (rest.forM projected) (observe after)
      apply ih
      intro prior action remaining reached schedule recorded
      apply agrees (step :: prior) action remaining reached (congrArg (List.cons step) schedule)
      change EStateM.bind (actual step) (fun _ => prior.forM actual) initial = .ok () reached
      simpa only [EStateM.bind, next] using recorded

/-- Project the same reached append and publication, with a local law
at each issued callback. A failed callback keeps its diagnostic and
the projection of its own returned state. No later callback is needed. -/
theorem commitBytesAt_projects {source target : Type} (observe : source → target)
    (directory : DiskDirectory) (first : Nat) (bytes : ByteArray) (count : Nat)
    (append stage : FilePath → ByteArray → EStateM IO.Error source Unit)
    (sync : Array FilePath → EStateM IO.Error source Unit)
    (rename : FilePath → FilePath → EStateM IO.Error source Unit)
    (appendAt stageAt : FilePath → ByteArray → EStateM IO.Error target Unit)
    (syncAt : Array FilePath → EStateM IO.Error target Unit)
    (renameAt : FilePath → FilePath → EStateM IO.Error target Unit)
    (entry : source)
    (appendProjects : let path := directory.file (.walSegment first)
      projectResult observe (append path bytes entry) = appendAt path bytes (observe entry))
    (markerProjects : ∀ appended, append (directory.file (.walSegment first)) bytes entry = .ok () appended →
      ∀ (prior : List Publication.Step) step remaining reached, Publication.steps = prior ++ step :: remaining →
      let actual := performMarkerAt directory first count stage sync rename
      (prior.forM actual) appended = .ok () reached →
      projectResult observe (actual step reached) =
        performMarkerAt directory first count stageAt syncAt renameAt step (observe reached)) :
    projectResult observe (commitBytesAt directory first bytes count append stage sync rename entry) =
      commitBytesAt directory first bytes count appendAt stageAt syncAt renameAt (observe entry) := by
  let keeper := directory.file (.walSegment first)
  change projectResult observe (EStateM.bind (append keeper bytes) (fun _ =>
      Publication.run (performMarkerAt directory first count stage sync rename)) entry) =
    EStateM.bind (appendAt keeper bytes) (fun _ =>
      Publication.run (performMarkerAt directory first count stageAt syncAt renameAt)) (observe entry)
  unfold EStateM.bind
  rw [← appendProjects]
  cases ran : append keeper bytes entry with
  | error cause reached => rfl
  | ok value appended =>
    cases value
    exact markerRun_projects observe _ _ _ appended (markerProjects appended ran)

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
