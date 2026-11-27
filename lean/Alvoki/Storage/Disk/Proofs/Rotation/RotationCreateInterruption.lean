import Alvoki.Storage.Disk.Proofs.Rotation.RotationReopenAdmission
import Alvoki.Storage.Disk.BatchRecoveryPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRotation WalSegmentRepair SyncHandleRouting

def rotateFileCall {image α : Type} (action : ExceptT IO.Error (EStateM FilePath image) α) :
    ExceptT IO.Error (EStateM FilePath (Phase Installed × LockedFileState image)) α :=
  fun (phase, before) => match action.run before.image with
  | .ok value after => .ok value (phase, { before with image := after })
  | .error stop after => .error stop (phase, { before with image := after })

/-- The successor read has returned absence. The next exclusive open
stops before returning a handle to the cache. The file effect is the
reported first cut of the rotation body. -/
structure ObservedRotationCreateStop {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : RotationInFlightCut directory before) (handle : Type) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  openNew : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) handle
  cache : Cache handle
  checked : checkActiveSegmentWith directory before.installed lookup = .ok ()
  absent : ∃ name message, lookup (directory.file (.walSegment (before.installed.walBytes / WAL.frameSize))) =
    .error (.noFileOrDirectory name 2 message)
  first : cut.completed = 0
  stopped : let path := directory.file (.walSegment (before.installed.walBytes / WAL.frameSize))
    (openNew path).run (cache, .initial before.wal) = .error path (cache, cut.image)

/-- Interpret the public rotation schedule with ordinary errors as return
values and a separate stop channel. Exclusive open precedes the same
pending-handle insertion used by the native create callback. -/
def runRotationWithInterruption {handle : Type} (directory : DiskDirectory) (before : SegmentedWriterState)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (openNew : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) handle) (cache : Cache handle)
    (sync : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) Unit) :
    EStateM.Result FilePath (Phase Installed × LockedFileState (Cache handle × State)) (Except IO.Error Unit) :=
  let create := fun path => do
    let descriptor ← openNew path
    ExceptT.lift (modify fun (cache, files) => (cache.remember path descriptor, files))
  let read := fun path => readEmptyWith (pure (lookup path)) path "WAL segment successor is not empty"
  (rotateWalSchedule
    (fun state => .ok (state.1.installed : Except IO.Error Installed) state)
    (fun installed state => .ok (checkActiveSegmentWith directory installed lookup) state)
    (fun phase state => .ok (.ok ()) (phase, state.2))
    (fun successor => rotateFileCall
      (runAt directory successor read create sync))
    (fun (phase, before) =>
      .ok (.ok ()) (phase, { before with image := ({ before.image.1 with active := none }, before.image.2) }))).run
    (.ready before.installed, ⟨(cache, .initial before.wal), before.owners⟩)

/-- After power loss chooses the successor, reported retries use that
fixed keeper. Their selected files still prepare the old history before
any attempt has returned a session. -/
theorem RotationInFlightCut.refinesReportedReopenPrefix {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : RotationInFlightCut directory before) (ready : before.RetainedReady directory writer)
    {pair : DirectoryPublication.Bindings} {present : Bool}
    (metadata : pair ∈ cut.image.metadata.crashImages)
    (survives : cut.image.successor.MaySurvive present)
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory (cut.survivingWal pair present).active.first
      (cut.crashedFiles pair present) retry) :
    let keeper := (cut.survivingWal pair present).active
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (cut.crashedFiles pair present) retry ∧
    retry.image.directory.active = before.target.pair ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ Prepared retry.image layout.target layout.plan := by
  intro keeper
  have selected := cut.trace.selectsOriginal (List.mem_cons_of_mem _ metadata)
  have binding : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using selected
  have pairSelected := binding.trans ready.walPair
  have loss : Trace before.wal (cut.released pair present).image := .crash cut.trace pair metadata survives
  have decoded : (cut.released pair present).image.metadata.active.walRange = some before.target.range := by
    change pair.walRange = _
    rw [pairSelected]
    exact before.target.decoded
  obtain ⟨_, _, _, sourcePair, chosen, _, chosenKeeper, _, _, _, prepared⟩ :=
    loss.settledReopenLayout (ready.rotationInput cut.nonempty) ready.layout ready.valid decoded ready.resumed.through
  have authority : CheckpointRetryTarget before.history keeper.first chosen.target := by
    refine ⟨congrArg WalSegment.first chosenKeeper, chosen.through, ?_⟩
    simpa only [keeper, RotationInFlightCut.survivingWal, CanonicalKeeperLayout.target, chosenKeeper]
      using chosen.chain.keeperBytes
  have select {current : LockedFileState FileImage}
      (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
        (cut.crashedFiles pair present) current) :=
    (attempts.rotationRetryEffects authority prepared
      ((cut.released pair present).image.settledReopenImage_sync before.wal)).canonicalRetryLayout chosen prepared
  have attempts := reported.refines fun earlier => by
    obtain ⟨layout, _, _, _, _, _, _, checked⟩ := select earlier
    exact ⟨chosen.target, layout.plan, authority, authority.1, checked⟩
  obtain ⟨layout, target, _, _, _, active, _, checked⟩ := select attempts
  exact ⟨attempts, checked.pair.trans (prepared.pair.symm.trans (sourcePair.trans pairSelected)),
    layout, active.trans chosenKeeper, target.symm ▸ checked⟩

namespace ObservedRotationCreateStop

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {cut : RotationInFlightCut directory before} {handle : Type}

def runUntilCreate (observed : ObservedRotationCreateStop cut handle)
    (sync : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) Unit) :=
  runRotationWithInterruption directory before observed.lookup observed.openNew observed.cache sync

/-- After the active-file guard passes, the outer schedule records the
poisoned phase and issues the exclusive open on the canonical successor
path. The no-follow lookup and the nonreturning open preserve the original cache. -/
theorem stopsSchedule (observed : ObservedRotationCreateStop cut handle) (sync) :
    observed.runUntilCreate sync =
      .error (directory.file (.walSegment (before.installed.walBytes / WAL.frameSize)))
        (.poisoned, ⟨(observed.cache, cut.image), before.owners⟩) := by
  let path := directory.file (.walSegment (before.installed.walBytes / WAL.frameSize))
  have stopped : observed.openNew path (observed.cache, .initial before.wal) =
      .error path (observed.cache, cut.image) := observed.stopped
  obtain ⟨name, message, absent⟩ := observed.absent
  simp [runUntilCreate, runRotationWithInterruption, rotateWalSchedule, Phase.installed, cut.nonempty, observed.checked,
    publishPrepared, rotateFileCall, WalSegmentRotation.runAt_fileEffects, observeSuccessorWith, readEmptyWith,
    optionalMetadataWith, absent, path, stopped, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
    EStateM.bind, Pure.pure,
    ExceptT.pure, EStateM.pure, Except.pure]

/-- With zero returned create or sync calls, the only possible file effect
is the appearance of the empty successor. -/
theorem createEffect (observed : ObservedRotationCreateStop cut handle) :
    cut.image = .initial before.wal ∨ cut.image = ⟨before.wal.directory, .created⟩ := by
  have initial := cut.returned
  rw [observed.first] at initial
  have same : cut.reached = .initial before.wal := (EStateM.Result.ok.inj initial).2.symm
  obtain unchanged | ⟨action, invoked, applied⟩ := cut.effect
  · exact Or.inl (unchanged.trans same)
  · rw [observed.first] at invoked
    have first : action = .createEmpty := (Option.some.inj invoked).symm
    subst action
    rw [same] at applied
    exact Or.inr (Option.some.inj applied).symm

/-- The same stopped image supplies the rotation retry after power loss.
The report supplies the surviving metadata and successor binding; an
empty visible successor can change the physical keeper with no change
to the acknowledged WAL. -/
theorem startsReopen (observed : ObservedRotationCreateStop cut handle)
    (ready : before.RetainedReady directory writer)
    (barrier : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) Unit)
    (stopped : observed.runUntilCreate barrier = .error tag reached)
    {pair : DirectoryPublication.Bindings} {present : Bool}
    (metadata : pair ∈ reached.2.image.2.metadata.crashImages)
    (survives : reached.2.image.2.successor.MaySurvive present) :
    tag = directory.file (.walSegment (before.installed.walBytes / WAL.frameSize)) ∧
    reached.1 = .poisoned ∧ reached.2.image.1 = observed.cache ∧
    RotationReopenFailures directory before.wal before.history ⟨reached.2.image.2, reached.2.owners⟩
      (cut.released pair present) ∧
    pair = before.target.pair ∧
    ((cut.released pair present).image.visible before.wal).ReadLayout before.history := by
  obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj (stopped.symm.trans (observed.stopsSchedule barrier))
  have selected := cut.trace.selectsOriginal (List.mem_cons_of_mem _ metadata)
  have binding : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using selected
  have layout := (cut.released pair present).image.visibleReadLayout (ready.rotationInput cut.nonempty) ready.layout
  exact ⟨rfl, rfl, rfl, cut.startsRetry metadata survives, binding.trans ready.walPair, layout⟩

/-- After power loss chooses the successor, reported retries use that
fixed keeper. Their selected files still prepare the old history before
any attempt has returned a session. -/
theorem refinesReopenPrefix (observed : ObservedRotationCreateStop cut handle)
    (ready : before.RetainedReady directory writer)
    (barrier : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) Unit)
    (stopped : observed.runUntilCreate barrier = .error tag reached)
    {pair : DirectoryPublication.Bindings} {present : Bool}
    (metadata : pair ∈ reached.2.image.2.metadata.crashImages)
    (survives : reached.2.image.2.successor.MaySurvive present)
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory (cut.survivingWal pair present).active.first
      (cut.crashedFiles pair present) retry) :
    let keeper := (cut.survivingWal pair present).active
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (cut.crashedFiles pair present) retry ∧
    retry.image.directory.active = before.target.pair ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ Prepared retry.image layout.target layout.plan := by
  obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj (stopped.symm.trans (observed.stopsSchedule barrier))
  exact cut.refinesReportedReopenPrefix ready metadata survives reported

end ObservedRotationCreateStop

end Alvoki.Storage.DiskSession
