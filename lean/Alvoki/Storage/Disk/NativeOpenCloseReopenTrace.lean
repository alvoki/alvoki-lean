import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeOpenClose
import Alvoki.Storage.Disk.NativeOpenChoice

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap : Type} {opened : NativeOpenedHandle heap}
  {initial current : NativeOpenedPosition opened} {input : FilePath}
  {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
  {directory : IO.Ref (Option IO.FS.Handle)}

/-- Follow a finite ready trace with the public close of its exact
table, then an aligned open from the same reported release. The
closed heap supplies the next admission census on ordinary success.
On error the original raw reply and held projection survive until
the observed last reference drop. -/
theorem NativeOpenedTrace.closesAndReopens
    (prior : NativeOpenedTrace initial instructions events current)
    (references : opened.files.UsesCacheReferences active pending directory)
    (view : OpenCloseHeapView heap FileImage) (callbacks : OpenCloseCallbacks heap)
    (samePhase : view.phase = opened.contents) (sameGet : callbacks.getPhase = opened.get)
    (sameSet : @callbacks.set (Phase Installed) = opened.set)
    (observed : NativeCloseReopenObservation current.current.ready.state input)
    (seen : OpenCloseObservation observed.close.report view callbacks opened.lock opened.phase
      active pending directory current.reached) :
    let state := current.current.ready.state
    let close := closeSchedule (opened.get opened.phase) (fun _ => callbacks.unlock opened.lock)
      (callbacks.set active none) (callbacks.set pending []) (callbacks.set directory none) (opened.set opened.phase .closed)
    opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (active.set none) (pending.set []) (directory.set none) (opened.phase.set .closed) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions),
      NativeCloseReopenStep current.current.ready observed next ∧
      NativeExecutionTrace initial.current (events ++ [.closedAndReopened input observed.close.report.result])
        ⟨current.current.history, current.current.submissions, next⟩ ∧
      match observed.close.report.result with
      | .error cause => close current.reached = .error cause seen.afterUnlock ∧
        view.Matches opened.phase active pending directory seen.afterUnlock state.closeState
      | .ok () => ∃ after,
        close current.reached = .ok () after ∧ opened.contents after opened.phase = some .closed ∧
        view.cacheAt after directory active pending = ⟨none, none, []⟩ ∧
        view.files after = state.releasedFiles ∧ view.descriptors after = observed.inventory := by
  intro state close
  obtain ⟨rawActive, rawPending, rawDirectory, uses, source⟩ := current.uses.close
  have sameActive := uses.1.symm.trans references.1
  have samePending := uses.2.1.symm.trans references.2.1
  have sameDirectory := uses.2.2.symm.trans references.2.2
  subst rawActive rawPending rawDirectory
  obtain ⟨next, reopened⟩ := current.current.ready.closesAndReopens observed
  refine ⟨source, next, reopened, .step prior.common (.closeAndReopen current.current observed next reopened), ?_⟩
  have notClosed : state.closeState.phase ≠ .closed := by
    simp [state, NativeReadyState.closeState, current.current.ready.readPrefix.refines.1.phase]
  have raw := seen.returns notClosed
  unfold OpenCloseObservation.Reached at raw
  dsimp only at raw
  rw [sameGet, sameSet] at raw
  cases result : observed.close.report.result with
  | error cause =>
    rw [result] at raw
    exact raw
  | ok value =>
    cases value
    rw [result] at raw
    obtain ⟨clears, returned, projected⟩ := raw
    have closure := reopened.closed
    simp only [NativeCloseReopenObservation.CloseReturned, result] at closure
    obtain ⟨_, phase, files, census, _⟩ := closure
    refine ⟨clears.afterPhase, returned, ?_, ?_, ?_, projected.2.2.2.trans census.symm⟩
    · rw [← samePhase, ← phase]
      exact projected.1
    · simpa only [files] using projected.2.1
    · have physical := projected.2.2.1
      rw [files] at physical
      exact physical

/-- The close/reopen reader is a marked-opening report with the already
selected checkpoint, retained WAL and chronological callbacks. Its
worker is the one that the close/reopen edge returned. -/
private def NativeCloseAlignedReads.markedReport {state : NativeReadyState} {files : NativeCloseFiles state}
    {inventory : DescriptorInventory} {plan : ClosedReadyReopenLayout state.writer state.releasedFiles}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory plan.layout selected)
    (retained : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := inventory
  retry := state.releasedFiles
  layout := plan.layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := selected
  vacant := state.releasedVacant
  opening := ⟨seen.opening.admission, seen.opening.callbacks, seen.opening.reads, .aligned seen.opening.finish,
    seen.chronology, seen.opening.marker, seen.opening.markerFound⟩
  prepared := plan.prepared
  following := seen.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  accepted := by
    have pair := plan.prepared.pair.trans (congrArg Target.pair plan.target)
    exact (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ retained.resumed.accepted
  ordered := retained.resumed.ordered
  wal := state.writer.wal
  walLayout := retained.layout
  walValid := retained.valid
  spans := retained.spans
  active := retained.walPair.trans (congrArg Target.pair plan.target).symm
  keeper := congrArg WalSegment.first plan.keeper
  kept := retained.sealedFiles
  pending := pending
  bounded := bounded

/-- Expose the exact chosen close/reopen reader as the marked report
used by the phase and cache installer. The result still points to the
same original-file reads, census and returned position. -/
theorem NativeCloseReopenStep.markedOpenReport
    {current next : NativeReadPosition history log}
    {observed : NativeCloseReopenObservation current.state input}
    (reopened : NativeCloseReopenStep current observed next) :
    ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
      (seen : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected)
      (reported : MarkedOpenSuccessReports input current.state.session.directory current.state.writer.history log current.reads),
      NativeCloseSelectedReads seen ∧ current.state.writer.history = history ∧
      reported.opening.finish.run reported.opening.chronology = next.opened ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      reported.inventory = observed.inventory ∧ reported.retry = current.state.releasedFiles ∧
      (∃ finish, reported.opening.finish = .aligned finish) ∧
      reported.opening.admission.owner = next.state.owner ∧
      reported.opening.admission.cached = next.state.directorySlot ∧
      reported.opening.admission.cache = next.state.cache := by
  obtain ⟨plan, selected, seen, returned, opened, _, owner, cached, cache, _, reads⟩ := reopened.exactOpen
  obtain ⟨valid, rows, prior⟩ := current.readPrefix.refines
  have bounded := current.readPrefix.readsBounded
  have retained : PendingClientReplay log current.reads current.state.writer.history := by
    simpa only [rows] using prior
  have inRange : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length := by
    simpa only [rows] using bounded
  let reported := seen.markedReport valid.retained retained inRange
  exact ⟨plan, selected, seen, reported, reads, rows, opened.symm, opened.trans returned,
    rfl, rfl, ⟨seen.opening.finish, rfl⟩, owner.symm, cached.symm, cache.symm⟩

end Alvoki.Storage.DiskSession
