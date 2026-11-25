import Alvoki.Storage.Disk.NativePendingFirstAppend
import Alvoki.Storage.Disk.NativeMarkedReadPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

/-- The first reported slot event after the interrupted write is the
append issuer's exit. Observed later drops may end lock aliases that
outlive that process. -/
structure NativeFirstAppendExit (stop : NativeFirstAppendStop prepared) where
  issuerLock : DescriptorSlot
  issuerLockLive : issuerLock ∈ stop.cutFiles.1.slots
  issuerLockDescription : issuerLock.description = state.session.descriptor
  issuerProcess : issuerLock.reference.process = stop.handle.2.1.reference.process
  exit : LockReferenceDrop
  reported : exit = .exited stop.handle.2.1.reference.process
  later : List LockReferenceDrop
  last : (stop.cutFiles.1.afterDrops (exit :: later)).references state.session.descriptor = []

namespace NativeFirstAppendExit

variable {stop : NativeFirstAppendStop prepared}

def census (seen : NativeFirstAppendExit stop) : DescriptorInventory :=
  stop.cutFiles.1.afterDrops (seen.exit :: seen.later)

def retry (_seen : NativeFirstAppendExit stop) : LockedFileState FileImage :=
  ⟨stop.files, state.files.owners.set (state.session.directory.file .lock) none⟩

theorem vacant (seen : NativeFirstAppendExit stop) :
    TryLockObserves seen.retry.owners state.session.directory (.ok true) := by
  simp [retry, TryLockObserves, LockOwners.set]

theorem noIssuerSlots (seen : NativeFirstAppendExit stop) :
    ∀ slot ∈ seen.census.slots, slot.reference.process ≠ stop.handle.2.1.reference.process := by
  intro slot present same
  have kept := (List.mem_filter.mp present).2
  have stayed := List.all_eq_true.mp kept seen.exit List.mem_cons_self
  simp [seen.reported, LockReferenceDrop.removes, same] at stayed

/-- Start the earlier append recovery proof with the exact lock references
at the interrupted callback. The exit and every later drop have the
same inventories and file authority in both interpretations. -/
theorem reaches (seen : NativeFirstAppendExit stop) (valid : state.Valid) :
    ∃ first : stop.logical.Stop state.session.descriptor,
      LockCensusTrace state.session.directory state.session.descriptor stop.cutFiles.1
        ⟨stop.files, state.files.owners⟩ seen.census seen.retry ∧
      ReportedReopenPrefix state.session.directory state.writer.wal.active.first first.origin seen.retry := by
  let initial : LockedFileState FileImage := ⟨stop.files, state.files.owners⟩
  let desc := state.session.descriptor
  have live : stop.cutFiles.1.references desc ≠ [] := List.ne_nil_of_mem
    (stop.cutFiles.1.mem_references.mpr ⟨seen.issuerLock, seen.issuerLockLive, rfl, seen.issuerLockDescription⟩)
  let references := stop.cutFiles.1.held desc live
  let first : stop.logical.Stop desc := .processExit references stop.handle.2.1.reference.process
  let afterExit := stop.cutFiles.1.afterDrops [seen.exit]
  have exited : stop.cutFiles.1.dropLockState desc [seen.exit] state.session.directory initial = first.origin := by
    simp only [DescriptorInventory.dropLockState, dite_eq_left live, seen.reported, first,
      BatchAppendInterruption.Stop.origin]
    rfl
  have started : LockCensusTrace state.session.directory desc stop.cutFiles.1 initial afterExit first.origin := by
    rw [← exited]
    exact .drops (.start valid.retained.held live) [seen.exit]
  have traced := LockCensusTrace.drops started seen.later
  have sameCensus : afterExit.afterDrops seen.later = seen.census := by
    rw [show seen.census = stop.cutFiles.1.afterDrops ([seen.exit] ++ seen.later) from rfl,
      DescriptorInventory.afterDrops_append]
  have released := traced.reached.2.2
  have last : seen.census.references desc = [] := seen.last
  rw [sameCensus, ite_eq_left last] at released
  have chosen : afterExit.dropLockState desc seen.later state.session.directory first.origin = seen.retry := released
  have full : LockCensusTrace state.session.directory desc stop.cutFiles.1 initial seen.census seen.retry := by
    rw [← sameCensus, ← chosen]
    exact traced
  refine ⟨first, full, ?_⟩
  by_cases survivor : afterExit.references desc = []
  · have same : seen.retry = first.origin := by
      rw [← chosen, DescriptorInventory.dropLockState, dite_eq_right (not_not_intro survivor)]
    rw [same]
    exact .start
  · have held : first.origin.owners.Owns state.session.directory desc := by
      have same := started.reached.2.2
      rw [ite_eq_right survivor] at same
      exact same.symm ▸ valid.retained.held
    have rest : LockCensusTrace state.session.directory desc afterExit first.origin seen.census seen.retry := by
      rw [← sameCensus, ← chosen]
      exact .drops (.start held survivor) seen.later
    exact rest.reopenTrace .start

/-- Select the live original marker's layout after the reported slots
have released the issuing writer. No reboot or new table enters the plan. -/
structure Plan (seen : NativeFirstAppendExit stop) where
  pair : seen.retry.image.directory.active = state.writer.target.pair
  layout : CanonicalKeeperLayout seen.retry.image state.writer.history
  recovery : BatchAppendInterruption.PreparedRetry state.writer layout
  selected : SelectedIntegrityCheckpoint state.writer.published.durable
    seen.retry.image.directory.active.manifest state.writer.checkpoint

theorem plans (seen : NativeFirstAppendExit stop) (valid : state.Valid) : Nonempty seen.Plan := by
  obtain ⟨first, _, reported⟩ := seen.reaches valid
  obtain ⟨_, _, pair, layout, recovery⟩ := first.refinesReopenPrefix valid.retained reported
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  exact ⟨⟨pair, layout, recovery, manifest.symm ▸ valid.retained.resumed.selected⟩⟩

end NativeFirstAppendExit

/-- The next healthy opener reports its reads and repair on the exact
released image, with a stable directory and child namespace after exit. -/
structure NativeFirstAppendExitReads {stop : NativeFirstAppendStop prepared} (seen : NativeFirstAppendExit stop)
    (input : FilePath) (layout : CanonicalKeeperLayout seen.retry.image state.writer.history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      seen.retry.image.directory.active.manifest state.writer.checkpoint) where
  opening : MarkedReadyOpenObservations input state.session.directory seen.census seen.retry layout
    state.writer.published seen.vacant selected
  view : opening.admission.view = stop.view
  root : opening.admission.root = stop.root
  earlierRefs : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧
    state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeFirstAppendExitReads

variable {stop : NativeFirstAppendStop prepared} {seen : NativeFirstAppendExit stop}
  {input : FilePath} {layout : CanonicalKeeperLayout seen.retry.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    seen.retry.image.directory.active.manifest state.writer.checkpoint}

/-- A new lock description refers to the original stable lock object, and
the captured cache still refers to the same physical parent directory. -/
theorem rootAndLock (reads : NativeFirstAppendExitReads seen input layout selected) :
    reads.opening.reads.bindings state.session.directory.path = some (stop.view.modelObject stop.root) ∧
    reads.opening.reads.bindings (state.session.directory.file .lock) = some (stop.view.modelObject stop.lock.child) := by
  have directory := reads.opening.reads.canonicalDirectory
  have identified := reads.opening.reads.canonicalLock
  have child := reads.opening.reads.lockEntry
  rw [reads.view, reads.root] at directory child
  rw [reads.view, ← stop.lock.child_eq child] at identified
  exact ⟨directory, identified⟩

theorem sameKeeper (reads : NativeFirstAppendExitReads seen input layout selected)
    (valid : state.Valid) (chosen : BatchAppendInterruption.PreparedRetry state.writer layout) :
    reads.opening.reads.wal.keeper.object = stop.keeper.child := by
  have bound := reads.opening.reads.wal.keeper.bound
  have first : layout.keeper.first = state.writer.installed.activeFirst :=
    chosen.first.trans (valid.retained.active.symm.trans valid.retained.resumed.keeper.symm)
  have path : reads.opening.admission.view.child reads.opening.admission.root (renderWalSegmentName layout.keeper.first) =
      stop.view.child stop.root prepared.keeperName := by
    rw [reads.view, reads.root, first]
  exact (stop.keeper.child_eq (path.symm.trans bound)).symm

end NativeFirstAppendExitReads

/-- The no-return append and the later admitted open share one attempt
ledger. The prior marker excludes the stopped batch from recovered data. -/
structure NativeFirstAppendExitContinuation {history : List WAL.Write} {log : List DatabaseSubmissions}
    (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeFirstAppendStop prepared)
    (seen : NativeFirstAppendExit stop) (input : FilePath)
    (next : NativeReadPosition history (log ++ [.uncertainBatch prepared.batch])) : Prop where
  stopped : NativePendingFirstAppend current stop
  released : LockCensusTrace current.state.session.directory current.state.session.descriptor stop.cutFiles.1
    ⟨stop.files, current.state.files.owners⟩ seen.census seen.retry
  issuerRetired : ∀ slot ∈ seen.census.slots, slot.reference.process ≠ stop.handle.2.1.reference.process
  issuerLockRetired : seen.issuerLock ∉ seen.census.slots
  reads : next.reads = current.reads
  path : next.state.session.directory = current.state.session.directory
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  target : next.state.writer.target = current.state.writer.target
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  marker : next.state.files.image.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen :
    ∃ (layout : CanonicalKeeperLayout seen.retry.image current.state.writer.history)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        seen.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (opened : NativeFirstAppendExitReads seen input layout selected),
      next.opened = opened.opening.finish.run opened.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.cache = opened.opening.admission.cache ∧ next.state.census = opened.opening.finish.census ∧
      next.state.owner = opened.opening.admission.owner ∧ next.state.directorySlot = opened.opening.admission.cached ∧
      opened.opening.reads.bindings current.state.session.directory.path =
        stop.bindings stop.cutFiles current.state.session.directory.path ∧
      opened.opening.reads.bindings (current.state.session.directory.file .lock) =
        stop.bindings stop.cutFiles (current.state.session.directory.file .lock) ∧
      opened.opening.reads.wal.keeper.object = stop.keeper.child ∧
      layout.keeper.bytes ++ layout.tail = current.state.writer.wal.active.bytes ++ stop.cut.visibleTail ∧
      opened.opening.reads.reads.ObservesSelected current.state.session.directory
        seen.retry.image.directory.active.manifest current.state.writer.published.durable

/-- Use one selected reader for both the exact session continuation
and the later raw returned table. -/
theorem NativeReadPosition.recoversFirstAppendAfterExitFrom (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeFirstAppendStop prepared}
    (seen : NativeFirstAppendExit stop) {input : FilePath} (plan : seen.Plan)
    (opened : NativeFirstAppendExitReads seen input plan.layout plan.selected) :
    ∃ next, NativeFirstAppendExitContinuation current stop seen input next ∧
      next.opened = opened.opening.finish.run opened.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.cache = opened.opening.admission.cache ∧ next.state.owner = opened.opening.admission.owner ∧
      next.state.directorySlot = opened.opening.admission.cached := by
  let stopped := current.stopsAtFirstAppend stop
  obtain ⟨valid, oldHistory, _⟩ := current.readPrefix.refines
  obtain ⟨_, released, _⟩ := seen.reaches valid
  obtain ⟨pair, layout, chosen, selected⟩ := plan
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  let openReport := opened.opening
  have accepted := manifest.symm ▸ valid.retained.resumed.accepted
  have replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch])
      current.reads current.state.writer.history := oldHistory.symm ▸ stopped.replay
  have bounded : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length :=
    oldHistory.symm ▸ stopped.bounded
  have pairWal := valid.retained.walPair.trans (congrArg Target.pair chosen.target).symm
  obtain ⟨after, seed, cache, census, owner, directorySlot, active, durable, checkpoint, path, target, kept,
    phaseFresh, sessionFresh⟩ := openReport.finish.startsNativeReadPrefix openReport.chronology
      openReport.markerFound chosen.prepared
      (openReport.reads.walReads.selectedAfterWatermark chosen.offsets chosen.descriptors)
      accepted valid.retained.resumed.ordered valid.retained.layout valid.retained.valid valid.retained.spans
      pairWal chosen.first (chosen.kept.trans valid.retained.sealedFiles) replay bounded
  have continued : NativeReadyReadPrefix (openReport.finish.run openReport.chronology) after history
      (log ++ [.uncertainBatch prepared.batch]) current.reads after :=
    Eq.mp (congrArg (fun journal => NativeReadyReadPrefix (openReport.finish.run openReport.chronology) after
      journal (log ++ [.uncertainBatch prepared.batch]) current.reads after) oldHistory) seed
  let next : NativeReadPosition history (log ++ [.uncertainBatch prepared.batch]) :=
    ⟨openReport.finish.run openReport.chronology, after, after, current.reads, continued⟩
  have keeper := Option.some.inj (layout.visible.symm.trans stopped.visibleKeeper)
  have bindings := stop.heldBindings stop.cutFiles (by simp [NativeFirstAppendStop.cutFiles])
  obtain ⟨directory, lock⟩ := opened.rootAndLock
  have issuerLockRetired : seen.issuerLock ∉ seen.census.slots := fun live =>
    seen.noIssuerSlots seen.issuerLock live seen.issuerProcess
  exact ⟨next, ⟨stopped, released, seen.noIssuerSlots, issuerLockRetired, rfl, path,
    fun same => phaseFresh (same.symm ▸ opened.earlierRefs.1),
    fun same => sessionFresh (same.symm ▸ opened.earlierRefs.2), target.trans chosen.target, checkpoint, durable,
    (congrArg DirectoryPublication.Bindings.walBoundary active).trans stopped.marker,
    kept.trans chosen.kept, layout, selected, opened, rfl, seed.frames.1, rfl, cache, census, owner, directorySlot,
    directory.trans bindings.1.symm, lock.trans bindings.2.1.symm,
    opened.sameKeeper valid chosen, keeper, openReport.reads.chunkReads⟩,
    rfl, seed.frames.1, cache, owner, directorySlot⟩

/-- The exact stopped write supplies the live files before process exit.
Use the observed release to select their old marked WAL, then run and
install the reported chronological native opener from that census. -/
theorem NativeReadPosition.recoversFirstAppendAfterExit (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeFirstAppendStop prepared)
    (seen : NativeFirstAppendExit stop) (input : FilePath)
    (observe : ∀ layout : CanonicalKeeperLayout seen.retry.image current.state.writer.history,
      BatchAppendInterruption.PreparedRetry current.state.writer layout →
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        seen.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeFirstAppendExitReads seen input layout selected)) :
    ∃ next, NativeFirstAppendExitContinuation current stop seen input next := by
  obtain ⟨plan⟩ := seen.plans current.readPrefix.refines.1
  obtain ⟨opened⟩ := observe plan.layout plan.recovery plan.selected
  obtain ⟨next, recovered, _⟩ := current.recoversFirstAppendAfterExitFrom seen plan opened
  exact ⟨next, recovered⟩

end Alvoki.Storage.DiskSession
