import Alvoki.Storage.Disk.Proofs.Recovery.NativeUncertainRebootStageError
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRejectedOpenLineage

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair WAL.Boundary

variable {history : List WAL.Write} {log : List DatabaseSubmissions}
  {before : NativeReadPosition history log} {pending : NativePendingWrite before}
  {crash : NativeUncertainWriteCrash pending.write pending.observed} {input nextInput : FilePath}
  {layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history}

namespace RebootLongStageErrorReports

private theorem rebootSettled (crash : NativeUncertainWriteCrash pending.write pending.observed) :
    crash.retry.image.syncDirectory = crash.retry.image := by
  obtain ⟨pair, _, payload, _, names, _, survived⟩ := crash.survives
  change crash.image.syncDirectory = crash.image
  rw [survived]
  rfl

theorem atCleanup (report : RebootLongStageErrorReports crash input layout) :
    report.failure.atStage.2 = report.admission.held := by
  change { report.admission.held with image := crash.retry.image.syncDirectory } = report.admission.held
  rw [rebootSettled crash]
  rfl

/-- Both syncs leave the already settled reboot image unchanged.
The original unlock callback therefore supplies the ordinary disposal
contract at its exact reached census. -/
def cleanup (report : RebootLongStageErrorReports crash input layout) :
    NativeOpenErrorUnlock report.admission report.failure.atStage.1 where
  ownerLive := report.failure.ownerLive
  cachedLive := report.failure.directoryLive
  result := report.unlock
  observed := by
    have observed := report.unlocked
    have atStage : report.failure.atStage = (report.failure.atStage.1, report.admission.held) :=
      Prod.ext rfl report.atCleanup
    rw [atStage] at observed
    cases result : report.unlock <;>
      simpa only [result, NativeMarkedLongStageCreateError.afterUnlock, report.atCleanup] using observed

theorem cleanupFiles (report : RebootLongStageErrorReports crash input layout) :
    report.cleanup.files = report.failure.afterUnlock report.unlock := by
  cases result : report.unlock <;>
    simp only [cleanup, NativeOpenErrorUnlock.files, result, NativeMarkedLongStageCreateError.afterUnlock, report.atCleanup]

end RebootLongStageErrorReports

/-- These are the observed finalizers after the returned error. The
next admission requires successful unlock or the last old lock drop. -/
structure RebootStageErrorDisposal (report : RebootLongStageErrorReports crash input layout) where
  reached : CensusOpenState
  events : NativeOpenErrorDisposal report.cleanup reached
  released : report.unlock = .ok () ∨ reached.1.references report.admission.owner.description = []

namespace RebootStageErrorDisposal

variable {report : RebootLongStageErrorReports crash input layout}
  (disposal : RebootStageErrorDisposal report)

theorem vacant : TryLockObserves disposal.reached.2.owners before.state.session.directory (.ok true) :=
  disposal.events.admits.mpr disposal.released

def retryLayout : CanonicalKeeperLayout disposal.reached.2.image before.state.writer.history where
  range := layout.range
  decoded := (congrArg (fun image : FileImage => image.directory.active.walRange) disposal.events.preserves.2).trans layout.decoded
  through := layout.through
  first := layout.first
  sealed := layout.sealed
  keeper := layout.keeper
  chain := layout.chain
  covers := layout.covers
  tail := layout.tail
  visible := (congrArg (fun image : FileImage => image.keeper.active) disposal.events.preserves.2).trans layout.visible

theorem target : disposal.retryLayout.target = layout.target := by
  have pair := congrArg (fun image : FileImage => image.directory.active) disposal.events.preserves.2
  cases original : layout.target with
  | mk bindings range decoded first covered trimmed size =>
    have start : first = layout.keeper.first := (congrArg Target.first original).symm
    have coordinates : range = layout.range := (congrArg Target.range original).symm
    have bytes : trimmed = layout.keeper.bytes := (congrArg Target.trimmed original).symm
    have samePair : bindings = disposal.reached.2.image.directory.active := (congrArg Target.pair original).symm.trans pair.symm
    subst first range trimmed bindings
    rfl

theorem prepared (first : Prepared crash.retry.image layout.target layout.plan) :
    Prepared disposal.reached.2.image disposal.retryLayout.target disposal.retryLayout.plan := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, disposal.retryLayout.visible⟩
  · rw [disposal.target, disposal.events.preserves.2]
    exact first.keeperPrefix
  · change disposal.reached.2.image.later.Beyond layout.range.through
    rw [disposal.events.preserves.2]
    exact first.newer

theorem selected (first : SelectedIntegrityCheckpoint before.state.writer.published.durable
    crash.retry.image.directory.active.manifest before.state.writer.checkpoint) :
    SelectedIntegrityCheckpoint before.state.writer.published.durable disposal.reached.2.image.directory.active.manifest
      before.state.writer.checkpoint := by
  rw [disposal.events.preserves.2]
  exact first

end RebootStageErrorDisposal

/-- The next marked read receives the same surviving children after the
local error and disposal. The names and bytes are reported inside the
held namespace of that particular acquired lock and directory. -/
structure RebootStageRetryReports {report : RebootLongStageErrorReports crash input layout}
    (disposal : RebootStageErrorDisposal report) (nextInput : FilePath)
    (selected : SelectedIntegrityCheckpoint before.state.writer.published.durable crash.retry.image.directory.active.manifest
      before.state.writer.checkpoint) where
  opening : MarkedReadyOpenObservations nextInput before.state.session.directory disposal.reached.1 disposal.reached.2
    disposal.retryLayout before.state.writer.published disposal.vacant (disposal.selected selected)
  directory : opening.reads.bindings before.state.session.directory.path = report.reads.bindings before.state.session.directory.path
  lock : opening.reads.bindings (before.state.session.directory.file .lock) = report.reads.bindings (before.state.session.directory.file .lock)
  children : ∀ name, (opening.admission.view.child opening.admission.root name).map opening.admission.view.modelObject =
    (report.admission.view.child report.admission.root name).map report.admission.view.modelObject
  bytes : ∀ inode payload, opening.reads.reads.objectBytes inode = some payload → crash.contents inode = payload

namespace RebootStageRetryReports

variable {report : RebootLongStageErrorReports crash input layout} {disposal : RebootStageErrorDisposal report}
  {selected : SelectedIntegrityCheckpoint before.state.writer.published.durable crash.retry.image.directory.active.manifest
    before.state.writer.checkpoint}
  (next : RebootStageRetryReports disposal nextInput selected)

/-- Both opens use the same reported surviving inode at this name and
obtain its same selected bytes. The long keeper's full contents witness
its extent, while the repair schedule consumes its selected prefix. -/
def ReadsSame (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : next.opening.reads.reads.ObservesFile path payload,
    report.ReadsSurvivor path payload ∧ crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsAgain {path : FilePath} {name : String} {object : DeviceInode} {payload : ByteArray}
    (first : report.ReadsSurvivor path payload) (child : CheckpointCrashChild crash.names report.admission path name)
    (bound : next.opening.admission.view.child next.opening.admission.root name = some object)
    (contents : next.opening.reads.reads.objectBytes (next.opening.admission.view.modelObject object) = some payload)
    (call : RunChunkPathReport next.opening.reads.reads path name next.opening.admission.root next.opening.admission.view) :
    next.ReadsSame path payload := by
  have nextChild : CheckpointCrashChild crash.names next.opening.admission path name := (next.children name).trans child
  let read := call.observesFile bound contents
  exact ⟨read, first, nextChild.sameObject call bound contents, next.bytes _ _ read.contents⟩

def ReadsSameCheckpoint : Prop :=
  (∀ bytes, crash.retry.image.directory.active.manifest = some bytes →
    next.ReadsSame (before.state.session.directory.file .manifest) bytes) ∧
  ∀ bytes manifest, crash.retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
    ∀ payload, before.state.writer.published.durable manifest.header.generation index = some payload →
      next.ReadsSame (before.state.session.directory.file (.run manifest.header.generation index)) payload

theorem readsSameCheckpoint (first : report.ReadsCheckpoint) : next.ReadsSameCheckpoint := by
  have image := disposal.events.preserves.2
  constructor
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := next.opening.reads.metadata.manifestFile bytes (image.symm ▸ present)
    exact next.readsAgain (first.1 bytes present) report.manifest file.bound file.contents file.calls
  · intro bytes manifest present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := next.opening.reads.runs bytes manifest (image.symm ▸ present)
      decoded index within payload stored
    exact next.readsAgain (first.2 bytes manifest present decoded index within payload stored)
      (report.runs bytes manifest present decoded index within) bound contents calls

def ReadsSameWal : Prop :=
  (∀ bytes, crash.retry.image.directory.active.walBoundary = some bytes →
    next.ReadsSame (before.state.session.directory.file .walBoundary) bytes) ∧
  next.ReadsSame (before.state.session.directory.file (.walSegment layout.keeper.first)) (layout.keeper.bytes ++ layout.tail) ∧
  ∀ segment ∈ layout.sealed, next.ReadsSame (before.state.session.directory.file (.walSegment segment.first)) segment.bytes

theorem readsSameWal (first : report.ReadsWal) : next.ReadsSameWal := by
  refine ⟨?_, ?_, ?_⟩
  · intro bytes present
    obtain ⟨file, _⟩ := next.opening.reads.metadata.markerFile bytes (disposal.events.preserves.2.symm ▸ present)
    exact next.readsAgain (first.1 bytes present) report.marker file.bound file.contents file.calls
  · let file := next.opening.reads.wal.keeper
    exact next.readsAgain first.2.1 (report.wal _ (List.mem_append_right _ (by simp))) file.bound file.contents file.calls
  · intro segment listed
    let file := next.opening.reads.wal.sealedFile segment listed
    exact next.readsAgain (first.2.2 segment listed) (report.wal _ (List.mem_append_left _ listed))
      file.bound file.contents file.calls

end RebootStageRetryReports

/-- The reboot and the two reported attempts belong to one reached
uncertain return. The first selects a long keeper at the old marker.
The second starts only after the same failed opener's reported disposal. -/
structure NativeUncertainStageRetryObservation (pending : NativePendingWrite before) (input nextInput : FilePath) where
  crash : NativeUncertainWriteCrash pending.write pending.observed
  oldMarker : crash.retry.image.directory.active.walBoundary = before.state.writer.wal.directory.active.walBoundary
  first : ∀ layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history,
    Prepared crash.retry.image layout.target layout.plan → Nonempty (RebootLongStageErrorReports crash input layout)
  retry : ∀ layout (report : RebootLongStageErrorReports crash input layout)
    (selected : SelectedIntegrityCheckpoint before.state.writer.published.durable crash.retry.image.directory.active.manifest
      before.state.writer.checkpoint),
    ∃ disposal : RebootStageErrorDisposal report, Nonempty (RebootStageRetryReports disposal nextInput selected)

/-- The exposed ready state is the successful primitive result of the
second call. It uses the original submission ledger extended once. -/
structure NativeUncertainStageRetryContinuation (pending : NativePendingWrite before)
    (observed : NativeUncertainStageRetryObservation pending input nextInput)
    (ready : NativeReadPosition history pending.submissions) where
  layout : CanonicalKeeperLayout observed.crash.retry.image before.state.writer.history
  failedOpen : RebootLongStageErrorReports observed.crash input layout
  disposal : RebootStageErrorDisposal failedOpen
  selected : SelectedIntegrityCheckpoint before.state.writer.published.durable
    observed.crash.retry.image.directory.active.manifest before.state.writer.checkpoint
  next : RebootStageRetryReports disposal nextInput selected
  failed : ∀ bootstrap install, failedOpen.failure.run failedOpen.chronology bootstrap install =
    .error (failedOpen.failure.diagnostic failedOpen.unlock) (failedOpen.failure.atStage.1, failedOpen.cleanup.files)
  disposalInodes : disposal.reached.1.inode = failedOpen.failure.atStage.1.inode
  disposalFiles : disposal.reached.2.image = observed.crash.retry.image
  observedOpen : ready.opened = next.opening.finish.run next.opening.chronology
  returned : ready.opened = .ok ready.state.session (ready.state.census, ready.state.files)
  installed : ready.initial = ready.state
  census : ready.state.census = next.opening.finish.census
  cache : ready.state.cache = next.opening.admission.cache
  owner : ready.state.owner = next.opening.admission.owner
  directorySlot : ready.state.directorySlot = next.opening.admission.cached
  directory : ready.state.session.directory = before.state.session.directory
  checkpoint : ready.state.writer.checkpoint = before.state.writer.checkpoint
  durable : ready.state.writer.published.durable = before.state.writer.published.durable
  bindings : ready.state.files.image.directory.active = observed.crash.retry.image.directory.active
  reads : ready.reads = before.reads
  directoryInode : next.opening.reads.bindings before.state.session.directory.path =
    some (before.state.census.inode before.state.directorySlot.description)
  lockInode : next.opening.reads.bindings (before.state.session.directory.file .lock) =
    some (before.state.census.inode before.state.owner.description)
  readsCheckpoint : next.ReadsSameCheckpoint
  readsWal : next.ReadsSameWal
  replay : InstalledClientReplay pending.submissions before.reads history ready.state.writer.installed ready.state.session

/-- The old-marker reboot, returned long-keeper stage error and reported
local disposal can lead into an actual healthy marked retry. The retry
acquires the reached vacant lock, reads the same survivor, and installs
the earlier committed table with the same bounded read ledger. -/
theorem NativePendingWrite.reopensAfterOldMarkerStageError
    (pending : NativePendingWrite before) (observed : NativeUncertainStageRetryObservation pending input nextInput) :
    ∃ next, Nonempty (NativeUncertainStageRetryContinuation pending observed next) := by
  let crash := observed.crash
  obtain ⟨layout, report, failure, _, _, _, _, _, directory, lock, firstCheckpoint, firstWal, replay, bounded, seed, same⟩ :=
    pending.rejectsOldMarkerStageAfterPowerLoss crash observed.oldMarker observed.first
  subst layout
  obtain ⟨disposal, ⟨next⟩⟩ := observed.retry seed.layout report seed.selected
  have accepted : before.state.writer.published.AcceptsVersioned before.state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix before.state.writer.history) disposal.reached.2.image.directory.active.manifest := by
    rw [disposal.events.preserves.2]
    exact seed.accepted
  have historyEq := before.readPrefix.refines.2.1
  let submissions := pending.submissions
  have replayed : PendingClientReplay submissions before.reads before.state.writer.history :=
    Eq.mpr (congrArg (PendingClientReplay submissions before.reads) historyEq) replay
  have readBounds : ∀ read ∈ before.reads, read.BoundedBy before.state.writer.history.length :=
    Eq.mpr (congrArg (fun rows : List WAL.Write => ∀ read ∈ before.reads, read.BoundedBy rows.length) historyEq) bounded
  obtain ⟨state, started, cache, census, owner, slot, active, durable, checkpoint, directoryPath, _, _, _, _, _, _⟩ :=
    next.opening.finish.startsNativeReadPrefix next.opening.chronology next.opening.markerFound (disposal.prepared seed.prepared).newer
      seed.following accepted seed.ordered seed.readLayout seed.valid seed.spans (disposal.target.symm ▸ seed.active)
      seed.keeper (disposal.events.preserves.2.symm ▸ seed.kept) replayed readBounds
  have exactPrefix : NativeReadyReadPrefix (next.opening.finish.run next.opening.chronology)
      state history submissions before.reads state :=
    Eq.mp (congrArg (fun rows => NativeReadyReadPrefix (next.opening.finish.run next.opening.chronology)
      state rows submissions before.reads state) historyEq) started
  let ready : NativeReadPosition history pending.submissions :=
    ⟨next.opening.finish.run next.opening.chronology, state, state, before.reads, exactPrefix⟩
  refine ⟨ready, ⟨seed.layout, report, disposal, seed.selected, next, ?_, disposal.events.preserves.1, disposal.events.preserves.2,
    rfl, started.frames.1, rfl, census, cache, owner, slot, directoryPath, checkpoint, durable,
    active.trans (congrArg (fun image : FileImage => image.directory.active) disposal.events.preserves.2), rfl,
    next.directory.trans directory, next.lock.trans lock, next.readsSameCheckpoint firstCheckpoint, next.readsSameWal firstWal,
    ready.readPrefix.guardedReplay⟩⟩
  intro bootstrap install
  rw [report.cleanupFiles]
  exact failure bootstrap install

end Alvoki.Storage.DiskSession
