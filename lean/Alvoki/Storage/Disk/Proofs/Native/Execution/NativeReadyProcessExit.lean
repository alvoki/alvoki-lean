import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionClose
import Alvoki.Storage.Disk.Proofs.Filesystem.LockCensusTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The writer's live slot identifies its exiting process. A reported
interval can include a private fork before exit and additional slot
drops afterwards. It carries one managed file state without an unlock. -/
structure NativeWriterProcessExit (state : NativeReadyState) (initial : DescriptorInventory)
    (source : LockedFileState FileImage) where
  beforeExit : DescriptorInventory
  filesBeforeExit : LockedFileState FileImage
  observed : LockCensusTrace state.session.directory state.session.descriptor initial source beforeExit filesBeforeExit
  writerLive : state.owner ∈ beforeExit.slots
  later : List LockReferenceDrop
  last : (beforeExit.afterDrops (.exited state.owner.reference.process :: later)).references state.session.descriptor = []

namespace NativeWriterProcessExit

variable {state : NativeReadyState} {initial : DescriptorInventory} {source : LockedFileState FileImage}

def afterExit (seen : NativeWriterProcessExit state initial source) : DescriptorInventory :=
  seen.beforeExit.afterDrops [.exited state.owner.reference.process]

def filesAfterExit (seen : NativeWriterProcessExit state initial source) : LockedFileState FileImage :=
  seen.beforeExit.dropLockState state.session.descriptor [.exited state.owner.reference.process]
    state.session.directory seen.filesBeforeExit

def census (seen : NativeWriterProcessExit state initial source) : DescriptorInventory :=
  seen.afterExit.afterDrops seen.later

def files (seen : NativeWriterProcessExit state initial source) : LockedFileState FileImage :=
  seen.afterExit.dropLockState state.session.descriptor seen.later state.session.directory seen.filesAfterExit

structure Released (seen : NativeWriterProcessExit state initial source) : Prop where
  sameBeforeExit : seen.filesBeforeExit = source
  heldBeforeExit : ¬ TryLockObserves seen.filesBeforeExit.owners state.session.directory (.ok true)
  afterExit : TryLockObserves seen.filesAfterExit.owners state.session.directory (.ok true) ↔
    seen.afterExit.references state.session.descriptor = []
  noWriterSlots : ∀ slot ∈ seen.census.slots, slot.reference.process ≠ state.owner.reference.process
  trace : LockCensusTrace state.session.directory state.session.descriptor initial source seen.census seen.files
  exactFiles : seen.files = ⟨source.image, source.owners.set (state.session.directory.file .lock) none⟩
  vacant : TryLockObserves seen.files.owners state.session.directory (.ok true)
  inodeMap : seen.census.inode = initial.inode

theorem releases (seen : NativeWriterProcessExit state initial source)
    (owner : state.owner.description = state.session.descriptor) : seen.Released := by
  have exited : LockCensusTrace state.session.directory state.session.descriptor
      initial source seen.afterExit seen.filesAfterExit :=
    .drops seen.observed [.exited state.owner.reference.process]
  have complete : LockCensusTrace state.session.directory state.session.descriptor initial source seen.census seen.files :=
    .drops exited seen.later
  have refs : seen.census.references state.session.descriptor = [] := by
    rw [census, afterExit, DescriptorInventory.afterDrops_append]
    exact seen.last
  have live : seen.beforeExit.references state.session.descriptor ≠ [] :=
    List.ne_nil_of_mem (seen.beforeExit.mem_references.mpr ⟨state.owner, seen.writerLive, rfl, owner⟩)
  have sameBeforeExit : seen.filesBeforeExit = source := by
    simpa only [ite_eq_right live] using seen.observed.reached.2.2
  have noWriterSlots : ∀ slot ∈ seen.census.slots, slot.reference.process ≠ state.owner.reference.process := by
    intro slot present same
    have afterExit := (List.mem_filter.mp present).1
    have survived := List.all_eq_true.mp (List.mem_filter.mp afterExit).2
      (.exited state.owner.reference.process) List.mem_cons_self
    simp [LockReferenceDrop.removes, same] at survived
  have released := complete.reached
  rw [ite_eq_left refs] at released
  exact ⟨sameBeforeExit, fun available => live (seen.observed.freshFlockAllowed.mp available), exited.freshFlockAllowed,
    noWriterSlots, complete, released.2.2, complete.freshFlockAllowed.mpr refs, released.2.1⟩

end NativeWriterProcessExit

/-- Exit between calls consumes no cache-unlock operation. The next
opener observes the same protected selected files on the reached census. -/
structure NativeReadyProcessExitObservation (state : NativeReadyState) (input : FilePath) where
  exit : NativeWriterProcessExit state state.census state.files
  files : NativeCloseFiles state
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
    Nonempty (NativeCloseAlignedReads files input exit.census plan.layout selected)

structure NativeReadyProcessExitReopened (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeReadyProcessExitObservation current.state input) (next : NativeReadPosition history log) : Prop where
  release : seen.exit.Released
  exactReleased : seen.exit.files = current.state.releasedFiles
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  pair : next.state.files.image.directory.active = current.state.files.image.directory.active
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (observed : NativeCloseAlignedReads seen.files input seen.exit.census plan.layout selected),
    observed.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = observed.run ∧ next.initial = next.state ∧
    next.state.owner = observed.opening.admission.owner ∧ next.state.directorySlot = observed.opening.admission.cached ∧
    next.state.cache = observed.opening.admission.cache ∧ next.state.census = observed.opening.finish.census ∧
    NativeCloseSelectedReads observed
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- Use the same chosen reader for the process-exit continuation and
its exact returned session, cache and custody. -/
theorem NativeReadPosition.reopensAfterProcessExitAt (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeReadyProcessExitObservation current.state input)
    {plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles}
    {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint}
    (reader : NativeCloseAlignedReads seen.files input seen.exit.census plan.layout selected)
    (recovered : reader.SelectedResult history log current.reads) :
    ∃ next, NativeReadyProcessExitReopened current seen next ∧ reader.run = next.opened ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.owner = reader.opening.admission.owner ∧ next.state.directorySlot = reader.opening.admission.cached ∧
      next.state.cache = reader.opening.admission.cache ∧ NativeCloseSelectedReads reader := by
  have released := seen.exit.releases current.readPrefix.refines.1.owner
  obtain ⟨state, continued, directory, owner, directorySlot, cache, census, sessionFresh,
    phaseFresh, lockInode, directoryInode, pair, kept, target, checkpoint, durable, manifestMissing, manifest,
    runs, marker, wal, replay⟩ := recovered
  let next : NativeReadPosition history log := ⟨reader.run, state, state, current.reads, continued⟩
  let reads : NativeCloseSelectedReads reader := ⟨manifestMissing, manifest, runs, marker, wal⟩
  exact ⟨next, ⟨released, released.exactFiles, rfl, ⟨directory, directoryInode, lockInode, target, checkpoint, durable⟩,
    sessionFresh, phaseFresh, pair, kept, ⟨plan, selected, reader, continued.frames.1, rfl, rfl, owner, directorySlot,
      cache, census, reads⟩, replay⟩, rfl, continued.frames.1, owner, directorySlot, cache, reads⟩

/-- The reported writer exit and alias drops lead directly to a healthy
marked open of the original checkpoint and committed replay. -/
theorem NativeReadPosition.reopensAfterProcessExit (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeReadyProcessExitObservation current.state input) :
    ∃ next, NativeReadyProcessExitReopened current seen next := by
  obtain ⟨plan, selected, reader, recovered⟩ := current.readPrefix.reopensReleasedAligned seen.files seen.observe
  obtain ⟨next, reopened, _⟩ := current.reopensAfterProcessExitAt seen (plan := plan) (selected := selected) reader recovered
  exact ⟨next, reopened⟩

end Alvoki.Storage.DiskSession
