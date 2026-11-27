import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeCloseAlignedReopen
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

/-- The next admission starts with the census returned by the cache
clears, or with the census after the final observed drop of the old
owner's description. A failed unlock by itself leaves it held. -/
inductive NativeCloseRelease {state : NativeReadyState} (close : NativeReadyClose state) :
    DescriptorInventory → Prop where
  | success (reported : close.report.result = .ok ()) : NativeCloseRelease close close.report.finished.descriptors
  | failed {cause : IO.Error} (reported : close.report.result = .error cause)
      {inventory : DescriptorInventory} {reached : LockedFileState FileImage}
      (beforeDrop : LockCensusTrace state.session.directory state.session.descriptor state.census state.files inventory reached)
      (event : LockReferenceDrop) (live : inventory.references state.session.descriptor ≠ [])
      (last : (inventory.afterDrops [event]).references state.session.descriptor = []) :
      NativeCloseRelease close (inventory.afterDrops [event])

/-- Reports for one explicit close followed by the next healthy aligned
open. The selected files and callback effects are supplied locally. -/
structure NativeCloseReopenObservation (state : NativeReadyState) (input : FilePath) where
  close : NativeReadyClose state
  files : NativeCloseFiles state
  inventory : DescriptorInventory
  release : NativeCloseRelease close inventory
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
    Nonempty (NativeCloseAlignedReads files input inventory plan.layout selected)

namespace NativeCloseReopenObservation

variable {state : NativeReadyState} {input : FilePath}

/-- Record the actual explicit-close result separately from the later
successful open, retaining the exact file projection in either branch. -/
def CloseReturned (observed : NativeCloseReopenObservation state input) : Prop :=
  match observed.close.report.result with
  | .ok () => observed.close.report.run = .ok () observed.close.report.finished ∧
      observed.close.report.finished.phase = .closed ∧
      observed.close.report.finished.files = ⟨(⟨none, none, []⟩, state.files.image), state.releasedFiles.owners⟩ ∧
      observed.inventory = observed.close.report.finished.descriptors ∧
      observed.inventory = state.census.afterDrops (observed.close.report.drops .active ++
        observed.close.report.drops .pending ++ observed.close.report.drops .directory)
  | .error cause => observed.close.report.run = .error cause state.closeState ∧
      ∃ (before : DescriptorInventory) (reached : LockedFileState FileImage) (event : LockReferenceDrop),
        LockCensusTrace state.session.directory state.session.descriptor state.census state.files before reached ∧
        before.references state.session.descriptor ≠ [] ∧ reached = state.files ∧
        ¬ TryLockObserves reached.owners state.session.directory (.ok true) ∧
        (∀ reference ∈ before.references state.session.descriptor, event.removes reference = true) ∧
        observed.inventory = before.afterDrops [event] ∧ observed.inventory.references state.session.descriptor = [] ∧
        let after := before.dropLockState state.session.descriptor [event] state.session.directory reached
        after = state.releasedFiles ∧ TryLockObserves after.owners state.session.directory (.ok true)

private theorem reopens (observed : NativeCloseReopenObservation state input)
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession} {initial : NativeReadyState}
    (prior : NativeReadyReadPrefix opened initial history log reads state) :
    observed.CloseReturned ∧ NativeCloseAlignedResult observed.files input observed.inventory history log reads := by
  cases observed with
  | mk close files inventory release observe =>
    cases release with
    | success reported =>
      obtain ⟨returned, phase, cleared, census, next⟩ := prior.reopensAfterClose close reported files observe
      exact ⟨by simpa only [CloseReturned, reported, returned, phase, cleared, true_and] using census, next⟩
    | failed reported beforeDrop event live last =>
      obtain ⟨returned, same, held, removed, released, vacant, _, next⟩ :=
        prior.reopensAfterFailedUnlock close reported beforeDrop event live last files observe
      refine ⟨?_, next⟩
      simp only [CloseReturned, reported]
      exact ⟨returned, _, _, event, beforeDrop, live, same, held, removed, rfl, last, released, vacant⟩

end NativeCloseReopenObservation

/-- The original checkpoint metadata and marked WAL supply the bytes
read by the same reported open that returned the next position. -/
structure NativeCloseSelectedReads {state : NativeReadyState} {files : NativeCloseFiles state}
    {input : FilePath} {inventory : DescriptorInventory}
    {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory layout selected) : Prop where
  manifestMissing : state.writer.target.pair.manifest = none → files.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message)
  manifest : ∀ bytes, state.writer.target.pair.manifest = some bytes →
    seen.ReadsOriginal (state.session.directory.file .manifest) bytes
  runs : ∀ bytes manifest, state.writer.target.pair.manifest = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
    ∀ index < manifest.header.runCount.toNat, ∀ payload, state.writer.published.durable manifest.header.generation index = some payload →
    seen.ReadsOriginal (state.session.directory.file (.run manifest.header.generation index)) payload
  marker : seen.ReadsOriginal (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  wal : ∀ segment ∈ layout.sealed ++ [layout.keeper],
    seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes

/-- One complete close and re-admission edge of the native trace. The
close's reported result remains visible even when recovery succeeds. -/
structure NativeCloseReopenStep (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCloseReopenObservation current.state input) (next : NativeReadPosition history log) : Prop where
  closed : observed.CloseReturned
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  pair : next.state.files.image.directory.active = current.state.files.image.directory.active
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (seen : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    NativeCloseSelectedReads seen

/-- Build the common edge using the very reader supplied for this open.
The result exposes that reader's exact return and its captured custody. -/
theorem NativeCloseReopenStep.fromSelectedOpen (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCloseReopenObservation current.state input) (closed : observed.CloseReturned)
    {plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles}
    {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint}
    (seen : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected)
    (recovered : seen.SelectedResult history log current.reads) :
    ∃ next, NativeCloseReopenStep current observed next ∧ seen.run = next.opened ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      next.state.cache = seen.opening.admission.cache ∧ NativeCloseSelectedReads seen := by
  obtain ⟨state, continued, directory, owner, directorySlot, cache, census, sessionFresh,
    phaseFresh, lockInode, directoryInode, pair, kept, target, checkpoint, durable, manifestMissing, manifest,
    runs, marker, wal, _⟩ := recovered
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, continued⟩
  let reads : NativeCloseSelectedReads seen := ⟨manifestMissing, manifest, runs, marker, wal⟩
  exact ⟨next,
    ⟨closed, rfl, ⟨directory, directoryInode, lockInode, target, checkpoint, durable⟩, sessionFresh,
      phaseFresh, pair, kept, plan, selected, seen, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census, reads⟩,
    rfl, continued.frames.1, owner, directorySlot, cache, reads⟩

/-- The reported close or final reference drop flows into the actual
aligned open and supplies its fresh position for the next instruction. -/
theorem NativeReadPosition.closesAndReopens (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCloseReopenObservation current.state input) :
    ∃ next, NativeCloseReopenStep current observed next := by
  obtain ⟨closed, plan, selected, seen, recovered⟩ := observed.reopens current.readPrefix
  obtain ⟨next, step, _⟩ := NativeCloseReopenStep.fromSelectedOpen current observed closed
    (plan := plan) (selected := selected) seen recovered
  exact ⟨next, step⟩

end Alvoki.Storage.DiskSession
