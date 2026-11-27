import Alvoki.Storage.Disk.Proofs.Collection.NativeReadyWalCollectionError
import Alvoki.Storage.Disk.NativeMarkedReadPrefix
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.ClientCachedClose
import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {state : NativeReadyState}

/-- The filesystem and descriptor state reached by a poisoned collector.
The error path supplies the original held lock and its exact binding. -/
structure NativeCollectedWal (state : NativeReadyState) where
  image : WalSealedUnlinkImage
  census : DescriptorInventory
  root : DeviceInode
  view : DirectoryReadNamespace
  lock : DeviceInode
  lockBound : view.child root "LOCK" = some lock
  lockObject : view.modelObject lock = census.inode state.owner.description
  directoryObject : view.modelObject root = census.inode state.directorySlot.description

namespace NativeCollectedWal

def closeState (reached : NativeCollectedWal state) : CachedCloseState CheckpointOpenHandle WalSealedUnlinkImage :=
  ⟨.poisoned, ⟨(state.cache, reached.image), state.files.owners⟩, reached.census⟩

def released (reached : NativeCollectedWal state) : LockedFileState FileImage :=
  let pending : LockedFileState WalSealedUnlinkImage :=
    ⟨reached.image, state.files.owners.set (state.session.directory.file .lock) none⟩
  pending.collectionReopenFiles state.writer.files.keeper.staged

theorem vacant (reached : NativeCollectedWal state) : TryLockObserves reached.released.owners state.session.directory (.ok true) := by
  intro _
  simp [released, LockedFileState.collectionReopenFiles, LockOwners.set]

end NativeCollectedWal

namespace NativeReadyWalCollection

def collected (reported : NativeReadyWalCollection state) : NativeCollectedWal state := by
  refine ⟨reported.pending.image, reported.census, reported.inventory.lifetime.root, reported.reachedView,
    reported.inventory.lifetime.lock, reported.retainsLock.2.1, reported.retainsLock.2.2, ?_⟩
  rw [reported.reachedObjects, reported.censusPreserved, ← reported.directoryMatches, ← reported.startsAt]
  exact reported.inventory.lifetime.identifiesDirectory

def poisonedCloseState (reported : NativeReadyWalCollection state) :
    CachedCloseState CheckpointOpenHandle WalSealedUnlinkImage := reported.collected.closeState

def released (reported : NativeReadyWalCollection state) : LockedFileState FileImage := reported.collected.released

theorem releasedVacant (reported : NativeReadyWalCollection state) :
    TryLockObserves reported.released.owners state.session.directory (.ok true) := reported.collected.vacant

end NativeReadyWalCollection

/-- The files visible when the failed collector returns, together with
the payloads read at the next open. The protected bindings remain stable
during the successful close and this direct retry. -/
structure NativeCollectionCloseFiles (reached : NativeCollectedWal state) where
  names : FilePath → Option Nat
  bytes : Nat → Option ByteArray
  directory : names state.session.directory.path = some (reached.census.inode state.directorySlot.description)
  child : ∀ name, names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
    (reached.view.child reached.root name).map reached.view.modelObject
  manifestAbsent : state.writer.target.pair.manifest = none → names (state.session.directory.file .manifest) = none
  manifest : ∀ payload, state.writer.target.pair.manifest = some payload →
    ∃ inode, names (state.session.directory.file .manifest) = some inode ∧ bytes inode = some payload
  marker : ∀ payload, state.writer.target.pair.walBoundary = some payload →
    ∃ inode, names (state.session.directory.file .walBoundary) = some inode ∧ bytes inode = some payload
  wal : ∀ segment ∈ reached.image.visible.segments,
    ∃ inode, names (state.session.directory.file (.walSegment segment.first)) = some inode ∧ bytes inode = some segment.bytes
  runs : ∀ manifestBytes manifest, state.writer.target.pair.manifest = some manifestBytes →
    Manifest.IntegrityCheckpoint.decode manifestBytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
    ∀ payload, state.writer.published.durable manifest.header.generation index = some payload →
    ∃ inode, names (state.session.directory.file (.run manifest.header.generation index)) = some inode ∧ bytes inode = some payload

namespace NativeCollectionCloseFiles

variable {reached : NativeCollectedWal state}

theorem lock (files : NativeCollectionCloseFiles reached) :
    files.names (state.session.directory.file .lock) = some (reached.census.inode state.owner.description) := by
  have bound := files.child "LOCK"
  change files.names (state.session.directory.file .lock) = _ at bound
  rw [bound, reached.lockBound, Option.map_some, reached.lockObject]

theorem directoryAtRoot (files : NativeCollectionCloseFiles reached) :
    files.names state.session.directory.path = some (reached.view.modelObject reached.root) :=
  files.directory.trans (congrArg some reached.directoryObject.symm)

end NativeCollectionCloseFiles

variable {reached : NativeCollectedWal state}

/-- Observe the next admission and aligned finish on the specific files
and census returned by close. Each selected child is observed in that
same namespace. -/
structure NativeCollectionAlignedReads (files : NativeCollectionCloseFiles reached) (input : FilePath)
    (inventory : DescriptorInventory)
    (selection : CoveredWalRetrySelection state.writer reached.image.visible) where
  opening : CheckpointBarrierAlignedReports input state.session.directory inventory reached.released selection.layout
    state.writer.published reached.vacant selection.checkpoint files.names
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  directoryObject : opening.reads.bindings state.session.directory.path = files.names state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) = files.names (state.session.directory.file .lock)
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeCollectionAlignedReads

variable {files : NativeCollectionCloseFiles reached} {input : FilePath} {inventory : DescriptorInventory}
  {selection : CoveredWalRetrySelection state.writer reached.image.visible}

def run (seen : NativeCollectionAlignedReads files input inventory selection) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def ReadsOriginal (seen : NativeCollectionAlignedReads files input inventory selection)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    files.names path = some read.object ∧ files.bytes read.object = some payload

private theorem readsFile (seen : NativeCollectionAlignedReads files input inventory selection)
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (pathBound : CheckpointCrashChild files.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some child)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view)
    (original : ∃ inode, files.names path = some inode ∧ files.bytes inode = some payload) :
    seen.ReadsOriginal path payload := by
  obtain ⟨inode, named, bytes⟩ := original
  unfold CheckpointCrashChild at pathBound
  rw [bound, Option.map_some] at pathBound
  have stat := (congrArg seen.opening.admission.view.modelObject (calls.statLookup.child_eq bound)).symm.trans calls.identifiedStat
  let read := calls.observesFile bound contents
  have identified : files.names path = some read.object := pathBound.symm.trans (congrArg some stat)
  exact ⟨read, identified, (Option.some.inj (identified.symm.trans named)).symm ▸ bytes⟩

theorem readsWal (seen : NativeCollectionAlignedReads files input inventory selection)
    (segment : WalSegment) (present : segment ∈ selection.layout.sealed ++ [selection.layout.keeper]) :
    seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  let wal := reached.image.visible
  have decoded : wal.directory.active.walRange = some state.writer.target.range :=
    selection.pair.symm ▸ state.writer.target.decoded
  have same := selection.retained.keepsReadDescriptors (List.mem_cons_self ..) decoded
  have descriptors : selection.layout.sealed ++ [selection.layout.keeper] = wal.readDescriptors selection.layout.range.watermark := by
    rw [selection.reads, selection.range, same]
  have stored : segment ∈ wal.segments := by
    rw [descriptors, WalSegmentImage.readDescriptors] at present
    split at present
    · exact (List.mem_filter.mp present).1
    · exact List.mem_append_right _ present
  have original := files.wal segment stored
  rcases List.mem_append.mp present with sealed | last
  · let file := seen.opening.reads.wal.sealedFile segment sealed
    exact seen.readsFile (seen.opening.sealChild segment sealed) file.bound file.contents file.calls original
  · obtain rfl := List.mem_singleton.mp last
    let file := seen.opening.reads.wal.keeper
    have contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject file.object) =
        some selection.layout.keeper.bytes := by simpa only [selection.aligned, ByteArray.append_empty] using file.contents
    exact seen.readsFile seen.opening.keeperChild file.bound contents file.calls original

end NativeCollectionAlignedReads

/-- The exact selected observations acquired by the returned open. -/
structure NativeCollectionSelectedReads {files : NativeCollectionCloseFiles reached} {input : FilePath}
    {inventory : DescriptorInventory} {selection : CoveredWalRetrySelection state.writer reached.image.visible}
    (seen : NativeCollectionAlignedReads files input inventory selection) : Prop where
  manifestMissing : state.writer.target.pair.manifest = none → files.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message)
  manifest : ∀ bytes, state.writer.target.pair.manifest = some bytes →
    seen.ReadsOriginal (state.session.directory.file .manifest) bytes
  runs : ∀ bytes manifest, state.writer.target.pair.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
    ∀ payload, state.writer.published.durable manifest.header.generation index = some payload →
    seen.ReadsOriginal (state.session.directory.file (.run manifest.header.generation index)) payload
  marker : seen.ReadsOriginal (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  wal : ∀ segment ∈ selection.layout.sealed ++ [selection.layout.keeper],
    seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes

/-- Release the exact poisoned collection state and reopen its reached files.
A selected WAL plan and chronological reports supply the actual return. -/
theorem NativeReadyReadPrefix.reopensCollectedWal
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (reached : NativeCollectedWal state)
    (close : CachedCloseReports state.session.directory state.session.descriptor reached.closeState)
    (owner : close.slot = state.owner) (closed : close.result = .ok ()) (files : NativeCollectionCloseFiles reached)
    (selection : CoveredWalRetrySelection state.writer reached.image.visible)
    {input : FilePath}
    (observe : ∀ selection : CoveredWalRetrySelection state.writer reached.image.visible,
      Nonempty (NativeCollectionAlignedReads files input close.finished.descriptors selection)) :
    close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
    close.finished.files = ⟨(⟨none, none, []⟩, reached.image), reached.released.owners⟩ ∧
    close.finished.descriptors = reached.census.afterDrops (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    close.bindings (state.session.directory.file .lock) = files.names (state.session.directory.file .lock) ∧
    ∃ (seen : NativeCollectionAlignedReads files input close.finished.descriptors selection) (next : NativeReadyState),
      NativeReadyReadPrefix seen.run next history log reads next ∧
      next.cache = seen.opening.admission.cache ∧ next.census = seen.opening.finish.census ∧
      next.owner = seen.opening.admission.owner ∧ next.directorySlot = seen.opening.admission.cached ∧
      next.session.directory = state.session.directory ∧
      next.session.phaseRef ≠ state.session.phaseRef ∧ next.session.sessionRef ≠ state.session.sessionRef ∧
      next.census.inode next.owner.description = reached.census.inode state.owner.description ∧
      next.census.inode next.directorySlot.description = reached.census.inode state.directorySlot.description ∧
      next.files.image.directory.active = state.writer.target.pair ∧ next.files.image.kept = reached.released.image.kept ∧
      next.writer.target = selection.layout.target ∧
      next.writer.checkpoint = state.writer.checkpoint ∧ next.writer.published.durable = state.writer.published.durable ∧
      NativeCollectionSelectedReads seen ∧
      InstalledClientReplay log reads history next.writer.installed next.session := by
  obtain ⟨valid, originalHistory, pending⟩ := prior.refines
  have closeReached := close.reaches (by simp [NativeCollectedWal.closeState]) valid.retained.held
  rw [CachedCloseReports.Reached, closed] at closeReached
  obtain ⟨finished, phase, cleared, finishedCensus, _⟩ := closeReached
  obtain ⟨seen⟩ := observe selection
  let opening := seen.opening
  let finish := opening.finish
  let keeper : CapturedKeeperFinish opening.callbacks opening.reads reached.vacant selection.checkpoint := .aligned finish
  have following := opening.reads.walReads.selectedAfterWatermark selection.offsets rfl
  let ready := valid.retained
  have keeperStart := congrArg WalSegment.first (selection.keeper.trans selection.retained.keepsActive.symm)
  obtain ⟨next, seeded, nextCache, nextCensus, nextOwner, nextDirectory, nextPair, nextRuns, nextCheckpoint,
    nextPath, nextTarget, nextKept, _, _, phaseFresh, sessionFresh⟩ :=
    keeper.startsNativeReadPrefix seen.chronology opening.markerFound selection.prepared.newer following selection.accepted
      ready.resumed.ordered (selection.retained.readLayout ready.layout) (selection.retained.valid ready.valid)
      (fun segment member => ready.spans segment (selection.retained.sealedSublist.subset member)) rfl keeperStart rfl
      (originalHistory.symm ▸ pending) (originalHistory.symm ▸ prior.readsBounded)
  have continued : NativeReadyReadPrefix seen.run next history log reads next := originalHistory ▸ seeded
  have sameCensus : next.census.inode = opening.admission.reached.inode := by
    change next.census = finish.census at nextCensus
    rw [nextCensus]
    change (finish.authorization.keeper.inventory.afterDrops
      (finish.repair.beforeAuthorization ++ finish.repair.afterAuthorization ++ finish.afterKeeper)).inode = _
    rw [finish.repair.opened]
    rfl
  have objects := opening.reads.sameObjects
  have sameLock := Option.some.inj (objects.2.1.symm.trans (seen.lockObject.trans files.lock))
  have sameDirectory := Option.some.inj (objects.1.symm.trans (seen.directoryObject.trans files.directory))
  have closeLock : close.bindings (state.session.directory.file .lock) = files.names (state.session.directory.file .lock) := by
    rw [close.lockObject, owner, files.lock]
    rfl
  refine ⟨finished, phase, cleared, finishedCensus, closeLock, seen, next, continued, nextCache,
    nextCensus, nextOwner, nextDirectory, nextPath, fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2), ?_, ?_, nextPair.trans selection.pair, nextKept,
    nextTarget, nextCheckpoint, nextRuns, ⟨?_, ?_, ?_, ?_, seen.readsWal⟩, continued.guardedReplay⟩
  · rw [sameCensus, nextOwner]
    exact sameLock
  · rw [sameCensus, nextDirectory]
    exact sameDirectory
  · intro absent
    have atOpen := (congrArg DirectoryPublication.Bindings.manifest selection.pair).trans absent
    exact ⟨files.manifestAbsent absent, (opening.reads.metadata.manifestMissing atOpen).2⟩
  · intro bytes present
    have atOpen := (congrArg DirectoryPublication.Bindings.manifest selection.pair).trans present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes atOpen
    exact seen.readsFile opening.manifestChild file.bound file.contents file.calls (files.manifest bytes present)
  · intro bytes manifest present decoded index within payload stored
    have atOpen := (congrArg DirectoryPublication.Bindings.manifest selection.pair).trans present
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := opening.reads.runs bytes manifest atOpen decoded index within payload stored
    exact seen.readsFile (opening.runChild bytes manifest atOpen decoded index within) bound contents calls
      (files.runs bytes manifest present decoded index within payload stored)
  · have marker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
      (congrArg DirectoryPublication.Bindings.walBoundary ready.resumed.ready.selected).symm.trans
        (congrArg Publication.Image.active ready.resumed.markerImage)
    have atOpen := (congrArg DirectoryPublication.Bindings.walBoundary selection.pair).trans marker
    obtain ⟨file, _⟩ := opening.reads.metadata.markerFile _ atOpen
    exact seen.readsFile opening.markerChild file.bound file.contents file.calls (files.marker _ marker)


/-- A collector's ordinary final sync error leaves a poisoned session.
The observed close releases that exact owner and passes its reached
inventory to a direct healthy aligned open of the remaining files. -/
theorem NativeReadyReadPrefix.reopensCollectionBarrierError
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (reported : NativeReadyWalCollection state) {cause : IO.Error}
    (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause)
    (close : CachedCloseReports state.session.directory state.session.descriptor reported.poisonedCloseState)
    (owner : close.slot = state.owner) (closed : close.result = .ok ()) (files : NativeCollectionCloseFiles reported.collected)
    {input : FilePath}
    (observe : ∀ selection : CoveredWalRetrySelection state.writer reported.collected.image.visible,
      Nonempty (NativeCollectionAlignedReads files input close.finished.descriptors selection)) :
    reported.run = .error (IO.userError s!"sync failed for '{state.session.directory.path}': {cause}")
      (.poisoned, ⟨(state.cache, reported.pending.image), reported.pending.owners⟩) ∧
    close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
    close.finished.files = ⟨(⟨none, none, []⟩, reported.pending.image), reported.released.owners⟩ ∧
    close.finished.descriptors = reported.census.afterDrops (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    close.bindings (state.session.directory.file .lock) = files.names (state.session.directory.file .lock) ∧
    ∃ (selection : CoveredWalRetrySelection state.writer reported.collected.image.visible)
      (seen : NativeCollectionAlignedReads files input close.finished.descriptors selection) (next : NativeReadyState),
      NativeReadyReadPrefix seen.run next history log reads next ∧
      next.cache = seen.opening.admission.cache ∧ next.census = seen.opening.finish.census ∧
      next.owner = seen.opening.admission.owner ∧ next.directorySlot = seen.opening.admission.cached ∧
      next.session.directory = state.session.directory ∧
      next.session.phaseRef ≠ state.session.phaseRef ∧ next.session.sessionRef ≠ state.session.sessionRef ∧
      next.census.inode next.owner.description = reported.barrier.reached.inode state.owner.description ∧
      next.census.inode next.directorySlot.description = reported.barrier.reached.inode state.directorySlot.description ∧
      next.files.image.directory.active = state.writer.target.pair ∧ next.files.image.kept = reported.released.image.kept ∧
      next.writer.target = selection.layout.target ∧
      next.writer.checkpoint = state.writer.checkpoint ∧ next.writer.published.durable = state.writer.published.durable ∧
      NativeCollectionSelectedReads seen ∧
      InstalledClientReplay log reads history next.writer.installed next.session := by
  obtain ⟨returned, _, _, _, _, _, _, _, _, _, _, _, ⟨selection⟩, _, _, _⟩ := prior.collectionBarrierFailed reported failed
  obtain ⟨finished, phase, cleared, finishedCensus, closeLock, seen, next, rest⟩ :=
    prior.reopensCollectedWal reported.collected close owner closed files selection observe
  exact ⟨returned, finished, phase, cleared, finishedCensus, closeLock, selection, seen, next, rest⟩

/-- Primitive reports for the failing collection barrier, explicit
close, and next aligned open. The reopen observes the exact visible
selection derived from the completed unlink sequence. -/
structure NativeCollectionReopenObservation (state : NativeReadyState) (input : FilePath) where
  reported : NativeReadyWalCollection state
  cause : IO.Error
  failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause
  close : CachedCloseReports state.session.directory state.session.descriptor reported.poisonedCloseState
  owner : close.slot = state.owner
  closed : close.result = .ok ()
  files : NativeCollectionCloseFiles reported.collected
  reopen : ∀ selection : CoveredWalRetrySelection state.writer reported.pending.image.visible,
    Nonempty (NativeCollectionAlignedReads files input close.finished.descriptors selection)

def NativeCollectionReopenObservation.diagnostic {input : FilePath}
    (observed : NativeCollectionReopenObservation state input) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.path}': {observed.cause}"

private theorem collectionTarget_eq {left right : Target}
    (pair : left.pair = right.pair) (range : left.range = right.range)
    (start : left.first = right.first) (bytes : left.trimmed = right.trimmed) : left = right := by
  cases left <;> cases right <;> simp_all

theorem CoveredWalRetrySelection.sameTarget {directory : DiskDirectory} {descriptor : Nat}
    {before : SegmentedWriterState} {wal : WalSegmentImage} (selected : CoveredWalRetrySelection before wal)
    (ready : before.RetainedReady directory descriptor) : selected.layout.target = before.target := by
  have keeper := selected.keeper
  have first : selected.layout.keeper.first = before.target.first :=
    (congrArg WalSegment.first keeper).trans ready.active.symm
  have bytes : selected.layout.keeper.bytes = before.target.trimmed := by
    rw [keeper, ready.layout.activeBytes, ← ready.active, ready.resumed.contents]
  exact collectionTarget_eq selected.pair selected.range first bytes

/-- The returned error, actual close, and new aligned position are one
execution edge. It preserves the read ledger and original selected
history, with the two new references allocated by the observed open. -/
structure NativeCollectionReopenContinuation (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCollectionReopenObservation current.state input) (next : NativeReadPosition history log) : Prop where
  returned : observed.reported.run = .error observed.diagnostic
    (.poisoned, ⟨(current.state.cache, observed.reported.pending.image), observed.reported.pending.owners⟩)
  closed : observed.close.run = .ok () observed.close.finished ∧ observed.close.finished.phase = .closed ∧
    observed.close.finished.files = ⟨(⟨none, none, []⟩, observed.reported.pending.image), observed.reported.released.owners⟩ ∧
    observed.close.finished.descriptors = observed.reported.census.afterDrops
      (observed.close.drops .active ++ observed.close.drops .pending ++ observed.close.drops .directory) ∧
    observed.close.bindings (current.state.session.directory.file .lock) =
      observed.files.names (current.state.session.directory.file .lock)
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  pair : next.state.files.image.directory.active = current.state.writer.target.pair
  seals : next.state.files.image.kept = observed.reported.released.image.kept
  exactOpen : ∃ (selection : CoveredWalRetrySelection current.state.writer observed.reported.pending.image.visible)
    (seen : NativeCollectionAlignedReads observed.files input observed.close.finished.descriptors selection),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    NativeCollectionSelectedReads seen

theorem NativeReadPosition.recoversCollectionBarrier (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCollectionReopenObservation current.state input) :
    ∃ next, NativeCollectionReopenContinuation current observed next := by
  obtain ⟨returned, closed, phase, cleared, afterClose, closeLock, selection, seen, state, readPrefix, cache, census, owner,
    directorySlot, directory, phaseFresh, sessionFresh, lockInode, directoryInode, pair, seals, target, checkpoint, durable,
    physical, _⟩ := current.readPrefix.reopensCollectionBarrierError observed.reported observed.failed observed.close
      observed.owner observed.closed observed.files observed.reopen
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, readPrefix⟩
  have entryInodes : observed.reported.barrier.reached.inode = current.state.census.inode := by
    have preserved := congrArg DescriptorInventory.inode observed.reported.censusPreserved
    exact preserved
  have frame : NativeReadRecoveryFrame current.state next.state :=
    ⟨directory, directoryInode.trans (congrFun entryInodes _), lockInode.trans (congrFun entryInodes _),
      target.trans (selection.sameTarget current.readPrefix.refines.1.retained), checkpoint, durable⟩
  exact ⟨next, returned, ⟨closed, phase, cleared, afterClose, closeLock⟩, rfl, frame, phaseFresh, sessionFresh,
    pair, seals, selection, seen, readPrefix.frames.1, rfl, rfl, owner, directorySlot, cache, census, physical⟩

end Alvoki.Storage.DiskSession
