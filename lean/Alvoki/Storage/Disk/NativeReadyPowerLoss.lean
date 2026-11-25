import Alvoki.Storage.Disk.NativeReadyReadPrefix
import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen
import Alvoki.Storage.Disk.SegmentedReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Scope the quiet crash observation to the selected files, the captured
parent and the lock. Other directory entries have their own crash rules. -/
def NativeReadyState.crashPath (state : NativeReadyState) (path : FilePath) : Prop :=
  let directory := state.session.directory
  path = directory.path ∨ path = directory.file .lock ∨
    checkpointSurvivorPath directory state.writer state.writer.target.pair.manifest path

/-- An observed durable file in the pre-crash namespace. -/
def CheckpointSurvivingFiles.Stored (files : CheckpointSurvivingFiles) (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ inode, files.names path = some inode ∧ files.bytes inode = [payload]

/-- Disk observations for power loss after a settled ready operation.
Every relevant dentry is settled in the reported crash name maps. The
machine restart carries a new descriptor census with no live slots from
this observation. The raw namespace and inode bytes remain observations
of the filesystem at the reached ready state. -/
structure NativeReadyQuietCrash (state : NativeReadyState) where
  live : CheckpointSurvivingFiles
  directoryBound : live.names state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lockBound : live.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  manifest : match state.writer.target.pair.manifest with
    | none => live.names (state.session.directory.file .manifest) = none
    | some bytes => live.Stored (state.session.directory.file .manifest) bytes
  marker : live.Stored (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  keeper : live.Stored (state.session.directory.file (.walSegment state.writer.wal.active.first)) state.writer.wal.active.bytes
  sealedFiles : ∀ segment ∈ state.writer.wal.sealed,
    live.Stored (state.session.directory.file (.walSegment segment.first)) segment.bytes
  runs : ∀ bytes metadata, state.writer.target.pair.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
    ∀ payload, state.writer.published.durable metadata.header.generation index = some payload →
    live.Stored (state.session.directory.file (.run metadata.header.generation index)) payload
  crashNames : List (FilePath → Option Nat)
  settled : ∀ names ∈ crashNames, ∀ path, state.crashPath path → names path = live.names path
  names : FilePath → Option Nat
  chosen : names ∈ crashNames
  contents : Nat → ByteArray
  durable : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, names path = some inode → contents inode ∈ live.bytes inode
  rebootObjects : Nat → Nat

namespace NativeReadyQuietCrash

variable {state : NativeReadyState}

/-- No pre-loss slots belong to the new machine's census. Its observed
object map still identifies the files opened after the restart. -/
def reboot (crash : NativeReadyQuietCrash state) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

def retry (_crash : NativeReadyQuietCrash state) : LockedFileState FileImage :=
  state.writer.powerLossFiles state.session.directory

theorem vacant (crash : NativeReadyQuietCrash state) : TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  intro _
  simp [retry, SegmentedWriterState.powerLossFiles, LockOwners.set]

theorem directorySurvives (crash : NativeReadyQuietCrash state) :
    crash.names state.session.directory.path = some (state.census.inode state.directorySlot.description) :=
  (crash.settled crash.names crash.chosen _ (.inl rfl)).trans crash.directoryBound

theorem lockSurvives (crash : NativeReadyQuietCrash state) :
    crash.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description) :=
  (crash.settled crash.names crash.chosen _ (.inr (.inl rfl))).trans crash.lockBound

private theorem fileSurvives (crash : NativeReadyQuietCrash state) {path : FilePath} {payload : ByteArray}
    (selected : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (stored : crash.live.Stored path payload) :
    ∃ inode, crash.names path = some inode ∧ crash.contents inode = payload := by
  obtain ⟨inode, live, bytes⟩ := stored
  have bound := (crash.settled crash.names crash.chosen path (.inr (.inr selected))).trans live
  have persisted := crash.durable path selected inode bound
  rw [bytes] at persisted
  exact ⟨inode, bound, List.mem_singleton.mp persisted⟩

theorem manifestAbsent (crash : NativeReadyQuietCrash state) (absent : state.writer.target.pair.manifest = none) :
    crash.names (state.session.directory.file .manifest) = none := by
  have live := crash.manifest
  rw [absent] at live
  exact (crash.settled crash.names crash.chosen _ (.inr (.inr (.inl rfl)))).trans live

theorem manifestSurvives (crash : NativeReadyQuietCrash state) {bytes : ByteArray}
    (present : state.writer.target.pair.manifest = some bytes) :
    ∃ inode, crash.names (state.session.directory.file .manifest) = some inode ∧ crash.contents inode = bytes := by
  have stored := crash.manifest
  rw [present] at stored
  exact crash.fileSurvives (.inl rfl) stored

theorem markerSurvives (crash : NativeReadyQuietCrash state) :
    ∃ inode, crash.names (state.session.directory.file .walBoundary) = some inode ∧
      crash.contents inode = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 :=
  crash.fileSurvives (.inr (.inl (.inl rfl))) crash.marker

theorem keeperSurvives (crash : NativeReadyQuietCrash state) :
    ∃ inode, crash.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode ∧
      crash.contents inode = state.writer.wal.active.bytes :=
  crash.fileSurvives (.inr (.inl (.inr (.inl rfl)))) crash.keeper

theorem sealSurvives (crash : NativeReadyQuietCrash state) (segment : WalSegment) (member : segment ∈ state.writer.wal.sealed) :
    ∃ inode, crash.names (state.session.directory.file (.walSegment segment.first)) = some inode ∧
      crash.contents inode = segment.bytes :=
  crash.fileSurvives (.inr (.inl (.inr (.inr ⟨segment, member, rfl⟩)))) (crash.sealedFiles segment member)

theorem runSurvives (crash : NativeReadyQuietCrash state) {bytes payload : ByteArray}
    {metadata : Manifest.IntegrityCheckpoint} (present : state.writer.target.pair.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) {index : Nat}
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, crash.names (state.session.directory.file (.run metadata.header.generation index)) = some inode ∧
      crash.contents inode = payload :=
  crash.fileSurvives (.inr (.inr ⟨bytes, metadata, index, present, decoded, within, rfl⟩))
    (crash.runs bytes metadata present decoded index within payload stored)

end NativeReadyQuietCrash

/-- A healthy aligned attempt against the reported reboot namespace.
The selected reads follow one inventory from cache capture to repair. -/
structure NativeReadyRestartReads {state : NativeReadyState} (crash : NativeReadyQuietCrash state)
    (input : FilePath) (layout : CanonicalKeeperLayout crash.retry.image state.writer.history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint) where
  opening : CheckpointBarrierAlignedReports input state.session.directory crash.reboot crash.retry layout
    state.writer.published crash.vacant selected crash.names
  directoryObject : opening.reads.bindings state.session.directory.path = crash.names state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) = crash.names (state.session.directory.file .lock)
  /-- The model allocates identifiers distinct from those of this prior
  session. They record chronology across process epochs. -/
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs
  metadataRelease : FilePath → List LockReferenceDrop
  manifestDrops : List LockReferenceDrop
  manifest : CapturedManifestCensus opening.reads metadataRelease manifestDrops
  runs : CapturedRunReadCensus opening.reads (opening.admission.reached.afterDrops manifestDrops)
  markerRead : CapturedMarkerCensus opening.reads ((opening.admission.reached.afterDrops manifestDrops).afterDrops
    (runReadDrops runs.events (selectedRunCount crash.retry.image.directory.active.manifest))) metadataRelease
  chronology : opening.reads.listing.beforeOpen = manifestDrops ++
    runReadDrops runs.events (selectedRunCount crash.retry.image.directory.active.manifest) ++
    (markerRead.custody.beforeOpen ++ metadataRelease (state.session.directory.file .walBoundary))
  sealRelease : FilePath → List LockReferenceDrop
  required : List (Nat × IO.FS.Metadata)
  seals : CapturedSealReadChain opening.reads sealRelease required opening.reads.listing.afterClose
    opening.finish.readCustody.beforeOpen
  offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first
  retained : ∀ event ∈ opening.finish.readCustody.beforeOpen,
    event.removes opening.admission.owner.reference = false ∧ event.removes opening.admission.cached.reference = false

namespace NativeReadyRestartReads

variable {state : NativeReadyState} {crash : NativeReadyQuietCrash state} {input : FilePath}
  {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    crash.retry.image.directory.active.manifest state.writer.checkpoint}

def run (observed : NativeReadyRestartReads crash input layout selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  observed.opening.finish.runFromCensus observed.metadataRelease observed.runs.released observed.sealRelease

/-- The actual no-follow stat and opened description use the object that
survived power loss. The reported durable bytes come from that object. -/
def ReadsSurvivor (observed : NativeReadyRestartReads crash input layout selected)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : observed.opening.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsFile (observed : NativeReadyRestartReads crash input layout selected)
    {path : FilePath} {name : String} {object : DeviceInode} {payload : ByteArray}
    (canonical : CheckpointCrashChild crash.names observed.opening.admission path name)
    (bound : observed.opening.admission.view.child observed.opening.admission.root name = some object)
    (contents : observed.opening.reads.reads.objectBytes (observed.opening.admission.view.modelObject object) = some payload)
    (calls : RunChunkPathReport observed.opening.reads.reads path name observed.opening.admission.root
      observed.opening.admission.view)
    (survived : ∃ inode, crash.names path = some inode ∧ crash.contents inode = payload) :
    observed.ReadsSurvivor path payload := by
  obtain ⟨inode, named, durable⟩ := survived
  unfold CheckpointCrashChild at canonical
  rw [bound, Option.map_some] at canonical
  have stat := (congrArg observed.opening.admission.view.modelObject (calls.statLookup.child_eq bound)).symm.trans calls.identifiedStat
  let read := calls.observesFile bound contents
  have binding : crash.names path = some read.object := canonical.symm.trans (congrArg some stat)
  have same := Option.some.inj (binding.symm.trans named)
  exact ⟨read, binding, same.symm ▸ durable⟩

theorem readsManifest (observed : NativeReadyRestartReads crash input layout selected) {bytes : ByteArray}
    (present : state.writer.target.pair.manifest = some bytes) :
    observed.ReadsSurvivor (state.session.directory.file .manifest) bytes := by
  obtain ⟨⟨file⟩, _⟩ := observed.opening.reads.metadata.manifestFile bytes present
  exact observed.readsFile observed.opening.manifestChild file.bound file.contents file.calls (crash.manifestSurvives present)

theorem readsRun (observed : NativeReadyRestartReads crash input layout selected) {bytes payload : ByteArray}
    {metadata : Manifest.IntegrityCheckpoint} (present : state.writer.target.pair.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) {index : Nat}
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    observed.ReadsSurvivor (state.session.directory.file (.run metadata.header.generation index)) payload := by
  obtain ⟨object, bound, contents, ⟨calls⟩⟩ := observed.opening.reads.runs bytes metadata present decoded index within payload stored
  exact observed.readsFile (observed.opening.runChild bytes metadata present decoded index within) bound contents calls
    (crash.runSurvives present decoded within stored)

theorem readsMarker (observed : NativeReadyRestartReads crash input layout selected)
    (valid : state.Valid) : observed.ReadsSurvivor (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
  have marker : state.writer.files.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    congrArg Publication.Image.active valid.retained.resumed.markerImage
  have bytes : crash.retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected).symm.trans marker
  obtain ⟨file, _⟩ := observed.opening.reads.metadata.markerFile _ bytes
  exact observed.readsFile observed.opening.markerChild file.bound file.contents file.calls crash.markerSurvives

private theorem keeperNoTail (target : layout.target = state.writer.target) : layout.tail = ByteArray.empty := by
  have trimmed : state.writer.target.trimmed = layout.keeper.bytes := by rw [← target]; rfl
  have full : layout.keeper.bytes ++ layout.tail = layout.keeper.bytes :=
    Option.some.inj (layout.visible.symm.trans (congrArg some trimmed))
  have size := congrArg ByteArray.size full
  rw [ByteArray.size_append] at size
  exact ByteArray.size_eq_zero_iff.mp (by omega)

theorem readsKeeper (observed : NativeReadyRestartReads crash input layout selected)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active) :
    observed.ReadsSurvivor (state.session.directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes := by
  let file := observed.opening.reads.wal.keeper
  have survived : ∃ inode, crash.names (state.session.directory.file (.walSegment layout.keeper.first)) = some inode ∧
      crash.contents inode = layout.keeper.bytes := keeper.symm ▸ crash.keeperSurvives
  have contents : observed.opening.reads.reads.objectBytes (observed.opening.admission.view.modelObject file.object) =
      some layout.keeper.bytes := by simpa only [keeperNoTail target, ByteArray.append_empty] using file.contents
  exact observed.readsFile observed.opening.keeperChild file.bound contents file.calls survived

private theorem selectedSeals (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark) :
    ∀ segment ∈ layout.sealed, segment ∈ state.writer.wal.sealed := by
  have order := descriptors
  rw [keeper] at order
  unfold WalSegmentImage.readDescriptors at order
  by_cases needed : layout.range.watermark < state.writer.wal.active.last
  · simp only [needed, ↓reduceIte, WalSegmentImage.afterWatermark, List.filter_append,
      List.filter_cons, decide_eq_true_eq, List.filter_nil] at order
    have same := List.append_cancel_right order
    intro segment present
    exact (List.mem_filter.mp (same ▸ present)).1
  · simp only [needed, ↓reduceIte] at order
    have empty : layout.sealed = [] := List.append_cancel_right order
    simp [empty]

theorem readsSeal (observed : NativeReadyRestartReads crash input layout selected)
    (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (segment : WalSegment) (present : segment ∈ layout.sealed) :
    observed.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  let file := observed.opening.reads.wal.sealedFile segment present
  exact observed.readsFile (observed.opening.sealChild segment present) file.bound file.contents file.calls
    (crash.sealSurvives segment (selectedSeals keeper descriptors segment present))

end NativeReadyRestartReads

/-- The exact next aligned session and protected file observations
after a reported crash image. -/
abbrev NativeReadyQuietCrash.Reopened {state : NativeReadyState} (crash : NativeReadyQuietCrash state)
    (input : FilePath) (history : List WAL.Write) (log : List DatabaseSubmissions)
    (reads : List RecordedSnapshotRead) : Prop :=
    BoundedReopenTrace state.session.directory (· = state.writer.target) state.files crash.retry ∧
    crash.reboot.slots = [] ∧
    ∃ (layout : CanonicalKeeperLayout crash.retry.image state.writer.history)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        crash.retry.image.directory.active.manifest state.writer.checkpoint)
      (observed : NativeReadyRestartReads crash input layout selected) (next : NativeReadyState),
      NativeReadyReadPrefix observed.run next history log reads next ∧
      next.session.directory = state.session.directory ∧
      next.owner = observed.opening.admission.owner ∧ next.directorySlot = observed.opening.admission.cached ∧
      next.cache = observed.opening.admission.cache ∧ next.census = observed.opening.finish.census ∧
      next.session.sessionRef ≠ state.session.sessionRef ∧ next.session.phaseRef ≠ state.session.phaseRef ∧
      next.census.inode next.owner.description = state.census.inode state.owner.description ∧
      next.census.inode next.directorySlot.description = state.census.inode state.directorySlot.description ∧
      next.files.image.directory.active = state.writer.target.pair ∧
      next.writer.target = state.writer.target ∧
      next.writer.checkpoint = state.writer.checkpoint ∧ next.writer.published.durable = state.writer.published.durable ∧
      (state.writer.target.pair.manifest = none → crash.names (state.session.directory.file .manifest) = none) ∧
      (∀ bytes, state.writer.target.pair.manifest = some bytes →
        observed.ReadsSurvivor (state.session.directory.file .manifest) bytes) ∧
      (∀ bytes metadata, state.writer.target.pair.manifest = some bytes →
        Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
        ∀ payload, state.writer.published.durable metadata.header.generation index = some payload →
        observed.ReadsSurvivor (state.session.directory.file (.run metadata.header.generation index)) payload) ∧
      observed.ReadsSurvivor (state.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
      observed.ReadsSurvivor (state.session.directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes ∧
      (∀ segment ∈ layout.sealed,
        observed.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes) ∧
      ∃ reference : Sequential.SnapshotTable UInt64,
        SnapshotWalReplay .empty history reference ∧
        (∀ read ∈ reads, read.agrees reference) ∧
        GuardedAcquireReads state.writer.installed state.session reference ∧
        GuardedAcquireReads next.writer.installed next.session reference

/-- Start from a reached phase with bounded client replay. The retained
selection may have come from an operation that stopped before returning. -/
theorem NativeReadyQuietCrash.restarts
    {state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (crash : NativeReadyQuietCrash state) (valid : state.Valid)
    (originalHistory : state.writer.history = history) (pending : PendingClientReplay log reads history)
    (bounded : ∀ read ∈ reads, read.BoundedBy history.length) {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image state.writer.history,
      layout.target = state.writer.target → Prepared crash.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
        crash.retry.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeReadyRestartReads crash input layout selected)) :
    crash.Reopened input history log reads := by
  let ready := valid.retained
  obtain ⟨layout, target, keeper, descriptors, offsets, prepared⟩ := ready.powerLossLayout
  let selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint := ready.resumed.selected
  obtain ⟨observed⟩ := observe layout target prepared selected
  let opening := observed.opening
  let finish := opening.finish
  have following := opening.reads.walReads.selectedAfterWatermark offsets descriptors
  have accepted : state.writer.published.AcceptsVersioned state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) crash.retry.image.directory.active.manifest := ready.resumed.accepted
  obtain ⟨session, final, returned, finalPair, ownerLive, directoryLive, installed⟩ :=
    finish.installsFromCensus observed.manifest observed.runs observed.markerRead observed.chronology observed.seals
      observed.offsets observed.retained opening.markerFound prepared.keeperPrefix prepared.newer following
      accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have kept : crash.retry.image.kept = (state.writer.wal.checkpointReopenFiles state.writer.wal.directory none).kept :=
    ready.sealedFiles
  obtain ⟨_, _, writer, indexed, path, description, phase, exactFiles, exactOwners, _, selectedTarget, nextHistory,
    _, durable, retained⟩ := appendReady.writerRetained ready.layout ready.valid ready.spans
      (ready.walPair.trans (congrArg Target.pair target).symm) (congrArg WalSegment.first keeper) kept
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  let next : NativeReadyState := ⟨session, writer, finish.census, opening.admission.cache, opening.admission.owner,
    opening.admission.cached⟩
  have sameFiles : next.files = final := by
    change (⟨writer.files, writer.owners⟩ : LockedFileState FileImage) = final
    rw [exactFiles, exactOwners]
  have nextValid : next.Valid :=
    ⟨phase, description.symm, ownerLive, directoryLive, ⟨opening.admission.reached, rfl⟩,
      path.symm ▸ description.symm ▸ retained⟩
  have newPrefix : NativeReadyReadPrefix observed.run next history log reads next :=
    .installed (sameFiles.symm ▸ returned) nextValid (nextHistory.trans originalHistory) pending bounded
  have actualSelection := retained.resumed.selected
  rw [selectedTarget.trans target, durable] at actualSelection
  have checkpoint := actualSelection.uniqueResult ready.resumed.selected
  have sameCensus : next.census.inode = opening.admission.reached.inode := by
    unfold next CapturedAlignedFinish.census
    rw [finish.repair.opened]
    rfl
  have objects := opening.reads.sameObjects
  have sameLock := Option.some.inj (objects.2.1.symm.trans (observed.lockObject.trans crash.lockSurvives))
  have sameDirectory := Option.some.inj (objects.1.symm.trans (observed.directoryObject.trans crash.directorySurvives))
  have fresh : session.sessionRef ≠ state.session.sessionRef ∧ session.phaseRef ≠ state.session.phaseRef := by
    obtain ⟨_, _, _, _, _, indexed, _, _, _, _, _, _, _, _, _, phaseFresh, sessionFresh, _⟩ := installed
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
    exact ⟨fun same => sessionFresh (same.symm ▸ observed.earlierTokens.2),
      fun same => phaseFresh (same.symm ▸ observed.earlierTokens.1)⟩
  refine ⟨ready.powerLossTrace _, rfl, layout, selected, observed, next, newPrefix, path, rfl, rfl, rfl, rfl,
    fresh.1, fresh.2, ?_, ?_, sameFiles.symm ▸ finalPair, selectedTarget.trans target, checkpoint, durable, crash.manifestAbsent,
    fun _ present => observed.readsManifest present, fun _ _ present decoded _ within _ stored =>
      observed.readsRun present decoded within stored,
    observed.readsMarker valid, observed.readsKeeper target keeper, observed.readsSeal keeper descriptors, ?_⟩
  · change next.census.inode opening.admission.owner.description = _
    rw [sameCensus]
    exact sameLock
  · change next.census.inode opening.admission.cached.description = _
    rw [sameCensus]
    exact sameDirectory
  · obtain ⟨reference, replayed, _, _, _, earlier⟩ := pending
    obtain ⟨_, refines, represents⟩ := ready.resumed.canonical
    obtain ⟨_, nextRefines, nextRepresents⟩ := retained.resumed.canonical
    refine ⟨reference, replayed, earlier, state.session.guardedAcquireReads valid.phase fun _ floor committed =>
      represents.acquireReads refines ready.resumed.bounds (originalHistory.symm ▸ replayed) floor committed,
      next.session.guardedAcquireReads nextValid.phase fun _ floor committed =>
        nextRepresents.acquireReads nextRefines retained.resumed.bounds
          ((nextHistory.trans originalHistory).symm ▸ replayed) floor committed⟩

/-- Start the next prefix at the actual aligned open after a quiet crash.
The earlier prefix fixes the durable selection and client responses. A
new lock acquisition and the chronological primitive reports determine
the reached session, whose reads still use the same replay. -/
theorem NativeReadyReadPrefix.restartsAfterPowerLoss
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (crash : NativeReadyQuietCrash state) {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image state.writer.history,
      layout.target = state.writer.target → Prepared crash.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
        crash.retry.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeReadyRestartReads crash input layout selected)) :
    crash.Reopened input history log reads :=
  crash.restarts prior.refines.1 prior.refines.2.1 prior.refines.2.2 prior.readsBounded observe

end Alvoki.Storage.DiskSession
