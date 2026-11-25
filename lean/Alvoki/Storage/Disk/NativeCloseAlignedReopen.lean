import Alvoki.Storage.Disk.NativeReadyClose
import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The selected live names and bytes at the reached explicit close.
The closed file projection preserves them and the next held lookups
must refer to the same managed names. -/
structure NativeCloseFiles (state : NativeReadyState) where
  names : FilePath → Option Nat
  bytes : Nat → Option ByteArray
  directory : names state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lock : names (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  manifestAbsent : state.writer.target.pair.manifest = none → names (state.session.directory.file .manifest) = none
  manifest : ∀ payload, state.writer.target.pair.manifest = some payload →
    ∃ inode, names (state.session.directory.file .manifest) = some inode ∧ bytes inode = some payload
  marker : ∀ payload, state.writer.target.pair.walBoundary = some payload →
    ∃ inode, names (state.session.directory.file .walBoundary) = some inode ∧ bytes inode = some payload
  wal : ∀ segment ∈ state.writer.wal.sealed ++ [state.writer.wal.active],
    ∃ inode, names (state.session.directory.file (.walSegment segment.first)) = some inode ∧ bytes inode = some segment.bytes
  runs : ∀ manifestBytes manifest, state.writer.target.pair.manifest = some manifestBytes →
    IntegrityCheckpoint.decode manifestBytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
    ∀ payload, state.writer.published.durable manifest.header.generation index = some payload →
    ∃ inode, names (state.session.directory.file (.run manifest.header.generation index)) = some inode ∧ bytes inode = some payload

theorem NativeReadyState.releasedVacant (state : NativeReadyState) :
    TryLockObserves state.releasedFiles.owners state.session.directory (.ok true) := by
  intro _
  simp [releasedFiles, LockOwners.set]

/-- The next native execution starts in the returned close census. The
separately issued admission and selected reads use the protected names
from the closing writer. The successful aligned barriers are observed. -/
structure NativeCloseAlignedReads {state : NativeReadyState} (files : NativeCloseFiles state)
    (input : FilePath) (inventory : DescriptorInventory)
    (layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint) where
  opening : CheckpointBarrierAlignedReports input state.session.directory inventory state.releasedFiles layout
    state.writer.published state.releasedVacant selected files.names
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  directoryObject : opening.reads.bindings state.session.directory.path = files.names state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) = files.names (state.session.directory.file .lock)
  differentLock : opening.admission.owner.description ≠ state.session.descriptor
  differentDirectory : opening.admission.cached.description ≠ state.session.descriptor
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeCloseAlignedReads

variable {state : NativeReadyState} {files : NativeCloseFiles state} {input : FilePath} {inventory : DescriptorInventory}
  {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}

def run (seen : NativeCloseAlignedReads files input inventory layout selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def admission (seen : NativeCloseAlignedReads files input inventory layout selected) :
    NativeCloseAdmission state input inventory state.releasedFiles :=
  ⟨seen.opening.admission, seen.differentLock, seen.differentDirectory,
    Option.some.inj (seen.opening.reads.sameObjects.2.1.symm.trans (seen.lockObject.trans files.lock)),
    seen.opening.admission.opened.captures.2.2.2.2.1.trans
      (Option.some.inj (seen.opening.reads.sameObjects.1.symm.trans (seen.directoryObject.trans files.directory)))⟩

/-- The exact native stat and payload reader refer to the original inode
and to the bytes observed at the preceding explicit close. -/
def ReadsOriginal (seen : NativeCloseAlignedReads files input inventory layout selected)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    files.names path = some read.object ∧ files.bytes read.object = some payload

private theorem readsFile (seen : NativeCloseAlignedReads files input inventory layout selected)
    {path : FilePath} {name : String} {object : DeviceInode} {payload : ByteArray}
    (canonical : CheckpointCrashChild files.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some object)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject object) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view)
    (original : ∃ inode, files.names path = some inode ∧ files.bytes inode = some payload) :
    seen.ReadsOriginal path payload := by
  obtain ⟨inode, named, bytes⟩ := original
  unfold CheckpointCrashChild at canonical
  rw [bound, Option.map_some] at canonical
  have stat := (congrArg seen.opening.admission.view.modelObject (calls.statLookup.child_eq bound)).symm.trans calls.identifiedStat
  let read := calls.observesFile bound contents
  have binding : files.names path = some read.object := canonical.symm.trans (congrArg some stat)
  have same := Option.some.inj (binding.symm.trans named)
  exact ⟨read, binding, same.symm ▸ bytes⟩

theorem readsManifest (seen : NativeCloseAlignedReads files input inventory layout selected)
    (pair : state.releasedFiles.image.directory.active = state.writer.target.pair) {bytes : ByteArray}
    (present : state.writer.target.pair.manifest = some bytes) :
    seen.ReadsOriginal (state.session.directory.file .manifest) bytes := by
  have selected := (congrArg DirectoryPublication.Bindings.manifest pair).trans present
  obtain ⟨⟨file⟩, _⟩ := seen.opening.reads.metadata.manifestFile bytes selected
  exact seen.readsFile seen.opening.manifestChild file.bound file.contents file.calls (files.manifest bytes present)

theorem manifestMissing (seen : NativeCloseAlignedReads files input inventory layout selected)
    (pair : state.releasedFiles.image.directory.active = state.writer.target.pair)
    (absent : state.writer.target.pair.manifest = none) :
    files.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message) :=
  ⟨files.manifestAbsent absent,
    (seen.opening.reads.metadata.manifestMissing ((congrArg DirectoryPublication.Bindings.manifest pair).trans absent)).2⟩

theorem readsRun (seen : NativeCloseAlignedReads files input inventory layout selected)
    (pair : state.releasedFiles.image.directory.active = state.writer.target.pair) {bytes payload : ByteArray}
    {manifest : IntegrityCheckpoint} (present : state.writer.target.pair.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) {index : Nat} (within : index < manifest.header.runCount.toNat)
    (stored : state.writer.published.durable manifest.header.generation index = some payload) :
    seen.ReadsOriginal (state.session.directory.file (.run manifest.header.generation index)) payload := by
  have selected := (congrArg DirectoryPublication.Bindings.manifest pair).trans present
  obtain ⟨object, bound, contents, ⟨calls⟩⟩ := seen.opening.reads.runs bytes manifest selected decoded index within payload stored
  exact seen.readsFile (seen.opening.runChild bytes manifest selected decoded index within) bound contents calls
    (files.runs bytes manifest present decoded index within payload stored)

theorem readsMarker (seen : NativeCloseAlignedReads files input inventory layout selected)
    (pair : state.releasedFiles.image.directory.active = state.writer.target.pair) {bytes : ByteArray}
    (present : state.writer.target.pair.walBoundary = some bytes) :
    seen.ReadsOriginal (state.session.directory.file .walBoundary) bytes := by
  have selected := (congrArg DirectoryPublication.Bindings.walBoundary pair).trans present
  obtain ⟨file, _⟩ := seen.opening.reads.metadata.markerFile bytes selected
  exact seen.readsFile seen.opening.markerChild file.bound file.contents file.calls (files.marker bytes present)

theorem readsWal (seen : NativeCloseAlignedReads files input inventory layout selected)
    (aligned : layout.tail = ByteArray.empty)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (segment : WalSegment) (present : segment ∈ layout.sealed ++ [layout.keeper]) :
    seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  have full : segment ∈ state.writer.wal.sealed ++ [state.writer.wal.active] := by
    rw [descriptors, WalSegmentImage.readDescriptors] at present
    split at present
    · exact (List.mem_filter.mp present).1
    · exact List.mem_append_right _ present
  have original := files.wal segment full
  rcases List.mem_append.mp present with sealed | last
  · let file := seen.opening.reads.wal.sealedFile segment sealed
    exact seen.readsFile (seen.opening.sealChild segment sealed) file.bound file.contents file.calls original
  · obtain rfl := List.mem_singleton.mp last
    let file := seen.opening.reads.wal.keeper
    have contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject file.object) =
        some layout.keeper.bytes := by simpa only [aligned, ByteArray.append_empty] using file.contents
    exact seen.readsFile seen.opening.keeperChild file.bound contents file.calls original

end NativeCloseAlignedReads

/-- The exact successful close supplies both the files and the census
to a chronological, healthy aligned open. The earlier responses still
agree with the replay used by the new live session. -/
theorem NativeReadyReadPrefix.reopensAfterClose
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (close : NativeReadyClose state) (success : close.report.result = .ok ()) (files : NativeCloseFiles state)
    {input : FilePath}
    (observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
      ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input close.report.finished.descriptors plan.layout selected)) :
    close.report.run = .ok () close.report.finished ∧ close.report.finished.phase = .closed ∧
    close.report.finished.files = ⟨(⟨none, none, []⟩, state.files.image), state.releasedFiles.owners⟩ ∧
    close.report.finished.descriptors = state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    ∃ (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint)
      (seen : NativeCloseAlignedReads files input close.report.finished.descriptors plan.layout selected)
      (next : NativeReadyState),
      NativeReadyReadPrefix seen.run next history log reads next ∧
      next.session.directory = state.session.directory ∧ next.owner = seen.opening.admission.owner ∧
      next.directorySlot = seen.opening.admission.cached ∧ next.cache = seen.opening.admission.cache ∧
      next.census = seen.opening.finish.census ∧
      next.session.sessionRef ≠ state.session.sessionRef ∧ next.session.phaseRef ≠ state.session.phaseRef ∧
      next.census.inode next.owner.description = state.census.inode state.owner.description ∧
      next.census.inode next.directorySlot.description = state.census.inode state.directorySlot.description ∧
      next.files.image.directory.active = state.files.image.directory.active ∧
      next.files.image.kept = state.files.image.kept ∧
      next.writer.target = state.writer.target ∧ next.writer.checkpoint = state.writer.checkpoint ∧
      next.writer.published.durable = state.writer.published.durable ∧
      (state.writer.target.pair.manifest = none → files.names (state.session.directory.file .manifest) = none ∧
        ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
          .error (.noFileOrDirectory name 2 message)) ∧
      (∀ bytes, state.writer.target.pair.manifest = some bytes → seen.ReadsOriginal (state.session.directory.file .manifest) bytes) ∧
      (∀ bytes manifest, state.writer.target.pair.manifest = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
        ∀ index < manifest.header.runCount.toNat, ∀ payload, state.writer.published.durable manifest.header.generation index = some payload →
        seen.ReadsOriginal (state.session.directory.file (.run manifest.header.generation index)) payload) ∧
      seen.ReadsOriginal (state.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
      (∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
        seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes) ∧
      InstalledClientReplay log reads history next.writer.installed next.session := by
  obtain ⟨valid, originalHistory, pending⟩ := prior.refines
  obtain ⟨closed, phase, cleared, census, _⟩ := close.closes valid success
  let ready := valid.retained
  obtain ⟨plan⟩ : Nonempty (ClosedReadyReopenLayout state.writer state.releasedFiles) := ready.cleanReopenLayout
  have pair := plan.prepared.pair.trans (congrArg Target.pair plan.target)
  have binding := congrArg DirectoryPublication.Bindings.manifest pair
  let selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint := binding.symm ▸ ready.resumed.selected
  have accepted : state.writer.published.AcceptsVersioned state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) state.releasedFiles.image.directory.active.manifest :=
    binding.symm ▸ ready.resumed.accepted
  obtain ⟨seen⟩ := observe plan selected
  let opening := seen.opening
  let finish := opening.finish
  let chrono := seen.chronology
  have following := opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  obtain ⟨session, final, returned, finalPair, ownerLive, directoryLive, installed⟩ := finish.installsFromCensus
    chrono.manifest chrono.runs chrono.marker chrono.beforeListing chrono.seals chrono.offsets chrono.retained
    opening.markerFound plan.prepared.keeperPrefix plan.prepared.newer following accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  obtain ⟨_, _, writer, indexed, path, description, newPhase, exactFiles, exactOwners, wal, selectedTarget, nextHistory,
    _, durable, retained⟩ := appendReady.writerRetained ready.layout ready.valid ready.spans
      (ready.walPair.trans (congrArg Target.pair plan.target).symm) (congrArg WalSegment.first plan.keeper) ready.sealedFiles
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  let next : NativeReadyState := ⟨session, writer, finish.census, opening.admission.cache, opening.admission.owner,
    opening.admission.cached⟩
  have sameFiles : next.files = final := by
    change (⟨writer.files, writer.owners⟩ : LockedFileState FileImage) = final
    rw [exactFiles, exactOwners]
  have nextValid : next.Valid := ⟨newPhase, description.symm, ownerLive, directoryLive,
    ⟨opening.admission.reached, rfl⟩, path.symm ▸ description.symm ▸ retained⟩
  have continued : NativeReadyReadPrefix seen.run next history log reads next :=
    .installed (sameFiles.symm ▸ returned) nextValid (nextHistory.trans originalHistory) pending
  have nextTarget := selectedTarget.trans plan.target
  have chosen := retained.resumed.selected
  rw [nextTarget, durable] at chosen
  have checkpoint := chosen.uniqueResult ready.resumed.selected
  have fresh : session.sessionRef ≠ state.session.sessionRef ∧ session.phaseRef ≠ state.session.phaseRef := by
    obtain ⟨_, _, _, _, _, indexed, _, _, _, _, _, _, _, _, _, phaseFresh, sessionFresh, _⟩ := installed
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
    exact ⟨fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2),
      fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1)⟩
  have sameCensus : next.census.inode = opening.admission.reached.inode := by
    unfold next CapturedAlignedFinish.census
    rw [finish.repair.opened]
    rfl
  have marker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary ready.resumed.ready.selected).symm.trans
      (congrArg Publication.Image.active ready.resumed.markerImage)
  refine ⟨closed, phase, cleared, census, plan, selected, seen, next, continued, path, rfl, rfl, rfl, rfl,
    fresh.1, fresh.2, ?_, ?_, sameFiles.symm ▸ finalPair, ?_, nextTarget, checkpoint, durable, seen.manifestMissing pair,
    fun _ present => seen.readsManifest pair present, fun _ _ present decoded _ within _ stored =>
      seen.readsRun pair present decoded within stored,
    seen.readsMarker pair marker, seen.readsWal plan.aligned plan.descriptors, continued.guardedReplay⟩
  · change next.census.inode opening.admission.owner.description = _
    rw [sameCensus]
    exact seen.admission.lockObject
  · change next.census.inode opening.admission.cached.description = _
    rw [sameCensus]
    exact opening.admission.opened.captures.2.2.2.2.1.symm.trans seen.admission.directoryObject
  · have kept := retained.sealedFiles
    change writer.files.kept = state.writer.files.kept
    rw [kept, wal]
    exact ready.sealedFiles.symm

end Alvoki.Storage.DiskSession
