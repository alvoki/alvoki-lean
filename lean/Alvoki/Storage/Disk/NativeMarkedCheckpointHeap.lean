import Alvoki.Storage.Disk.NativeAlignedKeeperCache

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

structure MarkedTemporaryReadCalls (heap : Type) where
  stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  readChunk : IO.FS.Handle → USize → EStateM IO.Error heap ByteArray
  release : IO.FS.Handle → EStateM IO.Error heap Unit

/-- Successful read scope with the observed release of its temporary
handle. The native adapter releases this handle when its scope exits. -/
def MarkedTemporaryReadCalls.readWith (calls : MarkedTemporaryReadCalls heap) (path : FilePath)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray) : EStateM IO.Error heap ByteArray := do
  let file ← calls.openRead path
  let bytes ← read file
  calls.release file
  pure bytes

private def MarkedTemporaryReadCalls.readMetadata (calls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (path : FilePath) (metadata : IO.FS.Metadata) (file : IO.FS.Handle) : EStateM IO.Error heap ByteArray :=
  if path == directory.file .walBoundary then
    readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (calls.readChunk file)
      WAL.Boundary.acquisitionLimit ByteArray.empty
  else
    readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat

def MarkedTemporaryReadCalls.readOptional (calls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (path : FilePath) : EStateM IO.Error heap (Option ByteArray) :=
  readOptionalDatabaseFileWithMetadata (calls.stat path)
    (fun metadata => calls.readWith path (calls.readMetadata directory path metadata))
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw

theorem MarkedTemporaryReadCalls.readOptionalManifest (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) {before after : heap} {metadata : IO.FS.Metadata} {bytes : ByteArray}
    (stat : calls.stat (directory.file .manifest) before = .ok (.ok metadata) before)
    (regular : metadata.type = .file)
    (read : calls.readWith (directory.file .manifest)
      (fun file => readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat) before = .ok bytes after) :
    calls.readOptional directory (directory.file .manifest) before = .ok (some bytes) after := by
  have schedule : calls.readMetadata directory (directory.file .manifest) metadata =
      fun file => readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat := by
    funext file
    simp [MarkedTemporaryReadCalls.readMetadata, manifestPath_ne_boundary]
  simp [readOptional, schedule, readOptionalDatabaseFileWithMetadata, stat, regular,
    read, show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

def MarkedTemporaryReadCalls.runSize (calls : MarkedTemporaryReadCalls heap) (path : FilePath) :
    EStateM IO.Error heap Nat := do
  let metadata ← liftExcept (← calls.stat path)
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  pure metadata.byteSize.toNat

private def MarkedTemporaryReadCalls.runRead (calls : MarkedTemporaryReadCalls heap) (count : Nat)
    (file : IO.FS.Handle) : EStateM IO.Error heap ByteArray :=
  readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (calls.readChunk file) count ByteArray.empty

def MarkedTemporaryReadCalls.runPrefix (calls : MarkedTemporaryReadCalls heap) (path : FilePath)
    (count : Nat) : EStateM IO.Error heap ByteArray :=
  calls.readWith path (calls.runRead count)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published}
  {keeper : CapturedKeeperOpenReports reads} {heap : Type}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}

/-- A read callback leaves the original raw cache cells and locked file
projection unchanged. Temporary descriptor custody is tracked separately. -/
structure MarkedReadCacheFrame (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (before after : heap) : Prop where
  directoryCell : view.directory after seed.directoryRef = view.directory before seed.directoryRef
  activeCell : view.active after seed.activeRef = view.active before seed.activeRef
  pendingCell : view.pending after seed.pendingRef = view.pending before seed.pendingRef
  directoryHandle : view.handle after seed.handle = view.handle before seed.handle
  files : view.files after = view.files before

theorem MarkedReadCacheFrame.refl (seed : OpenSyncCacheAllocations admission.opened view init entry) (state : heap) :
    MarkedReadCacheFrame seed state state := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem MarkedReadCacheFrame.trans (left : MarkedReadCacheFrame seed before middle)
    (right : MarkedReadCacheFrame seed middle after) : MarkedReadCacheFrame seed before after :=
  ⟨right.directoryCell.trans left.directoryCell, right.activeCell.trans left.activeCell,
    right.pendingCell.trans left.pendingCell, right.directoryHandle.trans left.directoryHandle,
    right.files.trans left.files⟩

theorem MarkedReadCacheFrame.keepsInitialCache (frame : MarkedReadCacheFrame seed seed.afterPending after) :
    view.cacheAt after seed.directoryRef seed.activeRef seed.pendingRef =
      view.cacheAt seed.afterPending seed.directoryRef seed.activeRef seed.pendingRef := by
  simp only [OpenCloseHeapView.cacheAt, frame.directoryCell, frame.activeCell, frame.pendingCell, seed.pendingSet,
    seed.activeKept, seed.activeSet, seed.directoryKept, seed.directorySet, Option.map_none, Option.map_some,
    List.map_nil, frame.directoryHandle]

/-- The raw open, bounded read and release all use the selected temporary
handle. The release report connects its reached heap to the same census
as the chronological descriptor model. -/
structure MarkedTemporaryReadReport (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (calls : MarkedTemporaryReadCalls heap) (path : FilePath) (drops : List LockReferenceDrop)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray) (bytes : ByteArray) (before after : heap) where
  file : IO.FS.Handle
  opened : heap
  finished : heap
  openedRaw : calls.openRead path before = .ok file opened
  sameOpened : reads.reads.openRead path = .ok (view.handle opened file)
  readRaw : read file opened = .ok bytes finished
  sameSlot : (view.handle finished file).2.1 = (view.handle opened file).2.1
  releasedRaw : calls.release file finished = .ok () after
  census : view.descriptors after = (view.handle opened file).1.afterDrops drops
  openFrame : MarkedReadCacheFrame seed before opened
  readFrame : MarkedReadCacheFrame seed opened finished
  releaseFrame : MarkedReadCacheFrame seed finished after

theorem MarkedTemporaryReadReport.returns {calls : MarkedTemporaryReadCalls heap}
    {read : IO.FS.Handle → EStateM IO.Error heap ByteArray}
    (report : MarkedTemporaryReadReport (reads := reads) seed calls path drops read bytes before after) :
    calls.readWith path read before = .ok bytes after ∧ MarkedReadCacheFrame seed before after := by
  refine ⟨?_, (report.openFrame.trans report.readFrame).trans report.releaseFrame⟩
  simp [MarkedTemporaryReadCalls.readWith, Bind.bind, EStateM.bind, report.openedRaw, report.readRaw,
    report.releasedRaw, Pure.pure, EStateM.pure]

theorem MarkedTemporaryReadReport.censusAfter {calls : MarkedTemporaryReadCalls heap}
    {read : IO.FS.Handle → EStateM IO.Error heap ByteArray}
    {name : String} {file : RunChunkPathReport reads.reads path name admission.root admission.view}
    {initial : DescriptorInventory} (custody : TemporaryPrefixCustody file initial drops)
    (raw : MarkedTemporaryReadReport (reads := reads) seed calls path drops read bytes before after) :
    view.descriptors after = initial.afterDrops (custody.beforeOpen ++ drops) ∧
    (view.descriptors after).references file.slot.description = [] ∧
    (view.handle raw.finished raw.file).2.1 = file.slot := by
  have same := (Except.ok.inj (raw.sameOpened.symm.trans file.opened))
  have releaseSlot := raw.sameSlot.trans (congrArg (fun handle : CheckpointOpenHandle => handle.2.1) same)
  rw [raw.census, same]
  exact ⟨(custody.closes (released := fun _ => drops)).1,
    (custody.closes (released := fun _ => drops)).2, releaseSlot⟩

private theorem MarkedTemporaryReadReport.readsOptional {calls : MarkedTemporaryReadCalls heap}
    {name : String} {file : RunChunkPathReport reads.reads path name admission.root admission.view}
    (stat : calls.stat path before = .ok ((reads.reads.stat path).map Prod.fst) before)
    (raw : MarkedTemporaryReadReport (reads := reads) seed calls path drops
      (calls.readMetadata directory path file.metadata) bytes before after) :
    calls.readOptional directory path before = .ok (some bytes) after := by
  simp [MarkedTemporaryReadCalls.readOptional, readOptionalDatabaseFileWithMetadata, stat, file.stat, file.regular,
    raw.returns.1, show (IO.FS.FileType.file == .file) = true from rfl, Except.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- The same raw temporary reader reaches the accepted manifest, its
selected runs in index order, and the bounded marker. The state after the
marker is ready for the directory scan of this marked open. -/
structure NativeMarkedCheckpointReadHeap (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (chronology : CapturedMarkedReadCensus reads keeper) (calls : MarkedTemporaryReadCalls heap) where
  atRun : Nat → heap
  atScan : heap
  manifestStat : calls.stat (directory.file .manifest) seed.afterPending =
    .ok ((reads.reads.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
  noManifest : retry.image.directory.active.manifest = none → atRun 0 = seed.afterPending
  manifestRead : ∀ bytes, retry.image.directory.active.manifest = some bytes →
    ∀ file : HeldMetadataFile reads.reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes,
      Nonempty (MarkedTemporaryReadReport (reads := reads) seed calls (directory.file .manifest)
        (chronology.metadataRelease (directory.file .manifest))
        (calls.readMetadata directory (directory.file .manifest) file.calls.metadata) bytes seed.afterPending (atRun 0))
  runStat : ∀ bytes manifest, retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
      let path := directory.file (.run manifest.header.generation index)
      calls.stat path (atRun index) = .ok ((reads.reads.stat path).map Prod.fst) (atRun index)
  runRead : ∀ bytes manifest, retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat, ∀ payload,
      published.durable manifest.header.generation index = some payload →
        let path := directory.file (.run manifest.header.generation index)
        Nonempty (MarkedTemporaryReadReport (reads := reads) seed calls path (chronology.runs.released path)
          (calls.runRead payload.size) payload (atRun index) (atRun (index + 1)))
  markerStat : calls.stat (directory.file .walBoundary)
      (atRun (selectedRunCount retry.image.directory.active.manifest)) =
    .ok ((reads.reads.stat (directory.file .walBoundary)).map Prod.fst)
      (atRun (selectedRunCount retry.image.directory.active.manifest))
  markerRead : MarkedTemporaryReadReport (reads := reads) seed calls (directory.file .walBoundary)
    (chronology.metadataRelease (directory.file .walBoundary))
    (calls.readMetadata directory (directory.file .walBoundary) chronology.marker.file.calls.metadata)
    chronology.marker.bytes (atRun (selectedRunCount retry.image.directory.active.manifest)) atScan

private theorem CapturedManifestCensus.observedFile {release : FilePath → List LockReferenceDrop}
    {drops : List LockReferenceDrop} (seen : CapturedManifestCensus reads release drops) :
    (retry.image.directory.active.manifest = none ∧ drops = []) ∨
    ∃ (bytes : ByteArray) (file : HeldMetadataFile reads.reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes)
      (custody : TemporaryPrefixCustody file.calls admission.reached (release (directory.file .manifest))),
      retry.image.directory.active.manifest = some bytes ∧
      drops = custody.beforeOpen ++ release (directory.file .manifest) := by
  cases seen with
  | missing bound => exact .inl ⟨bound, rfl⟩
  | present bound file _ custody => exact .inr ⟨_, file, custody, bound, rfl⟩

namespace NativeMarkedCheckpointReadHeap

variable {chronology : CapturedMarkedReadCensus reads keeper} {calls : MarkedTemporaryReadCalls heap}

private theorem manifest (report : NativeMarkedCheckpointReadHeap seed chronology calls) :
    calls.readOptional directory (directory.file .manifest) seed.afterPending =
      .ok retry.image.directory.active.manifest (report.atRun 0) ∧
    MarkedReadCacheFrame seed seed.afterPending (report.atRun 0) ∧
      view.descriptors (report.atRun 0) = admission.reached.afterDrops chronology.manifestDrops := by
  rcases chronology.manifest.observedFile with ⟨bound, noDrops⟩ | ⟨bytes, file, custody, bound, drops⟩
  ·
    obtain ⟨_, name, message, missing⟩ := reads.metadata.manifestMissing bound
    have stat := report.manifestStat
    rw [missing] at stat
    have same := report.noManifest bound
    refine ⟨?_, same.symm ▸ MarkedReadCacheFrame.refl seed seed.afterPending, ?_⟩
    · simp [MarkedTemporaryReadCalls.readOptional, readOptionalDatabaseFileWithMetadata, stat,
        Except.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, bound, same]
    · rw [same, noDrops]
      have initial : view.descriptors seed.afterPending = admission.reached :=
        seed.pendingSlots.trans (seed.activeSlots.trans (seed.directorySlots.trans seed.openedSlots))
      rw [initial]
      generalize admission.reached = before
      cases before
      simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
  · obtain ⟨raw⟩ := report.manifestRead bytes bound file
    rw [bound, drops]
    exact ⟨raw.readsOptional report.manifestStat, raw.returns.2, (raw.censusAfter custody).1⟩

private theorem readsRun (report : NativeMarkedCheckpointReadHeap seed chronology calls)
    {bytes : ByteArray} {manifest : IntegrityCheckpoint} (bound : retry.image.directory.active.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) {index : Nat} (within : index < manifest.header.runCount.toNat)
    {payload : ByteArray} (stored : published.durable manifest.header.generation index = some payload) :
    let path := directory.file (.run manifest.header.generation index)
    calls.runSize path (report.atRun index) = .ok payload.size (report.atRun index) ∧
    calls.runPrefix path payload.size (report.atRun index) = .ok payload (report.atRun (index + 1)) ∧
    MarkedReadCacheFrame seed (report.atRun index) (report.atRun (index + 1)) ∧
    view.descriptors (report.atRun (index + 1)) = (admission.reached.afterDrops chronology.manifestDrops).afterDrops
      (runReadDrops chronology.runs.events (index + 1)) := by
  intro path
  obtain ⟨object, located, contents, file, custody, events⟩ := chronology.runs.runs bytes manifest bound decoded index within payload stored
  have measured : file.metadata.byteSize.toNat = payload.size := (file.observesFile located contents).extent
  obtain ⟨raw⟩ := report.runRead bytes manifest bound decoded index within payload stored
  refine ⟨?_, raw.returns.1, raw.returns.2, ?_⟩
  · have stat := report.runStat bytes manifest bound decoded index within
    change calls.stat path (report.atRun index) = .ok ((reads.reads.stat path).map Prod.fst) (report.atRun index) at stat
    rw [file.stat] at stat
    simp [MarkedTemporaryReadCalls.runSize, stat, file.regular, Except.map, liftExcept,
      show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    exact measured
  · rw [runReadDrops, events, ← DescriptorInventory.afterDrops_append]
    exact (raw.censusAfter custody).1

/-- The actual selected checkpoint and bounded marker reads thread the
opened heap into the WAL scan, with the same cache and held file image.
The continuation still checks and opens the selected WAL files. -/
theorem reachesScan (report : NativeMarkedCheckpointReadHeap seed chronology calls)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat)) :
    let latest := selectedRunCount retry.image.directory.active.manifest
    let runCensus := fun index => (admission.reached.afterDrops chronology.manifestDrops).afterDrops
      (runReadDrops chronology.runs.events index)
    readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
      calls.runSize calls.runPrefix seed.afterPending = .ok checkpoint (report.atRun latest) ∧
    calls.readOptional directory (directory.file .walBoundary) (report.atRun latest) =
      .ok (some chronology.marker.bytes) report.atScan ∧
    (∀ index ≤ latest, view.descriptors (report.atRun index) = runCensus index) ∧
    view.descriptors report.atScan = admission.reached.afterDrops reads.listing.beforeOpen ∧
    MarkedReadCacheFrame seed seed.afterPending report.atScan ∧
    view.cacheAt report.atScan seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
    view.files report.atScan = admission.held ∧
    prepareBoundedMarkedFromReaders directory
      (readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
        calls.runSize calls.runPrefix)
      (calls.readOptional directory) readWal seed.afterPending =
      prepareBoundedMarkedFromReaders directory (pure checkpoint) (fun _ => pure (some chronology.marker.bytes))
        readWal report.atScan := by
  intro latest runCensus
  obtain ⟨manifest, firstFrame, firstCensus⟩ := report.manifest
  have checkpointRead : readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
      calls.runSize calls.runPrefix seed.afterPending = .ok checkpoint (report.atRun latest) := by
    apply readIntegrityCheckpointSized_fromSelectedReads selected _ _ _ _ report.atRun manifest
    · intro bytes file bound decoded index within payload stored
      exact (report.readsRun bound decoded within stored).1
    · intro bytes file bound decoded index within payload stored
      exact (report.readsRun bound decoded within stored).2.1
  have slotsAndCells : ∀ index ≤ latest,
      MarkedReadCacheFrame seed seed.afterPending (report.atRun index) ∧
      view.descriptors (report.atRun index) = runCensus index := by
    intro index
    induction index with
    | zero =>
      intro _
      simp only [runCensus, runReadDrops]
      rw [firstCensus]
      refine ⟨firstFrame, ?_⟩
      generalize admission.reached.afterDrops chronology.manifestDrops = before
      cases before
      simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
    | succ index earlier =>
      intro within
      have visited : index < latest := Nat.lt_of_succ_le within
      obtain ⟨_, _, _, bound, decoded, member, stored⟩ := selected.selectedRun visited
      obtain ⟨_, _, frame, census⟩ := report.readsRun bound decoded member stored
      exact ⟨(earlier (Nat.le_of_lt visited)).1.trans frame, census⟩
  have markerRead := report.markerRead.readsOptional report.markerStat
  change calls.readOptional directory (directory.file .walBoundary) (report.atRun latest) =
    .ok (some chronology.marker.bytes) report.atScan at markerRead
  have scanCensus := (report.markerRead.censusAfter chronology.marker.custody).1
  have frame := (slotsAndCells latest (Nat.le_refl _)).1.trans report.markerRead.returns.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, initialFiles, _, _, _, _, _⟩ := seed.installs
  rw [chronology.beforeListing]
  refine ⟨checkpointRead, markerRead, fun index within => (slotsAndCells index within).2, ?_,
    frame, ?_, frame.files.trans initialFiles, ?_⟩
  · rw [scanCensus]
    simp only [DescriptorInventory.afterDrops_append]
  · simp only [OpenCloseHeapView.cacheAt, frame.directoryCell, frame.activeCell, frame.pendingCell, frame.directoryHandle,
      seed.directoryKept, seed.directorySet, seed.activeKept, seed.activeSet, seed.pendingSet, seed.sameHandle, seed.openedHandle,
      Option.map_some, Option.map_none, List.map_nil, CensusOpenAdmissionReports.cache]
    rfl
  · simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, checkpointRead, markerRead, Pure.pure, EStateM.pure]

/-- The reported retained marker selects this guarded branch of the source
open schedule. The bounded continuation receives the same reached raw heap. -/
theorem reachesMarkedScan (report : NativeMarkedCheckpointReadHeap seed chronology calls)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (flat : optionalMetadataWith (calls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (calls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat))
    (finish : Plan × Reopened × Nat → EStateM IO.Error heap Reopened)
    (bootstrap : EStateM IO.Error heap Reopened) :
    recoverSegmentedWalWith
      (rejectFlatWalWith directory (optionalMetadataWith (calls.stat (directory.file .wal))))
      (optionalMetadataWith (calls.stat (directory.file .walBoundary)))
      (prepareBoundedMarkedFromReaders directory
        (readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
          calls.runSize calls.runPrefix) (calls.readOptional directory) readWal >>= finish) bootstrap seed.afterPending =
      (prepareBoundedMarkedFromReaders directory (pure checkpoint) (fun _ => pure (some chronology.marker.bytes))
        readWal >>= finish) report.atScan := by
  obtain ⟨_, _, _, _, _, _, _, reached⟩ := report.reachesScan selected readWal
  simp [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker, Pure.pure, EStateM.pure]
  rw [reached]
  rfl

end NativeMarkedCheckpointReadHeap

end Alvoki.Storage.DiskSession
