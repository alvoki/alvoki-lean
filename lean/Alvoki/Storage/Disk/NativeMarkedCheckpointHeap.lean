import Alvoki.Storage.Disk.NativeAlignedKeeperCache
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair SyncHandleRouting

structure MarkedTemporaryReadCalls (heap : Type) where
  stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  readChunk : IO.FS.Handle → USize → EStateM IO.Error heap ByteArray
  release : IO.FS.Handle → EStateM IO.Error heap Unit

/-- The returned read drops the unretained handle on either outcome.
The pinned runtime ignores the finalizer status. No handle was acquired
when the open itself fails. -/
def MarkedTemporaryReadCalls.readWith (calls : MarkedTemporaryReadCalls heap) (path : FilePath)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray) : EStateM IO.Error heap ByteArray := fun before =>
  match calls.openRead path before with
  | .error cause reached => .error cause reached
  | .ok file opened =>
    match read file opened with
    | .ok bytes reached => .ok bytes (dataErrorDropState calls.release file reached)
    | .error cause reached => .error cause (dataErrorDropState calls.release file reached)

theorem MarkedTemporaryReadCalls.readWith_error (calls : MarkedTemporaryReadCalls heap)
    (path : FilePath) (read : IO.FS.Handle → EStateM IO.Error heap ByteArray)
    {before opened failed : heap} {file : IO.FS.Handle} {cause : IO.Error}
    (openedRaw : calls.openRead path before = .ok file opened)
    (readRaw : read file opened = .error cause failed) :
    calls.readWith path read before =
      .error cause (dataErrorDropState calls.release file failed) := by
  simp only [readWith, openedRaw, readRaw]

/-- A successful scoped read determines the opened handle, its actual
read heap, and the heap reached after releasing that same handle. -/
theorem MarkedTemporaryReadCalls.readWith_ok (calls : MarkedTemporaryReadCalls heap)
    (path : FilePath) (read : IO.FS.Handle → EStateM IO.Error heap ByteArray)
    {before reached : heap} {bytes : ByteArray}
    (returned : calls.readWith path read before = .ok bytes reached) :
    ∃ file opened readHeap,
      calls.openRead path before = .ok file opened ∧
      read file opened = .ok bytes readHeap ∧
      dataErrorDropState calls.release file readHeap = reached := by
  simp only [readWith] at returned
  cases acquired : calls.openRead path before with
  | error cause heap => simp [acquired] at returned
  | ok file opened =>
    simp only [acquired] at returned
    cases observed : read file opened with
    | error cause failed => simp [observed] at returned
    | ok payload readHeap =>
      simp only [observed, EStateM.Result.ok.injEq] at returned
      obtain ⟨rfl, afterRelease⟩ := returned
      exact ⟨file, opened, readHeap, rfl, observed, afterRelease⟩

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

/-- The manifest and marker return their observed bytes only after a
successful regular-file check and read on the opened description. -/
theorem MarkedTemporaryReadCalls.readOptionalPresent (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) (path : FilePath)
    {before reached : heap} {bytes : ByteArray}
    (returned : calls.readOptional directory path before = .ok (some bytes) reached) :
    ∃ metadata afterStat file opened readHeap,
      calls.stat path before = .ok (.ok metadata) afterStat ∧ metadata.type = .file ∧
      calls.openRead path afterStat = .ok file opened ∧
      (if path == directory.file .walBoundary then
        readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (calls.readChunk file)
          WAL.Boundary.acquisitionLimit ByteArray.empty
      else readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat) opened = .ok bytes readHeap ∧
      dataErrorDropState calls.release file readHeap = reached := by
  simp only [readOptional, readOptionalDatabaseFileWithMetadata, Bind.bind, EStateM.bind] at returned
  cases stat : calls.stat path before with
  | error cause heap => simp [stat] at returned
  | ok observed afterStat =>
    cases observed with
    | error cause =>
      cases cause <;> simp [stat, throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure] at returned
      split at returned <;> simp [EStateM.throw, EStateM.pure] at returned
    | ok metadata =>
      simp only [stat] at returned
      have checked : (metadata.type == .file) = true := by
        cases test : metadata.type == .file
        · simp [test, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
        · rfl
      have regular : metadata.type = .file := by
        cases fileKind : metadata.type with
        | file => rfl
        | dir | symlink | other =>
          rw [fileKind] at checked
          exact False.elim (Bool.noConfusion checked)
      simp only [checked, ↓reduceIte, EStateM.bind, Pure.pure, EStateM.pure] at returned
      obtain ⟨file, opened, readHeap, acquired, read, dropped⟩ :=
        calls.readWith_ok path (calls.readMetadata directory path metadata)
          (show calls.readWith path (calls.readMetadata directory path metadata) afterStat = .ok bytes reached from by
            cases result : calls.readWith path (calls.readMetadata directory path metadata) afterStat with
            | error cause heap => simp [result] at returned
            | ok payload heap => simpa only [result, EStateM.Result.ok.injEq, Option.some.injEq] using returned)
      exact ⟨metadata, afterStat, file, opened, readHeap, rfl, regular, acquired, read, dropped⟩

/-- Project either result of acquisition on the admitted manifest. -/
theorem MarkedTemporaryReadCalls.readOptionalManifest_effects (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) {before : heap} {metadata : IO.FS.Metadata}
    (stat : calls.stat (directory.file .manifest) before = .ok (.ok metadata) before)
    (regular : metadata.type = .file) :
    calls.readOptional directory (directory.file .manifest) before =
      ((calls.readWith (directory.file .manifest) fun file =>
        readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat) >>= fun bytes => pure (some bytes))
        before := by
  have schedule : calls.readMetadata directory (directory.file .manifest) metadata =
      fun file => readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat := by
    funext file
    simp [MarkedTemporaryReadCalls.readMetadata, manifestPath_ne_boundary]
  simp [readOptional, schedule, readOptionalDatabaseFileWithMetadata, stat, regular,
    show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem MarkedTemporaryReadCalls.readOptionalManifest (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) {before after : heap} {metadata : IO.FS.Metadata} {bytes : ByteArray}
    (stat : calls.stat (directory.file .manifest) before = .ok (.ok metadata) before)
    (regular : metadata.type = .file)
    (read : calls.readWith (directory.file .manifest)
      (fun file => readIntegrityManifestPrefixWith (calls.readChunk file) metadata.byteSize.toNat) before = .ok bytes after) :
    calls.readOptional directory (directory.file .manifest) before = .ok (some bytes) after := by
  rw [calls.readOptionalManifest_effects directory stat regular]
  simp only [Bind.bind, EStateM.bind, read, Pure.pure, EStateM.pure]

theorem MarkedTemporaryReadCalls.readOptionalMissing (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) (path : FilePath) {before : heap} {name message : String}
    (stat : calls.stat path before = .ok (.error (.noFileOrDirectory name 2 message)) before) :
    calls.readOptional directory path before = .ok none before := by
  simp [readOptional, readOptionalDatabaseFileWithMetadata, stat, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- Project either result of the bounded read on the admitted marker. -/
theorem MarkedTemporaryReadCalls.readOptionalMarker_effects (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) {before : heap} {metadata : IO.FS.Metadata}
    (stat : calls.stat (directory.file .walBoundary) before = .ok (.ok metadata) before)
    (regular : metadata.type = .file) :
    calls.readOptional directory (directory.file .walBoundary) before =
      ((calls.readWith (directory.file .walBoundary) fun file =>
        readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (calls.readChunk file)
          WAL.Boundary.acquisitionLimit ByteArray.empty) >>= fun bytes => pure (some bytes)) before := by
  have schedule : calls.readMetadata directory (directory.file .walBoundary) metadata =
      fun file => readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (calls.readChunk file)
        WAL.Boundary.acquisitionLimit ByteArray.empty := by
    funext file
    simp [MarkedTemporaryReadCalls.readMetadata]
  simp [readOptional, schedule, readOptionalDatabaseFileWithMetadata, stat, regular,
    show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem MarkedTemporaryReadCalls.readOptionalMarker (calls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) {before after : heap} {metadata : IO.FS.Metadata} {bytes : ByteArray}
    (stat : calls.stat (directory.file .walBoundary) before = .ok (.ok metadata) before)
    (regular : metadata.type = .file)
    (read : calls.readWith (directory.file .walBoundary)
      (fun file => readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (calls.readChunk file)
        WAL.Boundary.acquisitionLimit ByteArray.empty) before = .ok bytes after) :
    calls.readOptional directory (directory.file .walBoundary) before = .ok (some bytes) after := by
  rw [calls.readOptionalMarker_effects directory stat regular]
  simp only [Bind.bind, EStateM.bind, read, Pure.pure, EStateM.pure]

def MarkedTemporaryReadCalls.runSize (calls : MarkedTemporaryReadCalls heap) (path : FilePath) :
    EStateM IO.Error heap Nat := do
  let metadata ← liftExcept (← calls.stat path)
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  pure metadata.byteSize.toNat

theorem MarkedTemporaryReadCalls.measuresRun (calls : MarkedTemporaryReadCalls heap)
    {path : FilePath} {before : heap} {metadata : IO.FS.Metadata} {bytes : ByteArray}
    (stat : calls.stat path before = .ok (.ok metadata) before)
    (regular : metadata.type = .file) (extent : metadata.byteSize.toNat = bytes.size) :
    calls.runSize path before = .ok bytes.size before := by
  simp [runSize, stat, regular, extent, liftExcept, show (IO.FS.FileType.file == .file) = true from rfl,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

private def MarkedTemporaryReadCalls.runRead (calls : MarkedTemporaryReadCalls heap) (count : Nat)
    (file : IO.FS.Handle) : EStateM IO.Error heap ByteArray :=
  readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (calls.readChunk file) count ByteArray.empty

def MarkedTemporaryReadCalls.runPrefix (calls : MarkedTemporaryReadCalls heap) (path : FilePath)
    (count : Nat) : EStateM IO.Error heap ByteArray :=
  calls.readWith path (calls.runRead count)

/-- Local effects at the actual open, bounded read, and scope release.
The same relation can track any filesystem projection left intact by these callbacks. -/
structure MarkedTemporaryReadCalls.ScopeFrames (calls : MarkedTemporaryReadCalls heap)
    (frame : heap → heap → Prop) : Prop where
  openRead : ∀ path entry, frame entry (reachedState (calls.openRead path entry))
  readChunk : ∀ file count entry, frame entry (reachedState (calls.readChunk file count entry))
  release : ∀ file entry, frame entry (dataErrorDropState calls.release file entry)

section ReadScopeFrames

variable {heap : Type} {frame : heap → heap → Prop}

theorem exactReadFrames (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (mismatch : IO.Error) (read : USize → EStateM IO.Error heap ByteArray)
    (keeps : ∀ count entry, frame entry (reachedState (read count entry)))
    (remaining : Nat) (buffer : ByteArray) (entry : heap) :
    frame entry (reachedState (readExactPrefixWith mismatch read remaining buffer entry)) := by
  by_cases empty : remaining = 0
  · rw [readExactPrefixWith]
    simpa only [empty, ↓reduceIte, Pure.pure, EStateM.pure, reachedState] using
      (refl entry)
  · rw [readExactPrefixWith]
    simp only [empty, ↓reduceIte, Bind.bind, EStateM.bind]
    have first := keeps remaining.toUSize entry
    cases issued : read remaining.toUSize entry with
    | error =>
      simpa only [issued, reachedState] using first
    | ok chunk reached =>
      have upToRead : frame entry reached := by
        simpa only [issued, reachedState] using first
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · simp only [valid]
        exact trans upToRead (exactReadFrames refl trans mismatch read keeps (remaining - chunk.size)
          (if buffer.isEmpty then chunk else buffer ++ chunk) reached)
      · simpa only [issued, valid, ↓reduceDIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          reachedState] using upToRead
termination_by remaining
decreasing_by omega

theorem manifestReadFrames (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (read : USize → EStateM IO.Error heap ByteArray)
    (keeps : ∀ count entry, frame entry (reachedState (read count entry)))
    (extent : Nat) (entry : heap) :
    frame entry (reachedState (readIntegrityManifestPrefixWith read extent entry)) := by
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  have first := exactReadFrames refl trans mismatch read keeps (min 48 extent) .empty entry
  unfold readIntegrityManifestPrefixWith
  cases issued : readExactPrefixWith mismatch read (min 48 extent) ByteArray.empty entry with
  | error =>
    simpa only [mismatch, Bind.bind, EStateM.bind, issued, reachedState] using first
  | ok header reached =>
    have upToRead : frame entry reached := by
      simpa only [issued, reachedState] using first
    let rest := min (extent - 48) (Manifest.IntegrityCheckpoint.declaredStampBytes header + 1)
    by_cases short : header.size < 48
    · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, Pure.pure, EStateM.pure, reachedState] using upToRead
    · by_cases fits : 48 + rest < USize.size
      · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, rest, fits, Pure.pure, EStateM.pure] using
          trans upToRead (exactReadFrames refl trans mismatch read keeps rest header reached)
      · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, rest, fits, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw, reachedState] using upToRead

theorem MarkedTemporaryReadCalls.readWithFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (path : FilePath)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray)
    (keeps : ∀ file entry, frame entry (reachedState (read file entry)))
    (entry : heap) :
    frame entry (reachedState (calls.readWith path read entry)) := by
  have opened := laws.openRead path entry
  cases ran : calls.openRead path entry with
  | error =>
    simpa only [MarkedTemporaryReadCalls.readWith, ran, reachedState] using opened
  | ok file openedAt =>
    have same : reachedState (calls.readWith path read entry) =
        dataErrorDropState calls.release file (reachedState (read file openedAt)) := by
      rw [MarkedTemporaryReadCalls.readWith, ran]
      cases returned : read file openedAt <;> simp [returned, reachedState]
    rw [same]
    rw [ran] at opened
    exact trans (trans opened (keeps file openedAt)) (laws.release file _)

private theorem prefixUntilEofFrames (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (mismatch : IO.Error) (read : USize → EStateM IO.Error heap ByteArray)
    (keeps : ∀ count entry, frame entry (reachedState (read count entry)))
    (remaining : Nat) (buffer : ByteArray) (entry : heap) :
    frame entry (reachedState (readPrefixUntilEofWith mismatch read remaining buffer entry)) := by
  by_cases empty : remaining = 0
  · rw [readPrefixUntilEofWith]
    simpa only [empty, ↓reduceIte, Pure.pure, EStateM.pure, reachedState] using (refl entry)
  · rw [readPrefixUntilEofWith]
    simp only [empty, ↓reduceIte, Bind.bind, EStateM.bind]
    have first := keeps remaining.toUSize entry
    cases issued : read remaining.toUSize entry with
    | error =>
      simpa only [issued, reachedState] using first
    | ok chunk reached =>
      have upToRead : frame entry reached := by
        simpa only [issued, reachedState] using first
      by_cases eof : chunk.size = 0
      · simpa only [eof, ↓reduceIte, Pure.pure, EStateM.pure, reachedState] using upToRead
      · by_cases within : chunk.size ≤ remaining
        · simp only [eof, ↓reduceIte, within]
          exact trans upToRead (prefixUntilEofFrames refl trans mismatch read keeps (remaining - chunk.size)
            (if buffer.isEmpty then chunk else buffer ++ chunk) reached)
        · simpa only [eof, ↓reduceIte, within, ↓reduceDIte, throw, throwThe, MonadExceptOf.throw,
            EStateM.throw, reachedState] using upToRead
termination_by remaining
decreasing_by omega

private theorem MarkedTemporaryReadCalls.metadataReadFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (directory : DiskDirectory) (path : FilePath) (metadata : IO.FS.Metadata)
    (file : IO.FS.Handle) (entry : heap) :
    frame entry (reachedState (calls.readMetadata directory path metadata file entry)) := by
  unfold MarkedTemporaryReadCalls.readMetadata
  split
  · exact prefixUntilEofFrames refl trans _ _ (laws.readChunk file) _ _ _
  · exact manifestReadFrames refl trans _ (laws.readChunk file) _ _

theorem MarkedTemporaryReadCalls.runPrefixFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (path : FilePath) (count : Nat) (entry : heap) :
    frame entry (reachedState (calls.runPrefix path count entry)) :=
  calls.readWithFrames laws trans path _
    (fun file => exactReadFrames refl trans _ _ (laws.readChunk file) count ByteArray.empty) entry

end ReadScopeFrames

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
structure RawTemporaryReadReport (observations : CheckpointRunChunkReads)
    (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (calls : MarkedTemporaryReadCalls heap) (path : FilePath) (drops : List LockReferenceDrop)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray) (bytes : ByteArray) (before after : heap) where
  file : IO.FS.Handle
  opened : heap
  finished : heap
  openedRaw : calls.openRead path before = .ok file opened
  sameOpened : observations.openRead path = .ok (view.handle opened file)
  readRaw : read file opened = .ok bytes finished
  sameSlot : (view.handle finished file).2.1 = (view.handle opened file).2.1
  releasedRaw : calls.release file finished = .ok () after
  census : view.descriptors after = (view.handle opened file).1.afterDrops drops
  openFrame : MarkedReadCacheFrame seed before opened
  readFrame : MarkedReadCacheFrame seed opened finished
  releaseFrame : MarkedReadCacheFrame seed finished after

theorem RawTemporaryReadReport.returns {observations : CheckpointRunChunkReads} {calls : MarkedTemporaryReadCalls heap}
    {read : IO.FS.Handle → EStateM IO.Error heap ByteArray}
    (report : RawTemporaryReadReport observations seed calls path drops read bytes before after) :
    calls.readWith path read before = .ok bytes after ∧ MarkedReadCacheFrame seed before after := by
  refine ⟨?_, (report.openFrame.trans report.readFrame).trans report.releaseFrame⟩
  simp only [MarkedTemporaryReadCalls.readWith, report.openedRaw, report.readRaw, dataErrorDropState, report.releasedRaw]

private theorem RawTemporaryReadReport.frames {observations : CheckpointRunChunkReads}
    {calls : MarkedTemporaryReadCalls heap} {read : IO.FS.Handle → EStateM IO.Error heap ByteArray}
    {frame : heap → heap → Prop} (raw : RawTemporaryReadReport observations seed calls path drops read bytes before after)
    (laws : calls.ScopeFrames frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (keeps : ∀ file entry, frame entry (reachedState (read file entry))) : frame before after := by
  simpa only [raw.returns.1, reachedState] using calls.readWithFrames laws trans path read keeps before

theorem RawTemporaryReadReport.censusAfter {observations : CheckpointRunChunkReads} {calls : MarkedTemporaryReadCalls heap}
    {read : IO.FS.Handle → EStateM IO.Error heap ByteArray}
    {name : String} {file : RunChunkPathReport observations path name admission.root admission.view}
    {initial : DescriptorInventory} (custody : TemporaryPrefixCustody file initial drops)
    (raw : RawTemporaryReadReport observations seed calls path drops read bytes before after) :
    view.descriptors after = initial.afterDrops (custody.beforeOpen ++ drops) ∧
    (view.descriptors after).references file.slot.description = [] ∧
    (view.handle raw.finished raw.file).2.1 = file.slot := by
  have same := (Except.ok.inj (raw.sameOpened.symm.trans file.opened))
  have releaseSlot := raw.sameSlot.trans (congrArg (fun handle : CheckpointOpenHandle => handle.2.1) same)
  rw [raw.census, same]
  exact ⟨(custody.closes (released := fun _ => drops)).1,
    (custody.closes (released := fun _ => drops)).2, releaseSlot⟩

abbrev MarkedTemporaryReadReport (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (calls : MarkedTemporaryReadCalls heap) (path : FilePath) (drops : List LockReferenceDrop)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray) (bytes : ByteArray) (before after : heap) :=
  RawTemporaryReadReport reads.reads seed calls path drops read bytes before after

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
    exact calls.measuresRun (by simpa only [Except.map] using stat) file.regular measured
  · rw [runReadDrops, events, ← DescriptorInventory.afterDrops_append]
    exact (raw.censusAfter custody).1

private theorem throughSelectedRuns {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    {invariant : Nat → Prop} (initial : invariant 0)
    (step : ∀ {bytes manifest index payload}, retry.image.directory.active.manifest = some bytes →
      IntegrityCheckpoint.decode bytes = .ok manifest → index < manifest.header.runCount.toNat →
      published.durable manifest.header.generation index = some payload →
      invariant index → invariant (index + 1)) :
    ∀ index ≤ selectedRunCount retry.image.directory.active.manifest, invariant index := by
  intro index
  induction index with
  | zero => exact fun _ => initial
  | succ index earlier =>
    intro within
    have visited := Nat.lt_of_succ_le within
    obtain ⟨_, _, _, bound, decoded, member, stored⟩ := selected.selectedRun visited
    exact step bound decoded member stored (earlier (Nat.le_of_lt visited))

/-- Follow the literal manifest, selected run and bounded marker reads to
the exact scan heap, carrying only the frame proved for each callback. -/
theorem framesScan (report : NativeMarkedCheckpointReadHeap seed chronology calls)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    {frame : heap → heap → Prop} (laws : calls.ScopeFrames frame)
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after) :
    frame seed.afterPending report.atScan := by
  have first : frame seed.afterPending (report.atRun 0) := by
    rcases chronology.manifest.observedFile with ⟨bound, _⟩ | ⟨bytes, file, _, bound, _⟩
    · rw [report.noManifest bound]
      exact refl seed.afterPending
    · obtain ⟨raw⟩ := report.manifestRead bytes bound file
      exact raw.frames laws trans (calls.metadataReadFrames laws refl trans directory _ _)
  have runs := throughSelectedRuns selected (invariant := fun index => frame seed.afterPending (report.atRun index))
    first (fun bound decoded member stored earlier => by
      obtain ⟨raw⟩ := report.runRead _ _ bound decoded _ member _ stored
      exact trans earlier (raw.frames laws trans (fun file =>
        exactReadFrames refl trans _ _ (laws.readChunk file) _ ByteArray.empty)))
  exact trans (runs _ (Nat.le_refl _))
    (report.markerRead.frames laws trans (calls.metadataReadFrames laws refl trans directory _ _))

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
    apply throughSelectedRuns selected (invariant := fun index =>
      MarkedReadCacheFrame seed seed.afterPending (report.atRun index) ∧
        view.descriptors (report.atRun index) = runCensus index)
    · simp only [runCensus, runReadDrops]
      rw [firstCensus]
      refine ⟨firstFrame, ?_⟩
      generalize admission.reached.afterDrops chronology.manifestDrops = before
      cases before
      simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
    · intro _ _ _ _ bound decoded member stored earlier
      obtain ⟨_, _, frame, census⟩ := report.readsRun bound decoded member stored
      exact ⟨earlier.1.trans frame, census⟩
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
