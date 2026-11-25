import Alvoki.Storage.Disk.NativeMarkedTableOpen
import Alvoki.Storage.Disk.NativeRawOpenCacheDisposal

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}

/-- Acquiring an absent checkpoint uses only the no-follow ENOENT. The
bounded marker reader and its release then supply the raw listing entry. -/
structure RawAbsentManifestMarkerPrefix
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  absent : retry.image.directory.active.manifest = none
  missing : ∃ name message, calls.lookup (directory.file .manifest) seed.afterPending =
    .ok (.error (.noFileOrDirectory name 2 message)) seed.afterPending
  selected : ByteArray
  bound : retry.image.directory.active.walBoundary = some selected
  reads : CheckpointRunChunkReads
  marker : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root selected
  stat : calls.lookup (directory.file .walBoundary) seed.afterPending =
    .ok ((reads.stat (directory.file .walBoundary)).map Prod.fst) seed.afterPending
  through : UInt64
  decoded : WAL.Boundary.decode selected = .ok through
  aligned : through.toNat % WAL.frameSize = 0
  file : IO.FS.Handle
  opened : heap
  finished : heap
  atScan : heap
  openedRaw : fileCalls.openRead (directory.file .walBoundary) seed.afterPending = .ok file opened
  sameOpened : reads.openRead (directory.file .walBoundary) = .ok (view.handle opened file)
  readRaw : readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (fileCalls.readChunk file)
    WAL.Boundary.acquisitionLimit ByteArray.empty opened = .ok selected finished
  sameSlot : (view.handle finished file).2.1 = (view.handle opened file).2.1
  releasedRaw : fileCalls.release file finished = .ok () atScan
  drops : List LockReferenceDrop
  custody : TemporaryPrefixCustody marker.calls admission.reached drops
  census : view.descriptors atScan = (view.handle opened file).1.afterDrops drops
  frame : MarkedReadCacheFrame seed seed.afterPending atScan

namespace RawAbsentManifestMarkerPrefix

variable {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

theorem readsSelected (seen : RawAbsentManifestMarkerPrefix (admitted := admitted) seed fileCalls) :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending = .ok none seed.afterPending ∧
    optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
      .ok (some seen.marker.calls.metadata) seed.afterPending ∧
    fileCalls.readOptional directory (directory.file .walBoundary) seed.afterPending = .ok (some seen.selected) seen.atScan ∧
    (view.handle seen.finished seen.file).2.1 = seen.marker.calls.slot ∧
    (view.handle seen.opened seen.file).1.inode (view.handle seen.opened seen.file).2.1.description =
      admission.view.modelObject seen.marker.object ∧
    view.descriptors seen.atScan = admission.reached.afterDrops (seen.custody.beforeOpen ++ seen.drops) ∧
    (view.descriptors seen.atScan).references seen.marker.calls.slot.description = [] := by
  obtain ⟨name, message, missing⟩ := seen.missing
  have stat : calls.lookup (directory.file .walBoundary) seed.afterPending =
      .ok (.ok seen.marker.calls.metadata) seed.afterPending := by
    simp only [seen.stat, seen.marker.calls.stat, Except.map]
  have opened := Except.ok.inj (seen.sameOpened.symm.trans seen.marker.calls.opened)
  have closed := seen.custody.closes (released := fun _ => seen.drops)
  have after : view.descriptors seen.atScan = admission.reached.afterDrops (seen.custody.beforeOpen ++ seen.drops) := by
    rw [seen.census, opened]
    exact closed.1
  refine ⟨fileCalls.readOptionalMissing directory _ (seen.sameLookup.symm ▸ missing), ?_,
    fileCalls.readOptionalMarker directory (seen.sameLookup.symm ▸ stat) seen.marker.calls.regular ?_,
    seen.sameSlot.trans (congrArg (fun handle : CheckpointOpenHandle => handle.2.1) opened), ?_, after,
    ?_⟩
  · simp only [optionalMetadataWith, Bind.bind, EStateM.bind, stat, Pure.pure, EStateM.pure]
  · simp only [MarkedTemporaryReadCalls.readWith, Bind.bind, EStateM.bind, seen.openedRaw, seen.readRaw,
      seen.releasedRaw, Pure.pure, EStateM.pure]
  · rw [opened]
    exact seen.marker.calls.identifiedOpen.symm.trans
      (congrArg admission.view.modelObject (seen.marker.calls.openLookup.child_eq seen.marker.bound))
  · rw [after, ← closed.1]
    exact closed.2

end RawAbsentManifestMarkerPrefix

/-- The native wrapper uses the terminal read error whenever both
callbacks fail. The close error is visible only after successful EOF. -/
inductive MarkedListingDiagnostic : Except IO.Error Unit → Except IO.Error Unit → IO.Error → Prop where
  | readError (cause : IO.Error) (closed : Except IO.Error Unit) : MarkedListingDiagnostic (.error cause) closed cause
  | closeError (cause : IO.Error) : MarkedListingDiagnostic (.ok ()) (.error cause) cause

/-- One checked stream reports both its terminal read and its close on
the same stream. Its effect report says whether the slot was released. -/
structure RawMarkedListingScanFailure
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (slotOf : heap → stream → DescriptorSlot)
    (before : heap) where
  descriptor : stream
  slot : DescriptorSlot
  free : ∀ other ∈ (view.descriptors before).slots, other.address ≠ slot.address
  fresh : (view.descriptors before).references slot.description = []
  rootObject : (view.descriptors before).inode slot.description = admission.view.modelObject admission.root
  opened : heap
  scanned : heap
  reached : heap
  openedRaw : directoryCalls.openDir directory.path before = .ok descriptor opened
  openedSlot : slotOf opened descriptor = slot
  openedCensus : view.descriptors opened = (view.descriptors before).insert slot free
  scan : OpenedDirectoryScan
  readRaw : directoryCalls.readDir descriptor opened = ((scan.names, scan.terminal), scanned)
  scannedSlot : slotOf scanned descriptor = slot
  scannedCensus : view.descriptors scanned = view.descriptors opened
  closedRaw : directoryCalls.closeDir descriptor scanned = match scan.closed with
    | .ok () => .ok () reached
    | .error cause => .error cause reached
  dropped : Bool
  closeDrops : scan.closed = .ok () → dropped = true
  closedCensus : view.descriptors reached = (view.descriptors scanned).afterDrops (if dropped then [slot.closeEvent] else [])
  frame : MarkedReadCacheFrame seed before reached
  cause : IO.Error
  diagnostic : MarkedListingDiagnostic scan.terminal scan.closed cause

namespace RawMarkedListingScanFailure

variable {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot} {before : heap}

theorem stops (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf before) :
    directoryCalls.run directory.path before = .error seen.cause seen.reached := by
  have diagnostic : (CheckedDirectoryReadReport.scanned seen.scan).result directory.path = .error seen.cause := by
    rcases outcome : seen.scan with ⟨names, terminal, closed⟩
    have failure := seen.diagnostic
    rw [outcome] at failure
    cases failure with
    | readError => exact CheckedDirectoryReadReport.scan_readError directory.path rfl
    | closeError => exact CheckedDirectoryReadReport.scan_closeError directory.path rfl rfl
  simp only [MarkedDirectoryReadCalls.run, seen.openedRaw, seen.readRaw, seen.closedRaw]
  cases scan : seen.scan with
  | mk names terminal closed =>
    cases closed with
    | error exception =>
      simp only [scan] at diagnostic ⊢
      rw [diagnostic]
      rfl
    | ok value =>
      cases value
      simp only [scan] at diagnostic ⊢
      rw [diagnostic]
      rfl

theorem sameStream (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf before) :
    slotOf seen.scanned seen.descriptor = slotOf seen.opened seen.descriptor ∧
    (view.descriptors seen.scanned).inode seen.slot.description = admission.view.modelObject admission.root ∧
    view.descriptors seen.reached = ((view.descriptors before).insert seen.slot seen.free).afterDrops
      (if seen.dropped then [seen.slot.closeEvent] else []) := by
  refine ⟨seen.scannedSlot.trans seen.openedSlot.symm, ?_, seen.closedCensus.trans ?_⟩
  · rw [seen.scannedCensus, seen.openedCensus]
    exact seen.rootObject
  · rw [seen.scannedCensus, seen.openedCensus]

end RawMarkedListingScanFailure

variable {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}
  {markerPrefix : RawAbsentManifestMarkerPrefix (admitted := admitted) seed fileCalls}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot}

/-- The absent checkpoint and bounded marker select the checked listing
before any WAL extent, payload, repair or table allocation is reached. -/
theorem RawMarkedListingScanFailure.stopsMarkedWorker
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error seen.cause seen.reached := by
  obtain ⟨manifest, markerRoute, marker, _⟩ := markerPrefix.readsSelected
  have watermark : (PackedTable.empty).committed.toNat = 0 := rfl
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, readIntegrityCheckpointSized,
    readSelectedWithCachedExtents, Bind.bind, EStateM.bind, markerPrefix.flat, markerRoute, Option.isSome_none,
    Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, manifest, marker, Option.getD_none,
    watermark, markerPrefix.decoded, markerPrefix.aligned, Nat.zero_le, true_and, liftExcept, Except.mapError, seen.stops]

/-- At the listing's error, the held scope disposes its synchronization
cache before unlocking the original handle. The file image is retained. -/
theorem RawMarkedListingScanFailure.returnsAbsentManifest {α : Type}
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    let recover := fun resolved lock cache =>
      calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove write rename bootstrap resolved cache >>= install resolved lock cache
    disposal.Returned recover seen.cause ∧
    (view.files disposal.reached).image.directory.active.manifest = none ∧
    (view.files disposal.reached).image.directory.active.walBoundary = some markerPrefix.selected := by
  intro recover
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, files, _⟩ := seed.installs
  have held := (markerPrefix.frame.trans seen.frame).files.trans files
  have returned := disposal.returns recover seen.cause (fun rawCache => by
    simp only [recover, Bind.bind, EStateM.bind, seen.stopsMarkedWorker callbacks remove write rename bootstrap]) held
  refine ⟨returned, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, image, _⟩ := returned
  exact ⟨(congrArg (fun image => image.directory.active.manifest) image).trans markerPrefix.absent,
    (congrArg (fun image => image.directory.active.walBoundary) image).trans markerPrefix.bound⟩

end Alvoki.Storage.DiskSession
