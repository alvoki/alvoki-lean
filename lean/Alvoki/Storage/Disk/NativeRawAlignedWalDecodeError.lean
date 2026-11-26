import Alvoki.Storage.Disk.HeldWalDecodeRejection
import Alvoki.Storage.Disk.NativeRawPresentManifestListing

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL (frameSize)

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {callbacks : AlignedKeeperCacheCallbacks heap}
  {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
  {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}

/-- Observe one checked listing and the selected aligned keeper. Its
physical payload may be malformed. The pending cache keeps its read
handle when the acquisition returns to the decoder. -/
structure RawAlignedWalDecodeRead (marker : RawPresentManifestMarkerPrefix selected)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (slotOf : heap → stream → DescriptorSlot)
    (callbacks : AlignedKeeperCacheCallbacks heap) where
  lifetime : HeldDirectoryReadLifetime (view.descriptors marker.atScan) admission.owner
  sameRoot : lifetime.root = admission.root
  sameNamespace : lifetime.namespaceView = admission.view
  sameDirectory : lifetime.directorySlot = admission.cached
  listing : HeldDirectoryScan lifetime
  streamHandle : stream
  openedStream : heap
  scannedStream : heap
  afterListing : heap
  openDir : directoryCalls.openDir directory.path marker.atScan = .ok streamHandle openedStream
  streamSlot : slotOf openedStream streamHandle = listing.stream
  streamCensus : view.descriptors openedStream = listing.opened
  readDir : directoryCalls.readDir streamHandle openedStream = ((listing.scan.names, listing.scan.terminal), scannedStream)
  sameStream : slotOf scannedStream streamHandle = listing.stream
  scannedCensus : view.descriptors scannedStream = listing.opened.afterDrops listing.duringScan
  closeDir : directoryCalls.closeDir streamHandle scannedStream = .ok () afterListing
  listedCensus : view.descriptors afterListing = (view.descriptors scannedStream).afterDrops [listing.stream.closeEvent]
  listedFrame : MarkedReadCacheFrame seed marker.atScan afterListing
  first : Nat
  bytes : ByteArray
  keeper : HeldWalPayloadFile selected.reads directory admission.view admission.root first bytes
  boundBytes : (view.files entry).image.keeper.active = some bytes
  extent : readWalSegmentExtentsWith directory (MarkedWalExtentReports.inspect fileCalls)
      ((listing.scan.entries directory.path).toList.map (·.fileName)) afterListing =
    .ok [(first, keeper.calls.metadata)] afterListing
  stat : calls.lookup (directory.file (.walSegment first)) afterListing =
    .ok ((selected.reads.stat (directory.file (.walSegment first))).map Prod.fst) afterListing
  selectedFirst : first ≤ (checkpoint.getD (.empty, 0)).1.committed.toNat
  width : bytes.size = (marker.through.toNat / frameSize - first) * frameSize
  fits : bytes.size < USize.size
  handle : IO.FS.Handle
  opened : heap
  read : heap
  remembered : heap
  openedRaw : fileCalls.openRead (directory.file (.walSegment first)) afterListing = .ok handle opened
  openedHandle : view.handle opened handle = (keeper.calls.inventory, keeper.calls.slot, 0)
  openedCensus : view.descriptors opened = keeper.calls.inventory
  slotFree : ∀ prior ∈ (view.descriptors afterListing).slots, prior.address ≠ keeper.calls.slot.address
  inserted : keeper.calls.inventory = (view.descriptors afterListing).insert keeper.calls.slot slotFree
  fresh : (view.descriptors afterListing).references keeper.calls.slot.description = []
  readRaw : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (fileCalls.readChunk handle)
    bytes.size ByteArray.empty opened = .ok bytes read
  readCensus : view.descriptors read = view.descriptors opened
  remember : callbacks.modifyPending seed.pendingRef (pushPending (directory.file (.walSegment first)) handle) read =
    .ok () remembered
  rememberedCensus : view.descriptors remembered = view.descriptors read
  rememberedSlot : (view.handle remembered handle).2.1 = keeper.calls.slot
  pending : view.pending remembered seed.pendingRef = [(directory.file (.walSegment first), handle)]
  directoryCell : view.directory remembered seed.directoryRef = view.directory afterListing seed.directoryRef
  activeCell : view.active remembered seed.activeRef = view.active afterListing seed.activeRef
  directoryHandle : view.handle remembered seed.handle = view.handle afterListing seed.handle
  files : view.files remembered = view.files afterListing

namespace RawAlignedWalDecodeRead

variable {marker : RawPresentManifestMarkerPrefix selected} {slotOf : heap → stream → DescriptorSlot}
variable (seen : RawAlignedWalDecodeRead marker directoryCalls slotOf callbacks)

theorem returnsListing :
    directoryCalls.run directory.path marker.atScan =
      .ok (seen.listing.scan.entries directory.path) seen.afterListing ∧
    view.descriptors seen.afterListing = seen.listing.afterClose := by
  refine ⟨?_, seen.listedCensus.trans ?_⟩
  · simp only [MarkedDirectoryReadCalls.run, seen.openDir, seen.readDir, seen.closeDir]
    have same : (⟨seen.listing.scan.names, seen.listing.scan.terminal, .ok ()⟩ : OpenedDirectoryScan) = seen.listing.scan := by
      rw [seen.listing.closed.symm]
    rw [same, (CheckedDirectoryReadReport.scan_complete directory.path seen.listing.eof seen.listing.closed
      seen.listing.complete).1]
    rfl
  · rw [seen.scannedCensus]
    rfl

/-- The measured and opened keeper identify the same rooted payload.
The open descriptor is still live when its handle is remembered. -/
theorem remembersSelected :
    MarkedWalExtentReports.inspect fileCalls (directory.file (.walSegment seen.first)) seen.afterListing =
      .ok (.ok seen.keeper.calls.metadata) seen.afterListing ∧
    (view.descriptors seen.remembered).inode seen.keeper.calls.slot.description =
      admission.view.modelObject seen.keeper.object ∧
    seen.keeper.calls.slot ∈ (view.descriptors seen.remembered).slots ∧
    view.pending seen.remembered seed.pendingRef = [(directory.file (.walSegment seen.first), seen.handle)] ∧
    view.files seen.remembered = admission.held := by
  have rawStat : fileCalls.stat (directory.file (.walSegment seen.first)) seen.afterListing =
      .ok (.ok seen.keeper.calls.metadata) seen.afterListing := by
    simp only [marker.sameLookup, seen.stat, seen.keeper.calls.stat, Except.map]
  have lookedUp : MarkedWalExtentReports.inspect fileCalls (directory.file (.walSegment seen.first)) seen.afterListing =
      .ok (.ok seen.keeper.calls.metadata) seen.afterListing := by
    simp [MarkedWalExtentReports.inspect, inspectWalSegmentWith, checkPrivateRegularWith, rawStat,
      seen.keeper.calls.regular, seen.keeper.oneLink, show (IO.FS.FileType.file == .file) = true from rfl,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have sameCensus := seen.rememberedCensus.trans (seen.readCensus.trans seen.openedCensus)
  have sameObject := seen.keeper.calls.openLookup.child_eq seen.keeper.bound
  obtain ⟨_, _, files, _⟩ := marker.reachesScan
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, held, _⟩ := seed.installs
  exact ⟨lookedUp, sameCensus.symm ▸ (seen.keeper.calls.identifiedOpen.symm.trans (congrArg _ sameObject)),
    sameCensus.symm ▸ seen.keeper.calls.live, seen.pending, seen.files.trans ((files.trans seen.listedFrame).files.trans held)⟩

theorem readKeeper :
    (callbacks.withFileReads fileCalls).readKeeper seed.pendingRef (directory.file (.walSegment seen.first))
      seen.bytes.size seen.keeper.calls.metadata.byteSize.toNat seen.afterListing = .ok seen.bytes seen.remembered := by
  have measured : seen.keeper.calls.metadata.byteSize.toNat = seen.bytes.size := seen.keeper.observesFile.extent
  rw [measured]
  exact (callbacks.withFileReads fileCalls).readsAligned seen.fits seen.openedRaw seen.readRaw seen.remember

theorem readsSelected :
    readSelectedWithCachedExtents directory (checkpoint.getD (.empty, 0)).1.committed.toNat marker.through
      directoryCalls.run (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal
      ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) marker.atScan =
      .ok (⟨[(seen.first, seen.bytes)], []⟩, seen.keeper.calls.metadata.byteSize.toNat) seen.remembered := by
  let watermark := (checkpoint.getD (.empty, 0)).1.committed.toNat
  let through := marker.through.toNat / frameSize
  have starts : seen.first ≤ through := Nat.le_trans seen.selectedFirst marker.checked.2
  have selectedExtent : selectWalExtentsThrough [(seen.first, seen.keeper.calls.metadata)] watermark through =
      some ([(seen.first, seen.keeper.calls.metadata)], []) := by
    simp [selectWalExtentsThrough, watermark, seen.selectedFirst, starts, Bind.bind, Option.bind]
  have measured : seen.keeper.calls.metadata.byteSize.toNat = seen.bytes.size := seen.keeper.observesFile.extent
  have keeper := readCachedWalPayloads_singletonReturned directory through seen.first fileCalls.seal
    ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) seen.keeper.calls.metadata
    seen.width measured.symm (by simpa only [measured] using seen.readKeeper)
  simp only [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate, marker.checked, true_and, ↓reduceIte,
    Bind.bind, EStateM.bind, seen.returnsListing.1, seen.extent, selectedExtent, keeper, Pure.pure, EStateM.pure, through, watermark]

/-- The source's span guard and retained-byte selector pass. Corruption
is checked by the ordinal decoder on exactly this keeper's bytes. -/
theorem replayError {cause : String} (corrupt : WAL.decodeOrdinalsFrom (seen.first + 1) seen.bytes = .error cause) :
    recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 marker.through [(seen.first, seen.bytes)] = .error cause := by
  let through := marker.through.toNat / frameSize
  have starts : seen.first ≤ through := Nat.le_trans seen.selectedFirst marker.checked.2
  have spans : checkSelectedWalSegmentSpans through [(seen.first, seen.bytes)] = true := by
    have width : (through - seen.first) * frameSize ≤ seen.bytes.size := Nat.le_of_eq seen.width.symm
    have layouts : checkWalSegmentSpans through [(seen.first, seen.bytes)] = true :=
      (checkWalSegmentSpans_iff ..).mpr ⟨⟨_, [], rfl, starts⟩, .active width⟩
    simp [checkSelectedWalSegmentSpans, starts, layouts]
  have throughBytes : through * frameSize = marker.through.toNat := by
    simpa [through, marker.checked.1, Nat.mul_comm] using Nat.mod_add_div marker.through.toNat frameSize
  have retained : seen.first * frameSize ≤ marker.through.toNat := by
    rw [← throughBytes]
    exact Nat.mul_le_mul_right _ starts
  have count : marker.through.toNat - seen.first * frameSize = seen.bytes.size := by
    rw [← throughBytes, ← Nat.sub_mul, seen.width]
  have fits : (marker.through.toNat - seen.first * frameSize).toUInt64.toNat = seen.bytes.size := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le ..) marker.through.toNat_lt_size), count]
  have selectedBytes : WAL.Boundary.selectRetained seen.first marker.through
      ((walSegmentPayloadBytes [(seen.first, seen.bytes)]).extract 0
        (marker.through.toNat - seen.first * frameSize)) = .ok seen.bytes := by
    rw [WAL.Boundary.selectRetained, ite_eq_right (Nat.not_lt.mpr retained), WAL.Boundary.select, fits,
      count, walSegmentPayloadBytes, List.foldr_cons, List.foldr_nil, ByteArray.append_empty, ByteArray.extract_zero_size]
    have aligned : seen.bytes.size % frameSize = 0 := by rw [seen.width, Nat.mul_mod_left]
    simp [aligned]
  exact (markedWalDecodeWork_of_selection _ _ _ _ [] spans selectedBytes).2 cause corrupt

/-- The actual marked worker stops at the populated cache. No repair
sync, rename or table installation is reached after decoder rejection. -/
theorem stopsMarkedWorker {cause : String} (corrupt : WAL.decodeOrdinalsFrom (seen.first + 1) seen.bytes = .error cause)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error (IO.userError cause) seen.remembered := by
  obtain ⟨loaded, rawMarker, _⟩ := marker.reachesScan
  simp [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, marker.flat, marker.route,
    loaded, rawMarker, marker.decoded, seen.readsSelected, seen.replayError corrupt, liftExcept, Except.mapError,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure, EStateM.pure]

end RawAlignedWalDecodeRead

end Alvoki.Storage.DiskSession
