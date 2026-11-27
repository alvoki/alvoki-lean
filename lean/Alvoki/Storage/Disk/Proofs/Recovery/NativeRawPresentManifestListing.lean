import Alvoki.Storage.Disk.Proofs.Recovery.FailedCheckpointDigestCensus
import Alvoki.Storage.Disk.Proofs.Recovery.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawAbsentManifestListing

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- The raw selected checkpoint reads need only the bounded manifest
and its ordered run opens. Their evidence ends before the marker read. -/
structure RawPresentManifestCheckpointPrefix
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) (durable : CheckpointPublication.RunFiles)
    (checkpoint : Option (PackedTable × UInt64)) where
  reads : CheckpointRunChunkReads
  bytes : ByteArray
  manifest : IntegrityCheckpoint
  bound : retry.image.directory.active.manifest = some bytes
  decoded : IntegrityCheckpoint.decode bytes = .ok manifest
  selected : SelectedIntegrityCheckpoint durable retry.image.directory.active.manifest checkpoint
  manifestFile : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes
  atRun : Nat → heap
  manifestDrops : List LockReferenceDrop
  manifestStat : fileCalls.stat (directory.file .manifest) seed.afterPending =
    .ok ((reads.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
  manifestCustody : TemporaryPrefixCustody manifestFile.calls admission.reached manifestDrops
  manifestRead : RawTemporaryReadReport reads seed fileCalls (directory.file .manifest) manifestDrops
    (fun file => readIntegrityManifestPrefixWith (fileCalls.readChunk file) manifestFile.calls.metadata.byteSize.toNat)
    bytes seed.afterPending (atRun 0)
  runDrops : Nat → List LockReferenceDrop
  runStat : ∀ index < manifest.header.runCount.toNat,
    let path := directory.file (.run manifest.header.generation index)
    fileCalls.stat path (atRun index) = .ok ((reads.stat path).map Prod.fst) (atRun index)
  runRead : ∀ index < manifest.header.runCount.toNat, ∀ payload,
    durable manifest.header.generation index = some payload →
      Nonempty (ReachedDigestRun reads directory admission.view admission.root manifest index payload
          (view.descriptors (atRun index)) (runDrops index) ×
        RawTemporaryReadReport reads seed fileCalls
          (directory.file (.run manifest.header.generation index)) (runDrops index)
          (fun handle => readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (fileCalls.readChunk handle)
            payload.size ByteArray.empty) payload (atRun index) (atRun (index + 1)))

namespace RawPresentManifestCheckpointPrefix

variable {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}

def beforeMarker (seen : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint) : heap :=
  seen.atRun (selectedRunCount retry.image.directory.active.manifest)

private theorem readsRun (seen : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint)
    {bytes : ByteArray} {manifest : IntegrityCheckpoint} (bound : retry.image.directory.active.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) {index : Nat} (within : index < manifest.header.runCount.toNat)
    {payload : ByteArray} (stored : durable manifest.header.generation index = some payload) :
    let path := directory.file (.run manifest.header.generation index)
    fileCalls.runSize path (seen.atRun index) = .ok payload.size (seen.atRun index) ∧
    fileCalls.runPrefix path payload.size (seen.atRun index) = .ok payload (seen.atRun (index + 1)) ∧
    MarkedReadCacheFrame seed (seen.atRun index) (seen.atRun (index + 1)) ∧
    (view.descriptors (seen.atRun (index + 1))).inode = (view.descriptors (seen.atRun index)).inode := by
  obtain rfl : bytes = seen.bytes := Option.some.inj (bound.symm.trans seen.bound)
  obtain rfl : manifest = seen.manifest := Except.ok.inj (decoded.symm.trans seen.decoded)
  intro path
  obtain ⟨⟨file, raw⟩⟩ := seen.runRead index within payload stored
  have stat := seen.runStat index within
  change fileCalls.stat path (seen.atRun index) = .ok ((seen.reads.stat path).map Prod.fst) (seen.atRun index) at stat
  rw [file.file.stat] at stat
  refine ⟨fileCalls.measuresRun (by simpa only [Except.map] using stat) file.file.regular
      (file.file.observesFile file.bound file.contents).extent,
    raw.returns.1, raw.returns.2, ?_⟩
  rw [(raw.censusAfter file.custody).1]
  rfl

/-- The sized checkpoint reader validates the real selected generation
and runs, holding the original cache until the marker reader starts. -/
theorem reachesMarker (seen : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .ok checkpoint seen.beforeMarker ∧
    MarkedReadCacheFrame seed seed.afterPending seen.beforeMarker ∧
    (view.descriptors seen.beforeMarker).inode = admission.reached.inode := by
  have stat := seen.manifestStat
  rw [seen.manifestFile.calls.stat] at stat
  have optional := fileCalls.readOptionalManifest directory (by simpa only [Except.map] using stat)
    seen.manifestFile.calls.regular seen.manifestRead.returns.1
  have scanned := (seen.manifestRead.censusAfter seen.manifestCustody).1
  have advanced : ∀ index ≤ selectedRunCount retry.image.directory.active.manifest,
      MarkedReadCacheFrame seed seed.afterPending (seen.atRun index) ∧
      (view.descriptors (seen.atRun index)).inode = admission.reached.inode := by
    intro index
    induction index with
    | zero =>
      intro _
      refine ⟨seen.manifestRead.returns.2, ?_⟩
      rw [scanned]
      rfl
    | succ index prior =>
      intro within
      obtain ⟨_, _, _, bound, decoded, member, stored⟩ := seen.selected.selectedRun (Nat.lt_of_succ_le within)
      obtain ⟨_, _, frame, c⟩ := seen.readsRun bound decoded member stored
      obtain ⟨initial, inode⟩ := prior (Nat.le_of_lt (Nat.lt_of_succ_le within))
      exact ⟨initial.trans frame, c.trans inode⟩
  obtain ⟨frame, inode⟩ := advanced _ (Nat.le_refl _)
  refine ⟨?_, frame, inode⟩
  apply readIntegrityCheckpointSized_fromSelectedReads seen.selected _ _ _ _ seen.atRun
  · rw [seen.bound]
    exact optional
  · intro _ _ bound decoded _ within _ stored
    exact (seen.readsRun bound decoded within stored).1
  · intro _ _ bound decoded _ within _ stored
    exact (seen.readsRun bound decoded within stored).2.1

end RawPresentManifestCheckpointPrefix

variable {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
  {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot}

/-- Read the selected marker from the heap reached by the accepted
checkpoint. The reported effects end at the marker decoder's entry. -/
structure RawPresentManifestMarkerRead
    (selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  routeMetadata : IO.FS.Metadata
  route : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
    .ok (some routeMetadata) seed.afterPending
  bytes : ByteArray
  bound : retry.image.directory.active.walBoundary = some bytes
  marker : HeldMetadataFile selected.reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root bytes
  stat : calls.lookup (directory.file .walBoundary) selected.beforeMarker =
    .ok ((selected.reads.stat (directory.file .walBoundary)).map Prod.fst) selected.beforeMarker
  afterMarker : heap
  drops : List LockReferenceDrop
  custody : TemporaryPrefixCustody marker.calls (view.descriptors selected.beforeMarker) drops
  read : RawTemporaryReadReport selected.reads seed fileCalls (directory.file .walBoundary) drops
    (fun file => readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (fileCalls.readChunk file)
      WAL.Boundary.acquisitionLimit ByteArray.empty)
    (bytes.extract 0 (min WAL.Boundary.acquisitionLimit bytes.size)) selected.beforeMarker afterMarker

abbrev RawPresentManifestMarkerRead.acquired (seen : RawPresentManifestMarkerRead selected) : ByteArray :=
  seen.bytes.extract 0 (min WAL.Boundary.acquisitionLimit seen.bytes.size)

theorem RawPresentManifestMarkerRead.reachesDecoder (seen : RawPresentManifestMarkerRead selected) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .ok checkpoint selected.beforeMarker ∧
    fileCalls.readOptional directory (directory.file .walBoundary) selected.beforeMarker = .ok (some seen.acquired) seen.afterMarker ∧
    MarkedReadCacheFrame seed seed.afterPending seen.afterMarker ∧
    (view.descriptors seen.afterMarker).inode = admission.reached.inode := by
  obtain ⟨loaded, frame, inode⟩ := selected.reachesMarker
  have stat := seen.stat
  rw [seen.marker.calls.stat] at stat
  exact ⟨loaded, fileCalls.readOptionalMarker directory (by simpa only [seen.sameLookup, Except.map] using stat) seen.marker.calls.regular
      seen.read.returns.1, frame.trans seen.read.returns.2,
    (congrArg DescriptorInventory.inode (seen.read.censusAfter seen.custody).1).trans inode⟩

/-- The checked directory listing is reached after the acquired marker
passes decoding and its extent checks against the accepted checkpoint. -/
structure RawPresentManifestMarkerPrefix
    (selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint)
    extends RawPresentManifestMarkerRead selected where
  through : UInt64
  decoded : WAL.Boundary.decode bytes = .ok through
  checked : through.toNat % WAL.frameSize = 0 ∧ (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ through.toNat / WAL.frameSize

abbrev RawPresentManifestMarkerPrefix.atScan (seen : RawPresentManifestMarkerPrefix selected) : heap :=
  seen.afterMarker

theorem RawPresentManifestMarkerPrefix.reachesScan (seen : RawPresentManifestMarkerPrefix selected) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .ok checkpoint selected.beforeMarker ∧
    fileCalls.readOptional directory (directory.file .walBoundary) selected.beforeMarker = .ok (some seen.bytes) seen.atScan ∧
    MarkedReadCacheFrame seed seed.afterPending seen.atScan ∧
    (view.descriptors seen.atScan).inode = admission.reached.inode := by
  have size : seen.bytes.size = 24 := by
    by_cases complete : seen.bytes.size = 24
    · exact complete
    · have accepted := seen.decoded
      simp [WAL.Boundary.decode, complete] at accepted
  have covered : seen.bytes.size ≤ WAL.Boundary.acquisitionLimit := by rw [size]; decide
  simpa only [RawPresentManifestMarkerRead.acquired, Nat.min_eq_right covered, ByteArray.extract_zero_size] using
    seen.toRawPresentManifestMarkerRead.reachesDecoder

variable {markerPrefix : RawPresentManifestMarkerPrefix selected}

/-- The checked stream is reached after validating the selected
checkpoint and marker. Either reported listing error bypasses WAL work. -/
theorem RawMarkedListingScanFailure.stopsAfterPresentManifest
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error seen.cause seen.reached := by
  obtain ⟨loaded, marker, _⟩ := markerPrefix.reachesScan
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, readSelectedWithCachedExtents,
    withAbsoluteWalCutoff_estate, Bind.bind, EStateM.bind, markerPrefix.flat, markerPrefix.route, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, loaded, marker, markerPrefix.decoded,
    markerPrefix.checked, true_and, liftExcept, Except.mapError, seen.stops]

theorem RawMarkedListingScanFailure.returnsAfterPresentManifest {α : Type}
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    let recover := fun resolved lock cache =>
      calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove write rename bootstrap resolved cache >>= install resolved lock cache
    disposal.Returned recover seen.cause := by
  intro recover
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, files, _⟩ := seed.installs
  have held := (markerPrefix.reachesScan.2.2.1.trans seen.frame).files.trans files
  apply disposal.returns recover seen.cause _ held
  intro cache
  simp only [recover, Bind.bind, EStateM.bind, seen.stopsAfterPresentManifest callbacks remove write rename bootstrap]

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}
  {markerPrefix : RawPresentManifestMarkerPrefix selected} {release : IO.FS.Handle → heap → heap}

/-- The exact failed listing can enter the retry sequence after the
reported cache drop, unlock and close of the original lock slot. -/
noncomputable def RawMarkedListingScanFailure.finalizedPresentAttempt
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry where
  admission := admission
  admitted := admitted
  seed := seed
  beforeCleanup := seen.reached
  disposed := disposal
  recover := fun resolved lock cache =>
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap resolved cache >>= install resolved lock cache
  cause := seen.cause
  rejected := seen.returnsAfterPresentManifest disposal callbacks remove write rename bootstrap install
  workerInodes := (congrArg DescriptorInventory.inode seen.sameStream.2.2).trans markerPrefix.reachesScan.2.2.2
  finalized := finalized

end

end Alvoki.Storage.DiskSession
