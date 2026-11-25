import Alvoki.Storage.Disk.CachedWalOpenFailure
import Alvoki.Storage.Disk.DirectoryCacheOpenAdmissionError
import Alvoki.Storage.Disk.HeldWalPayloadObservations
import Alvoki.Storage.Disk.WalReplayWork

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL (frameSize)

/-- The native no-follow guard applied to the observed WAL stat result. -/
def probeWalFile (reads : CheckpointRunChunkReads) (path : FilePath) :
    Except IO.Error (Except IO.Error IO.FS.Metadata) :=
  inspectWalSegmentWith path (.ok ((reads.stat path).map Prod.fst))

/-- Read-only reports up to replay, with physical WAL bytes from the acquired
directory. A selected seal's full payload and the keeper's prefix and tail
may contain arbitrary bytes. The span and successful chunk reads constrain
the extents without assuming a valid encoded history. -/
structure HeldWalDecodeReads (directory : DiskDirectory) (before : LockedFileState FileImage) where
  attempt : CachedOpenAttempt directory before
  descriptors : DescriptorInventory
  owner : DescriptorSlot
  acquiredOwner : attempt.descriptor = owner.description
  lifetime : HeldDirectoryReadLifetime descriptors owner
  listing : HeldDirectoryScan lifetime
  reads : CheckpointRunChunkReads
  lstatReader : attempt.lstat = fun path => liftExcept (probeWalFile reads path)
  sealReader : attempt.readSeal = fun path count => liftExcept (reads.readFilePrefix selectedWalSpanError path count)
  keeperReader : attempt.readKeeper = fun path count size => liftExcept (readWalKeeperBytes reads path count size)
  selection : CachedWalOpenSelection directory attempt.readOptional attempt.readRunSize attempt.readRunPrefix
    attempt.list attempt.lstat before.image
  visibleMarker : before.image.directory.active.walBoundary = some selection.marker
  checkpointReadOnly : selection.afterCheckpoint = before.image
  markerReadOnly : selection.afterMarker = selection.afterCheckpoint
  listed : attempt.list directory.path selection.afterMarker =
    (liftExcept ((CheckedDirectoryReadReport.scanned listing.scan).result directory.path) :
      EStateM IO.Error FileImage _) selection.afterMarker
  first : Nat
  bytes : ByteArray
  rest : List (Nat × ByteArray)
  keeper : Nat
  keeperPrefix : ByteArray
  tail : ByteArray
  addresses : selection.required.map Prod.fst = ((first, bytes) :: rest).map Prod.fst
  spans : WalSegmentSpans (selection.length.toNat / frameSize) ((first, bytes) :: rest)
  last : ((first, bytes) :: rest).getLast? = some (keeper, keeperPrefix)
  keeperWidth : keeperPrefix.size = (selection.length.toNat / frameSize - keeper) * frameSize
  sealedFile : ∀ file ∈ (((first, bytes) :: rest).dropLast),
    HeldWalPayloadFile reads directory lifetime.namespaceView lifetime.root file.1 file.2
  sealedHeld : ∀ file present, owner ∈ (sealedFile file present).calls.inventory.slots ∧
    lifetime.directorySlot ∈ (sealedFile file present).calls.inventory.slots
  sealedBytes : ∀ file ∈ (((first, bytes) :: rest).dropLast), before.image.kept file.1 = some file.2
  sealFits : ∀ file ∈ (((first, bytes) :: rest).dropLast), file.2.size < USize.size
  keeperFile : HeldWalPayloadFile reads directory lifetime.namespaceView lifetime.root keeper (keeperPrefix ++ tail)
  keeperHeld : owner ∈ keeperFile.calls.inventory.slots ∧ lifetime.directorySlot ∈ keeperFile.calls.inventory.slots
  keeperBytes : before.image.keeper.active = some (keeperPrefix ++ tail)
  keeperFits : keeperPrefix.size < USize.size

namespace HeldWalDecodeReads

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def files (report : HeldWalDecodeReads directory before) : List (Nat × ByteArray) :=
  (report.first, report.bytes) :: report.rest

def payload (report : HeldWalDecodeReads directory before) : ByteArray :=
  walSegmentPayloadBytes report.files

def frameAt (report : HeldWalDecodeReads directory before) (index : Nat) : Except String WAL.Write :=
  WAL.decodeFrame (report.payload.extract (index * frameSize) (index * frameSize + frameSize))

/-- The first malformed or wrongly numbered frame in the selected physical
bytes. A malformed frame includes a checksum mismatch from the frame decoder. -/
structure FailureAt (report : HeldWalDecodeReads directory before) (index : Nat) (cause : String) : Prop where
  within : index < report.payload.size / frameSize
  earlier : ∀ position, position < index → ∃ event, report.frameAt position = .ok event ∧
    event.sequence.toNat = report.first + 1 + position
  defect : report.frameAt index = .error cause ∨ ∃ event, report.frameAt index = .ok event ∧
    event.sequence.toNat ≠ report.first + 1 + index ∧ cause = "WAL frame sequence does not match its ordinal"

theorem FailureAt.decoderError {report : HeldWalDecodeReads directory before} {index : Nat} {cause : String}
    (bad : report.FailureAt index cause) : WAL.decodeOrdinalsFrom (report.first + 1) report.payload = .error cause :=
  WAL.decodeOrdinalsFrom_error_at _ _ index bad.within bad.earlier bad.defect

private theorem listed_eq (report : HeldWalDecodeReads directory before) :
    report.selection.entries = report.listing.scan.entries directory.path ∧
      report.selection.afterList = report.selection.afterMarker := by
  have accepted := (CheckedDirectoryReadReport.scan_complete directory.path report.listing.eof report.listing.closed
    report.listing.complete).1
  have listed := report.selection.listed
  rw [report.listed, accepted] at listed
  exact (EStateM.Result.ok.inj listed).imp Eq.symm Eq.symm

private theorem scanned (report : HeldWalDecodeReads directory before) :
    readWalSegmentExtentsWith (m := Except IO.Error) directory (probeWalFile report.reads)
      (report.selection.entries.toList.map (·.fileName)) = .ok report.selection.extents ∧
      report.selection.afterScan = report.selection.afterList := by
  have actual := report.selection.scanned
  simp only [report.lstatReader] at actual
  change readWalSegmentExtentsWith (m := EStateM IO.Error FileImage) directory
    (fun path => liftExcept (probeWalFile report.reads path)) _ _ = _ at actual
  rw [readWalSegmentExtentsWith_liftReports] at actual
  cases scan : readWalSegmentExtentsWith (m := Except IO.Error) directory
      (probeWalFile report.reads) (report.selection.entries.toList.map (·.fileName)) with
  | error cause => rw [scan] at actual; contradiction
  | ok extents =>
    rw [scan] at actual
    obtain ⟨rfl, same⟩ := EStateM.Result.ok.inj actual
    exact ⟨rfl, same.symm⟩

/-- The actual cached listing read the acquired directory and closed its
own stream with the lock and cached directory slots still present. -/
theorem listingCustody (report : HeldWalDecodeReads directory before) :
    report.selection.entries = report.listing.scan.entries directory.path ∧ report.listing.Custody :=
  ⟨report.listed_eq.1, report.listing.custody⟩

private theorem requiredMetadata (report : HeldWalDecodeReads directory before) {entry : Nat × IO.FS.Metadata}
    (present : entry ∈ report.selection.required) :
    probeWalFile report.reads (directory.file (.walSegment entry.1)) = .ok (.ok entry.2) :=
  readWalSegmentExtentsWith_metadata report.scanned.1
    (selectWalExtentsThrough_required_subset report.selection.selected present)

private theorem payloadReports (report : HeldWalDecodeReads directory before) :
    CachedWalPayloadReports directory (report.selection.length.toNat / frameSize)
      (report.reads.readFilePrefix selectedWalSpanError) (readWalKeeperBytes report.reads)
      report.selection.required report.files (report.keeperPrefix ++ report.tail).size := by
  apply CachedWalPayloadReports.of_spans report.spans report.addresses report.last report.keeperWidth
  · intro entry selected file member same
    let sealed := report.sealedFile file member
    let observed := sealed.observesFile
    have stat := report.requiredMetadata selected
    rw [same, probeWalFile, sealed.inspected] at stat
    have metadata : entry.2 = observed.metadata := (Except.ok.inj (Except.ok.inj stat)).symm
    refine ⟨metadata ▸ observed.extent, report.sealFits file member, ?_⟩
    simp [CheckpointRunChunkReads.readFilePrefix, Bind.bind, Except.bind, observed.opened,
      observed.readOpenedExactPrefix _ _ (report.sealFits file member) (Nat.le_refl _)]
  · intro entry selected same
    let observed := report.keeperFile.observesFile
    have stat := report.requiredMetadata selected
    rw [same, probeWalFile, report.keeperFile.inspected] at stat
    have metadata : entry.2 = observed.metadata := (Except.ok.inj (Except.ok.inj stat)).symm
    rw [metadata]
    exact ⟨observed.extent, observed.extent ▸ (by simp),
      by simp [readWalKeeperBytes, readWalKeeperWithChunks_exact observed report.keeperFits]⟩

/-- Exact physical chunks reach the bounded reader, excluding the keeper's
tail. Every read to this point preserves the file image. -/
theorem readSelected (report : HeldWalDecodeReads directory before) :
    readSelectedWithCachedExtents directory (report.selection.checkpoint.getD (.empty, 0)).1.committed.toNat
      report.selection.length report.attempt.list report.attempt.lstat report.attempt.readSeal
      report.attempt.readKeeper report.selection.afterMarker =
      .ok (⟨report.files, report.selection.newer⟩, (report.keeperPrefix ++ report.tail).size) before.image := by
  have scanUnchanged := report.selection.afterScan_eq_of_readonly report.checkpointReadOnly
    report.markerReadOnly report.listed_eq.2 report.scanned.2
  have calls := congrFun (readCachedWalPayloads_reportedEffects (state := FileImage) report.payloadReports)
    report.selection.afterScan
  rw [← report.sealReader, ← report.keeperReader] at calls
  simp [readSelectedWithCachedExtents, report.selection.checked, Bind.bind, EStateM.bind, report.selection.listed,
    report.selection.scanned, report.selection.selected, calls, Pure.pure, EStateM.pure]
  rw [scanUnchanged]

private theorem startsWithin (report : HeldWalDecodeReads directory before) :
    ∀ entry ∈ report.selection.required, entry.1 ≤ report.selection.length.toNat / frameSize := by
  let watermark := (report.selection.checkpoint.getD (.empty, 0)).1.committed.toNat
  have selected := report.selection.selected
  change selectWalExtentsThrough report.selection.extents watermark _ = _ at selected
  unfold selectWalExtentsThrough at selected
  cases start : ((report.selection.extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max? with
  | none => simp [start, Bind.bind, Option.bind] at selected
  | some first =>
    simp only [start, Bind.bind, Option.bind, Pure.pure, Option.some.injEq, Prod.mk.injEq] at selected
    intro entry present
    rw [← selected.1] at present
    have bounded := List.all_eq_true.mp (List.all_takeWhile
      (p := fun extent => decide (extent.1 ≤ report.selection.length.toNat / frameSize))) entry present
    exact of_decide_eq_true bounded

private theorem filesWithin (report : HeldWalDecodeReads directory before) :
    ∀ file ∈ report.files, file.1 ≤ report.selection.length.toNat / frameSize := by
  intro file member
  have address : file.1 ∈ report.selection.required.map Prod.fst :=
    report.addresses ▸ List.mem_map_of_mem member
  obtain ⟨entry, present, same⟩ := List.mem_map.mp address
  exact same ▸ report.startsWithin entry present

private theorem spanCheck (report : HeldWalDecodeReads directory before) :
    checkSelectedWalSegmentSpans (report.selection.length.toNat / frameSize) report.files = true := by
  rw [checkSelectedWalSegmentSpans, Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr fun file member => decide_eq_true (report.filesWithin file member),
    (checkWalSegmentSpans_iff ..).mpr
      ⟨⟨(report.first, report.bytes), report.rest, rfl, report.filesWithin _ List.mem_cons_self⟩, report.spans⟩⟩

private theorem payloadSize (report : HeldWalDecodeReads directory before) :
    report.payload.size = (report.selection.length.toNat / frameSize - report.first) * frameSize := by
  have size (files : List (Nat × ByteArray)) :
      (walSegmentPayloadBytes files).size = (files.map (fun item => item.2.size)).sum := by
    induction files with
    | nil => rfl
    | cons file rest ih =>
      simp [walSegmentPayloadBytes, ByteArray.size_append, ← ih]
  have count := report.payloadReports.byteCount report.startsWithin
  rw [← size] at count
  have first := congrArg List.head? report.addresses
  rw [List.head?_map] at first
  change (report.selection.required.head?.map Prod.fst) = some report.first at first
  simpa [payload, first] using count

private theorem markerSelects (report : HeldWalDecodeReads directory before) :
    WAL.Boundary.selectRetained report.first report.selection.length
      (report.payload.extract 0 (report.selection.length.toNat - report.first * frameSize)) = .ok report.payload := by
  let length := report.selection.length
  let through := length.toNat / frameSize
  have width : through * frameSize = length.toNat := by
    simpa [through, length, report.selection.checked.1, Nat.mul_comm] using Nat.mod_add_div length.toNat frameSize
  have retained : report.first * frameSize ≤ length.toNat := by
    rw [← width]
    exact Nat.mul_le_mul_right _ (report.filesWithin _ List.mem_cons_self)
  have count : length.toNat - report.first * frameSize = report.payload.size := by
    rw [report.payloadSize]
    change length.toNat - report.first * frameSize = (through - report.first) * frameSize
    exact (congrArg (· - report.first * frameSize) width).symm.trans (Nat.sub_mul ..).symm
  have fits : (length.toNat - report.first * frameSize).toUInt64.toNat = report.payload.size := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le ..) length.toNat_lt_size), count]
  change WAL.Boundary.selectRetained report.first length
    (report.payload.extract 0 (length.toNat - report.first * frameSize)) = _
  rw [WAL.Boundary.selectRetained, ite_eq_right (Nat.not_lt.mpr retained), WAL.Boundary.select]
  rw [fits, count, ByteArray.extract_zero_size]
  have aligned : report.payload.size % frameSize = 0 := by rw [report.payloadSize, Nat.mul_mod_left]
  simp [aligned]

/-- The rejected preparation reaches the ordinal decoder on the exact
selected bytes. Its cause is the decoder's own diagnostic. -/
def certified (report : HeldWalDecodeReads directory before) {cause : String}
    (failed : WAL.decodeOrdinalsFrom (report.first + 1) report.payload = .error cause) :
    CachedOpenRejection directory before where
  attempt := report.attempt
  cause := IO.userError cause
  rejected := by
    let base := (report.selection.checkpoint.getD (.empty, 0)).1
    have recovered := (markedWalDecodeWork_of_selection base report.selection.length report.first report.bytes
      report.rest report.spanCheck report.markerSelects).2 cause failed
    change recoverMarkedWalSegments base report.selection.length report.files = .error cause at recovered
    simp [CachedOpenAttempt.prepare, prepareBoundedMarkedFromReaders, report.selection.checkpointRead,
      report.selection.markerRead, report.selection.decoded, report.readSelected, recovered, base,
      Bind.bind, EStateM.bind, liftExcept, Except.mapError, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Identify the first failed frame in the exact selected file bytes and
account for format, checksum and ordinal checks actually reached. -/
theorem firstFailure (report : HeldWalDecodeReads directory before) {cause : String}
    (failed : WAL.decodeOrdinalsFrom (report.first + 1) report.payload = .error cause) :
    let work := markedWalDecodeWork report.selection.length report.files
    ∃ index, index < report.payload.size / frameSize ∧ work.frames = index + 1 ∧
      (∀ earlier, earlier < index → ∃ event, report.frameAt earlier = .ok event ∧
        event.sequence.toNat = report.first + 1 + earlier) ∧
      ((report.frameAt index = .error cause ∧ work.ordinals = index) ∨
        (∃ event, report.frameAt index = .ok event ∧ event.sequence.toNat ≠ report.first + 1 + index ∧
          cause = "WAL frame sequence does not match its ordinal" ∧ work.ordinals = index + 1)) := by
  let base := (report.selection.checkpoint.getD (.empty, 0)).1
  have work := (markedWalDecodeWork_of_selection base report.selection.length report.first report.bytes
    report.rest report.spanCheck report.markerSelects).1
  dsimp only
  rw [show report.files = (report.first, report.bytes) :: report.rest from rfl, work]
  exact WAL.decodeOrdinalsFromWithWork_firstFailure _ _ failed

/-- The held listing is reached in the native-shaped admitted open after
directory cache capture and the locked metadata checks. -/
def runWithAdmission (report : HeldWalDecodeReads directory before) {input : FilePath}
    (admission : OpenAdmissionReports input directory report.owner)
    (flock : DescriptorSlot → Except IO.Error Bool)
    (openFiles : DiskDirectory → DescriptorSlot → EStateM IO.Error FileImage
      (Cache (DescriptorInventory × DescriptorSlot × Nat)))
    (lookup : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (bootstrap : DiskDirectory → Cache (DescriptorInventory × DescriptorSlot × Nat) →
      EStateM IO.Error FileImage Reopened) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runAdmittedCachedOpen admission before flock report.attempt.nextRef report.attempt.unlock
    openFiles lookup (fun _ _ => report.attempt.recover) bootstrap

/-- Cache capture and locked metadata admission select the marked branch.
Its exact byte decoder rejects before any repair action or writer
installation. File image and lock outcomes extend the same bounded retry. -/
theorem runWithAdmission_error (report : HeldWalDecodeReads directory before) {input : FilePath}
    (admission : OpenAdmissionReports input directory report.owner)
    (flock : DescriptorSlot → Except IO.Error Bool) (acquired : flock report.owner = .ok true)
    (openFiles : DiskDirectory → DescriptorSlot → EStateM IO.Error FileImage
      (Cache (DescriptorInventory × DescriptorSlot × Nat)))
    (captured : openFiles directory report.owner before.image =
      .ok ⟨some (report.descriptors, report.lifetime.directorySlot, 0), none, []⟩ before.image)
    (lookup : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (flatName flatMessage : String)
    (flatAbsent : lookup (directory.file .wal) before.image =
      .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) before.image)
    {marker : IO.FS.Metadata}
    (present : lookup (directory.file .walBoundary) before.image = .ok (.ok marker) before.image)
    (bootstrap : DiskDirectory → Cache (DescriptorInventory × DescriptorSlot × Nat) →
      EStateM IO.Error FileImage Reopened)
    {index : Nat} {cause : String} (bad : report.FailureAt index cause)
    {initial : LockedFileState FileImage} {admits : Target → Prop}
    (prior : BoundedReopenTrace directory admits initial before) :
    let rejection := report.certified bad.decoderError
    report.runWithAdmission admission flock openFiles lookup bootstrap = .error rejection.error rejection.after ∧
      BoundedReopenTrace directory admits initial rejection.after ∧
      rejection.after.image = before.image ∧
      (match report.attempt.unlock with
      | .success => rejection.error = IO.userError cause ∧ rejection.after.owners (directory.file .lock) = none
      | .failure cleanup _ =>
        rejection.error = cleanup ∧ rejection.after.owners (directory.file .lock) = some report.owner.description) ∧
      (TryLockObserves rejection.after.owners directory (.ok true) ↔ report.attempt.unlock = .success) := by
  intro rejection
  refine ⟨?_, .cachedRejected prior rejection,
    report.attempt.cleanupError_keepsFiles _ _, ?_, rejection.immediateReacquire⟩
  · have checked : optionalMetadataWith (lookup (directory.file .walBoundary)) before.image =
        .ok (some marker) before.image := by
      simp [optionalMetadataWith, Bind.bind, EStateM.bind, present, Pure.pure, EStateM.pure]
    have branch := runOpenWithInstallation_recoveryBranch directory report.owner.description report.attempt.nextRef
      before report.attempt.unlock (openFiles directory report.owner) lookup (fun _ => report.attempt.recover)
      (bootstrap directory) _ captured flatName flatMessage flatAbsent (some marker) checked
    unfold runWithAdmission runAdmittedCachedOpen
    rw [admission.admits]
    unfold runAdmittedCachedOpenAt
    rw [acquired, branch, ← report.acquiredOwner]
    exact rejection.run_error
  · cases cleanup : report.attempt.unlock <;>
      simp [rejection, CachedOpenRejection.error, CachedOpenRejection.after, CachedOpenAttempt.cleanupError,
        certified, cleanup, LockOwners.set, report.acquiredOwner]

/-- After failed cleanup, retry becomes available on the last observed drop
of the acquired lock's references. The failed open retains the same files. -/
theorem afterLastDrop (report : HeldWalDecodeReads directory before)
    {index : Nat} {cause : String} (bad : report.FailureAt index cause)
    {initial : LockedFileState FileImage} {admits : Target → Prop}
    (prior : BoundedReopenTrace directory admits initial before)
    {cleanup : IO.Error} (retained : report.attempt.unlock = .failure cleanup false)
    (references : HeldLockReferences report.attempt.descriptor) (drops : List LockReferenceDrop)
    (last : references.remaining drops = []) :
    let released := references.afterFileDrops drops directory (report.certified bad.decoderError).after
    BoundedReopenTrace directory admits initial released ∧ TryLockObserves released.owners directory (.ok true) ∧
      released.image = before.image := by
  obtain ⟨retry, acquired⟩ := prior.afterCachedLastDrop (report.certified bad.decoderError) retained references drops last
  exact ⟨retry, acquired, report.attempt.cleanupError_keepsFiles (IO.userError cause) before.image⟩

end HeldWalDecodeReads

end Alvoki.Storage.DiskSession
