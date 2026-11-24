import Alvoki.Storage.Disk.WalSegmentCachedExtentInstall
import Alvoki.Storage.Disk.WalSegmentCachedExtentOpenEffects
import Alvoki.Storage.Disk.WalSegmentCollectionMetadata
import Alvoki.Storage.Disk.WalSegmentSizedCheckpointReports
import Alvoki.Storage.Disk.RetainedCollectionPowerLoss

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- The selected seals and keeper have the same held no-follow extent as
their canonical descriptor, with the keeper's unselected tail included
only in its physical size. Only selected payloads need successful reads. -/
structure CachedWalFileReports (dir : DiskDirectory) (reports : OpenPathReadReports)
    (wal : WalSegmentImage) (watermark : Nat) (tail : ByteArray) where
  readSeal : FilePath → Nat → Except IO.Error ByteArray
  readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray
  sealed : ∀ segment ∈ (wal.readDescriptors watermark).dropLast, ∀ metadata,
    reports.lstat (dir.file (.walSegment segment.first)) = .ok metadata →
    metadata.byteSize.toNat = segment.bytes.size ∧ segment.bytes.size < USize.size ∧
    readSeal (dir.file (.walSegment segment.first)) segment.bytes.size = .ok segment.bytes
  keeper : ∀ metadata, reports.lstat (dir.file (.walSegment wal.active.first)) = .ok metadata →
    metadata.byteSize.toNat = (wal.active.bytes ++ tail).size ∧
    readKeeper (dir.file (.walSegment wal.active.first)) wal.active.bytes.size metadata.byteSize.toNat =
      .ok wal.active.bytes

/-- Every selected extent retains its metadata from the input scan. -/
theorem selectWalExtentsThrough_required_subset {extents required : List (Nat × IO.FS.Metadata)}
    {watermark through : Nat} {newer : List Nat}
    (selected : selectWalExtentsThrough extents watermark through = some (required, newer)) :
    required ⊆ extents := by
  unfold selectWalExtentsThrough at selected
  cases chosen : ((extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max? with
  | none => simp [chosen, Bind.bind, Option.bind] at selected
  | some first =>
    simp only [chosen, Bind.bind, Option.bind, Pure.pure] at selected
    have kept := congrArg Prod.fst (Option.some.inj selected)
    dsimp only at kept
    rw [← kept]
    exact fun _ member => (List.mem_filter.mp (List.takeWhile_subset _ member)).1

/-- Checked spans and their bound-matched payload callbacks build the report
consumed by the cached reader's effect proof. -/
theorem CachedWalPayloadReports.of_spans {dir : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)}
    {keeper : Nat} {keeperBytes : ByteArray} {fileSize : Nat}
    (spans : WalSegmentSpans through files)
    (names : required.map Prod.fst = files.map Prod.fst)
    (last : files.getLast? = some (keeper, keeperBytes))
    (keeperWidth : keeperBytes.size = (through - keeper) * frameSize)
    (sealRead : ∀ entry ∈ required, ∀ file ∈ files.dropLast, entry.1 = file.1 →
      entry.2.byteSize.toNat = file.2.size ∧ file.2.size < USize.size ∧
      readSeal (dir.file (.walSegment file.1)) file.2.size = .ok file.2)
    (keeperRead : ∀ entry ∈ required, entry.1 = keeper →
      entry.2.byteSize.toNat = fileSize ∧ keeperBytes.size ≤ entry.2.byteSize.toNat ∧
      readKeeper (dir.file (.walSegment keeper)) keeperBytes.size entry.2.byteSize.toNat = .ok keeperBytes) :
    CachedWalPayloadReports dir through readSeal readKeeper required files fileSize := by
  induction spans generalizing required with
  | @active first bytes _ =>
    obtain ⟨⟨named, metadata⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp names
    have ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj last)
    obtain ⟨size, covers, read⟩ := keeperRead (named, metadata) (by simp) rfl
    rw [← size]
    exact .keeper keeperWidth (keeperWidth ▸ covers) (keeperWidth ▸ read)
  | @sealed first next nextBytes rest bytes forward width remaining ih =>
    obtain ⟨⟨found, metadata⟩, later, rfl, rfl, tailNames⟩ := List.map_eq_cons_iff.mp names
    obtain ⟨⟨following, nextMetadata⟩, after, rfl, rfl, _⟩ := List.map_eq_cons_iff.mp tailNames
    obtain ⟨extent, fits, read⟩ :=
      sealRead (found, metadata) (by simp) (found, bytes) (by simp) rfl
    refine .sealed forward width extent fits read (ih tailNames (by simpa using last) ?_ ?_)
    · intro entry selected file member same
      exact sealRead entry (List.mem_cons_of_mem _ selected) file
        (by simpa using List.mem_cons_of_mem (found, bytes) member) same
    · exact fun entry selected => keeperRead entry (List.mem_cons_of_mem _ selected)

/-- The complete held listing, exact metadata and bounded payload reports
derive the cached read at the actual marker. Selection and emitted bytes
follow from the canonical surviving layout rather than a prepared result. -/
theorem HealthyBoundedWalReports.readSelectedCachedWithState {directory owners descriptor wal pair watermark durable tail}
    {state : Type}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (cached : CachedWalFileReports directory raw.reports wal watermark tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (chosen : wal.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) (sameWatermark : range.watermark = watermark)
    (atEnd : range.through = history.length) {count : UInt64} (absolute : count.toNat = range.through * frameSize) :
    (readSelectedWithCachedExtents directory watermark count (fun path => liftExcept (raw.list path))
      (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (cached.readSeal path size))
      (fun path count size => liftExcept (cached.readKeeper path count size)) :
        EStateM IO.Error state (WalSegmentMarkerReads × Nat)) =
      readSelectedWithPrefix directory watermark count (fun path => liftExcept (raw.list path))
        (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
        (fun path => liftExcept (raw.reports.readBin path)) (fun path count => liftExcept (raw.readPrefix path count)) := by
  obtain ⟨first, begins, throughBound, addresses, chain, _⟩ := layout.selects valid chosen decoded
  have covered := (DirectoryPublication.Bindings.walRange_accounting decoded).2.1
  have counted : count.toNat / frameSize = range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  rw [sameWatermark] at begins addresses chain covered
  have throughAddresses := layout.selectedThroughEnd atEnd addresses
  have projected := raw.reports.walSegmentExtents_offsets directory (raw.entries.toList.map (·.fileName))
  rw [raw.scan layout] at projected
  obtain ⟨extents, scanned, offsets⟩ : ∃ extents : List (Nat × IO.FS.Metadata),
      readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (raw.reports.lstat path))
        (raw.entries.toList.map (·.fileName)) = .ok extents ∧
      extents.map Prod.fst = wal.segments.map WalSegment.first := by
    cases scanned : readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (raw.reports.lstat path))
        (raw.entries.toList.map (·.fileName)) with
    | error cause => simp [scanned, Except.map] at projected
    | ok extents =>
      exact ⟨extents, rfl, Except.ok.inj (by simpa only [scanned, Except.map] using projected)⟩
  obtain ⟨required, selected, names⟩ : ∃ required,
      selectWalExtentsThrough extents watermark (count.toNat / frameSize) = some (required, []) ∧
      required.map Prod.fst = (wal.readDescriptors watermark).map WalSegment.first := by
    have projects := selectWalExtentsThrough_offsets extents watermark (count.toNat / frameSize)
    have throughAtCount := counted.symm ▸ throughAddresses
    rw [offsets, throughAtCount] at projects
    cases admits : selectWalExtentsThrough extents watermark (count.toNat / frameSize) with
    | none => rw [admits] at projects; contradiction
    | some result =>
      obtain ⟨required, newer⟩ := result
      rw [admits] at projects
      obtain ⟨names, rfl⟩ := Prod.mk.inj (Option.some.inj projects)
      exact ⟨required, rfl, names⟩
  obtain ⟨seals, split⟩ := wal.readDescriptors_endsActive watermark
  let files := (wal.readDescriptors watermark).map (fun segment => (segment.first, segment.bytes))
  have spans : WalSegmentSpans (count.toNat / frameSize) files := by
    rw [split] at chain
    have checks := chain.checkReadSpans (tail := ByteArray.empty) (Nat.le_trans begins covered) throughBound
    rw [counted]
    simpa [files, split] using (checkWalSegmentSpans_iff ..).mp checks |>.2
  have listedNames : required.map Prod.fst = files.map Prod.fst := by
    simpa [files, List.map_map, Function.comp_def] using names
  have last : files.getLast? = some (wal.active.first, wal.active.bytes) := by simp [files, split]
  have keeperWidth : wal.active.bytes.size = (count.toNat / frameSize - wal.active.first) * frameSize := by
    rw [counted, layout.activeBytes, WAL.encode_size, List.length_drop, atEnd, Nat.mul_comm]
  have metadata (entry) (member : entry ∈ required) :
      raw.reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2 :=
    OpenPathReadReports.walSegmentExtents_metadata scanned (selectWalExtentsThrough_required_subset selected member)
  have payloads : CachedWalPayloadReports directory (count.toNat / frameSize) cached.readSeal cached.readKeeper
      required files (wal.active.bytes ++ tail).size := by
    apply CachedWalPayloadReports.of_spans spans listedNames last keeperWidth
    · intro entry member file selectedFile same
      have fromSeal : file ∈ seals.map (fun segment => (segment.first, segment.bytes)) := by
        simpa [files, split] using selectedFile
      obtain ⟨segment, found, rfl⟩ := List.mem_map.mp fromSeal
      have inSeals : segment ∈ (wal.readDescriptors watermark).dropLast := by simpa [split] using found
      exact cached.sealed segment inSeals entry.2 (by simpa only [same] using metadata entry member)
    · intro entry member same
      obtain ⟨size, read⟩ := cached.keeper entry.2 (by simpa only [same] using metadata entry member)
      exact ⟨size, by rw [size, ByteArray.size_append]; exact Nat.le_add_right .., read⟩
  funext initial
  have actual := readSelectedWithCachedExtents_reportedEffects directory watermark count raw.list
    (fun path => .ok (raw.reports.lstat path)) cached.readSeal cached.readKeeper
    ⟨aligned, counted.symm ▸ covered⟩ raw.listing scanned selected payloads initial
  rw [actual, readSelectedWithPrefix_liftReports,
    raw.readSelectedBounded layout atEnd covered absolute addresses]
  rfl

/-- Execute the cached opener with the bounded checkpoint, seal and keeper
reports at the same held paths. The repair operations are effectful. -/
def HealthyBoundedWalReports.reopenCachedWithState {directory owners descriptor wal pair watermark durable tail}
    {state : Type}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    (cached : CachedWalFileReports directory raw.reports wal watermark tail)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit) : EStateM IO.Error state Reopened :=
  reopenMarkedBoundedWithCachedExtents directory (fun path => liftExcept (raw.reports.readOptional path))
    (fun path => liftExcept (checkpointRunSizeReport raw.reports path))
    (fun path count => liftExcept (sizes.readPrefix path count))
    (fun path => liftExcept (raw.list path))
    (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
    (fun path count => liftExcept (cached.readSeal path count))
    (fun path count size => liftExcept (cached.readKeeper path count size))
    removeFile write sync renameFile

/-- The exact checkpoint files select the same watermark and the real
marker selects the same WAL extent. Thus the entire cached open agrees
with the earlier bounded report worker, including its repair effects. -/
theorem HealthyBoundedWalReports.reopenCachedWithState_eq {directory owners descriptor wal pair watermark durable tail}
    {state : Type}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    (cached : CachedWalFileReports directory raw.reports wal watermark tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (chosen : wal.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) (sameWatermark : range.watermark = watermark)
    (atEnd : range.through = history.length)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit) :
    raw.reopenCachedWithState sizes cached removeFile write sync renameFile =
      raw.reopenWithState removeFile write sync renameFile := by
  obtain ⟨reportedWatermark, _, marker, count, visible, parsed, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting decoded
  have clock := (Option.some.inj (selected.watermark.symm.trans reportedWatermark)).trans sameWatermark
  have checkpointRead := raw.readSizedCheckpoint_eq (state := state) sizes selected
  rw [readCheckpoint_liftReports (validateReport := fun result => result.mapError IO.userError)
    _ _ (by intro _ _; rfl), raw.readCheckpoint selected] at checkpointRead
  have markerRead : (liftExcept (raw.reports.readOptional (directory.file .walBoundary)) :
      EStateM IO.Error state _) = pure (some marker) := by
    rw [raw.marker, visible]
    rfl
  have walRead := raw.readSelectedCachedWithState (state := state) cached layout valid chosen decoded sameWatermark atEnd absolute
  rw [← raw.reopenSizedCheckpointWithState_eq sizes selected]
  unfold HealthyBoundedWalReports.reopenCachedWithState HealthyBoundedWalReports.reopenSizedCheckpointWithState
  refine reopenMarkedBoundedWithCachedExtents_eq_of_selectedWal _ _ _ _ _ _ _ _ _ _ _ _ _ _
    checkpointRead markerRead parsed ?_
  dsimp only
  rwa [clock]

theorem HealthyBoundedWalReports.readSelectedCached {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (cached : CachedWalFileReports directory raw.reports wal watermark tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (chosen : wal.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) (sameWatermark : range.watermark = watermark)
    (atEnd : range.through = history.length) {count : UInt64} (absolute : count.toNat = range.through * frameSize) :
    (readSelectedWithCachedExtents directory watermark count (fun path => liftExcept (raw.list path))
      (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (cached.readSeal path size))
      (fun path count size => liftExcept (cached.readKeeper path count size)) :
        EStateM IO.Error FileImage (WalSegmentMarkerReads × Nat)) =
      readSelectedWithPrefix directory watermark count (fun path => liftExcept (raw.list path))
        (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
        (fun path => liftExcept (raw.reports.readBin path)) (fun path count => liftExcept (raw.readPrefix path count)) :=
  raw.readSelectedCachedWithState (state := FileImage) cached layout valid chosen decoded sameWatermark atEnd absolute

abbrev HealthyBoundedWalReports.reopenCached {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail) :=
  raw.reopenCachedWithState (state := FileImage)

theorem HealthyBoundedWalReports.reopenCached_eq {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    (cached : CachedWalFileReports directory raw.reports wal watermark tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (chosen : wal.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) (sameWatermark : range.watermark = watermark)
    (atEnd : range.through = history.length)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    raw.reopenCached sizes cached removeFile write sync renameFile =
      raw.reopen removeFile write sync renameFile :=
  raw.reopenCachedWithState_eq sizes cached layout valid chosen decoded sameWatermark atEnd selected
    removeFile write sync renameFile

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Use the acquired inventory and exact file reads at an admitted WAL unlink
cut to interpret the cached and prefix readers as the same recovery action. -/
theorem SegmentedWriterState.RetainedReady.collectionPowerLossCached_eq {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    {cut : WalSealedUnlinkImage} {pair : DirectoryPublication.Bindings} {sealed : List WalSegment}
    (trace : WalSealedUnlinkTrace state.wal cut)
    (pairSurvives : pair ∈ cut.visible.directory.crashImages) (sealedSurvives : sealed ∈ cut.crashSealed)
    {nextDescriptor : Nat}
    (raw : HealthyBoundedWalReports directory
      ((state.owners.release (directory.file .lock) descriptor).set (directory.file .lock) (some nextDescriptor))
      nextDescriptor (cut.crash pair sealed).visible pair state.target.range.watermark
      state.published.durable ByteArray.empty)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest state.published.durable)
    (cached : CachedWalFileReports directory raw.reports (cut.crash pair sealed).visible
      state.target.range.watermark ByteArray.empty)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    raw.reopenCached sizes cached removeFile write sync renameFile = raw.reopen removeFile write sync renameFile := by
  have retry := ((trace.powerLoss pairSurvives sealedSurvives).projects ready.layout).1
  have survivingPair : pair = state.target.pair :=
    (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have decoded : pair.walRange = some state.target.range := survivingPair.symm ▸ state.target.decoded
  have selected : SelectedIntegrityCheckpoint state.published.durable pair.manifest state.checkpoint := by
    rw [survivingPair]
    exact ready.resumed.selected
  exact raw.reopenCached_eq sizes cached (retry.readLayout ready.layout) (retry.valid ready.valid)
    (List.mem_cons_self ..) decoded rfl ready.resumed.through selected removeFile write sync renameFile

/-- An admitted collection crash has a healthy cached reopen from the
exact surviving files. The final writer keeps the acknowledged history
and the strict checkpoint selected before the unlink. -/
theorem SegmentedWriterState.RetainedReady.openAfterCollectionPowerLossCached {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    {cut : WalSealedUnlinkImage} {pair : DirectoryPublication.Bindings} {sealed : List WalSegment}
    (trace : WalSealedUnlinkTrace state.wal cut)
    (pairSurvives : pair ∈ cut.visible.directory.crashImages) (sealedSurvives : sealed ∈ cut.crashSealed)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (raw : HealthyBoundedWalReports directory
      ((state.owners.release (directory.file .lock) descriptor).set (directory.file .lock) (some nextDescriptor))
      nextDescriptor (cut.crash pair sealed).visible pair state.target.range.watermark
      state.published.durable ByteArray.empty)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest state.published.durable)
    (cached : CachedWalFileReports directory raw.reports (cut.crash pair sealed).visible
      state.target.range.watermark ByteArray.empty)
    (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let survivors := (cut.crash pair sealed).visible
    let owners := state.owners.release (directory.file .lock) descriptor
    let files := survivors.checkpointReopenFiles survivors.directory none
    sync #[directory.path] files = .ok () files.syncDirectory →
    sync #[directory.file (.walSegment survivors.active.first)] files.syncDirectory =
      .ok () files.syncDirectory.syncKeeper →
    ∃ session final, ∃ next : SegmentedWriterState,
      runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
        (raw.reopenCached sizes cached removeFile write sync renameFile) ⟨files, owners⟩ = .ok session final ∧
      session.directory = directory ∧ session.descriptor = nextDescriptor ∧
      session.phase = .ready next.installed ∧ next.files = final.image ∧ next.owners = final.owners ∧
      next.target = state.target ∧ next.history = state.history ∧ next.checkpoint = state.checkpoint ∧
      next.installed.generation = state.installed.generation ∧ next.RetainedReady directory nextDescriptor := by
  intro survivors owners files syncDirectory syncKeeper
  have cachedEq := ready.collectionPowerLossCached_eq trace pairSurvives sealedSurvives raw sizes cached
    removeFile write sync renameFile
  obtain ⟨_, session, final, next, returned, path, lock, phase, image, owner, _, _, target, history, checkpoint,
    generation, _, readyNext⟩ :=
    ready.openAfterCollectionPowerLoss trace pairSurvives sealedSurvives liveRefs fresh raw unlock
      removeFile write sync renameFile syncDirectory syncKeeper
  rw [cachedEq]
  exact ⟨session, final, next, returned, path, lock, phase, image, owner, target, history, checkpoint, generation,
    readyNext⟩

end Alvoki.Storage.DiskSession
