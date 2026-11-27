import Alvoki.Storage.Disk.Proofs.Session.CapturedSealReadCensus

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

private abbrev ReadState := CensusDirectoryCache × CensusOpenState

/-- Interpret the shared native optional metadata reader and retain the
census of its observed open. The successful branch projects that same
open report to recover its inventory. The observed release and drops
determine the census for the next action. -/
def readTemporaryMetadata (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (released : FilePath → List LockReferenceDrop) (path : FilePath) :
    EStateM IO.Error ReadState (Option ByteArray) := fun (cache, census, files) =>
  match runCachedMetadataRead reads directory path 0 with
  | .error cause _ => .error cause (cache, census, files)
  | .ok none _ => .ok none (cache, census, files)
  | .ok (some bytes) _ =>
    match reads.openRead path with
    | .error cause => .error cause (cache, census, files)
    | .ok handle => .ok (some bytes) (cache, handle.1.afterDrops (released path), files)

namespace TemporaryPrefixCustody

theorem readMetadata {reads directory path name root view}
    {opened : RunChunkPathReport reads path name root view}
    {initial : DescriptorInventory} {released : FilePath → List LockReferenceDrop}
    (custody : TemporaryPrefixCustody opened initial (released path)) {bytes : ByteArray} {cursor : Nat}
    (read : runCachedMetadataRead reads directory path 0 = .ok (some bytes) cursor)
    (cache : CensusDirectoryCache) (files : LockedFileState FileImage) :
    readTemporaryMetadata reads directory released path (cache, initial, files) =
      .ok (some bytes) (cache, initial.afterDrops (custody.beforeOpen ++ released path), files) := by
  simp only [readTemporaryMetadata, read, opened.opened, custody.closes.1]

end TemporaryPrefixCustody

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- The manifest is read first. The missing branch uses the observed
no-follow ENOENT and allocates no temporary description. -/
inductive CapturedManifestCensus (report : CapturedMarkedReadReports admission layout published)
    (released : FilePath → List LockReferenceDrop) : List LockReferenceDrop → Prop where
  | missing (bound : retry.image.directory.active.manifest = none) : CapturedManifestCensus report released []
  | present {bytes : ByteArray} (bound : retry.image.directory.active.manifest = some bytes)
      (file : HeldMetadataFile report.reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes)
      (fits : IntegrityCheckpoint.acquisitionSize bytes < USize.size)
      (custody : TemporaryPrefixCustody file.calls admission.reached (released (directory.file .manifest))) :
      CapturedManifestCensus report released (custody.beforeOpen ++ released (directory.file .manifest))

theorem CapturedManifestCensus.reads {report : CapturedMarkedReadReports admission layout published}
    {released : FilePath → List LockReferenceDrop} {drops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report released drops) :
    readTemporaryMetadata report.reads directory released (directory.file .manifest)
      (admission.cache, admission.reached, admission.held) =
        .ok retry.image.directory.active.manifest
          (admission.cache, admission.reached.afterDrops drops, admission.held) := by
  cases manifest with
  | missing bound =>
    obtain ⟨_, name, message, absent⟩ := report.metadata.manifestMissing bound
    have noDrops : admission.reached.afterDrops [] = admission.reached := by
      cases admission.reached with
      | mk slots distinct inode =>
        simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
    rw [readTemporaryMetadata, runCachedMetadataRead_missing _ _ _ name message absent, bound, noDrops]
  | present bound file fits custody =>
    have eligible := (DirectoryPublication.Bindings.walRange_accounting layout.decoded).1
    rw [bound] at eligible
    obtain ⟨_, decoded, _⟩ := selectedCheckpointWatermark_present_iff.mp eligible
    have read := file.manifestPrefix fits
    rw [IntegrityCheckpoint.acquisitionPrefix_eq_of_decode decoded] at read
    rw [bound]
    exact custody.readMetadata read admission.cache admission.held

/-- The drops accumulated by the increasing manifest-index traversal. -/
def runReadDrops (events : Nat → List LockReferenceDrop) : Nat → List LockReferenceDrop
  | 0 => []
  | index + 1 => runReadDrops events index ++ events index

/-- For each actual selected generation/index, the raw opened description
comes from the previous census, and its observed release closes the step. -/
structure CapturedRunReadCensus (report : CapturedMarkedReadReports admission layout published)
    (initial : DescriptorInventory) where
  events : Nat → List LockReferenceDrop
  released : FilePath → List LockReferenceDrop
  runs : ∀ bytes manifest, retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat, ∀ payload,
    published.durable manifest.header.generation index = some payload →
      ∃ object, admission.view.child admission.root (renderRunFileName manifest.header.generation index) = some object ∧
        report.reads.objectBytes (admission.view.modelObject object) = some payload ∧
        ∃ file : RunChunkPathReport report.reads (directory.file (.run manifest.header.generation index))
            (renderRunFileName manifest.header.generation index) admission.root admission.view,
          ∃ custody : TemporaryPrefixCustody file (initial.afterDrops (runReadDrops events index))
              (released (directory.file (.run manifest.header.generation index))),
            events index = custody.beforeOpen ++ released (directory.file (.run manifest.header.generation index))

def CapturedMarkedReadReports.readCheckpointFromCensus (report : CapturedMarkedReadReports admission layout published)
    (metadataRelease runRelease : FilePath → List LockReferenceDrop) :
    EStateM IO.Error ReadState (Option (PackedTable × UInt64)) :=
  readIntegrityCheckpointSized directory
    (readTemporaryMetadata report.reads directory metadataRelease (directory.file .manifest))
    (fun path => liftExcept (checkpointRunSizeReport report.walReads.inventory.reports path))
    (readTemporaryPrefix report.reads (IO.userError checkpointIntegrityMismatch) runRelease)

/-- The executable sized checkpoint reader produces the selected table
from the durable run map and reaches the census left by exactly those runs. -/
theorem CapturedRunReadCensus.reads {report : CapturedMarkedReadReports admission layout published}
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) :
    report.readCheckpointFromCensus metadataRelease runs.released (admission.cache, admission.reached, admission.held) =
      .ok checkpoint (admission.cache,
        (admission.reached.afterDrops manifestDrops).afterDrops
          (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest)), admission.held) := by
  let initial := admission.reached.afterDrops manifestDrops
  let atIndex : Nat → ReadState := fun index =>
    (admission.cache, initial.afterDrops (runReadDrops runs.events index), admission.held)
  let sizes := SizedCheckpointRunReports.ofChunkReads selected report.reads report.stat report.chunkReads
  unfold CapturedMarkedReadReports.readCheckpointFromCensus
  apply sizes.readExactWithState selected _ _ _ atIndex
  · have start : initial.afterDrops [] = initial := by
      cases initial with
      | mk slots distinct inode =>
        simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
    simpa only [atIndex, runReadDrops, start] using manifest.reads
  · intro bytes manifest bound decoded index within payload stored
    obtain ⟨object, objectBound, contents, file, custody, ordered⟩ := runs.runs bytes manifest bound decoded
      index within payload stored
    have fits := selected.runSizeFits bound decoded within stored
    have read := custody.readPrefix (IO.userError checkpointIntegrityMismatch) objectBound contents fits
      admission.cache admission.held
    simpa only [atIndex, runReadDrops, ← DescriptorInventory.afterDrops_append, ordered] using read

/-- The marker is opened after the selected runs. Its bounded EOF read
uses that exact description and the finalizer releases its temporary slot. -/
structure CapturedMarkerCensus (report : CapturedMarkedReadReports admission layout published)
    (initial : DescriptorInventory) (released : FilePath → List LockReferenceDrop) where
  bytes : ByteArray
  bound : retry.image.directory.active.walBoundary = some bytes
  file : HeldMetadataFile report.reads (directory.file .walBoundary) "WAL.commit" admission.view admission.root bytes
  available : PrefixChunksAvailableUntilEof bytes (report.reads.readChunk file.observesFile.slot.description)
  custody : TemporaryPrefixCustody file.calls initial (released (directory.file .walBoundary))

/-- The marker callback returns the exact accepted bytes before the WAL scan. -/
theorem CapturedMarkerCensus.reads {report : CapturedMarkedReadReports admission layout published}
    {initial : DescriptorInventory} {released : FilePath → List LockReferenceDrop}
    (marker : CapturedMarkerCensus report initial released) :
    readTemporaryMetadata report.reads directory released (directory.file .walBoundary)
      (admission.cache, initial, admission.held) = .ok (some marker.bytes)
        (admission.cache, initial.afterDrops
          (marker.custody.beforeOpen ++ released (directory.file .walBoundary)), admission.held) := by
  obtain ⟨_, _, bytes, count, bound, decoded, _⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have same : bytes = marker.bytes := Option.some.inj (bound.symm.trans marker.bound)
  have size : marker.bytes.size = 24 := by
    rw [← same, ← WAL.Boundary.decode_reencode decoded, WAL.Boundary.encode_size]
  have covered : marker.bytes.size ≤ WAL.Boundary.acquisitionLimit := by rw [size]; decide
  have read := marker.file.markerPrefix marker.available
  rw [Nat.min_eq_right covered, ByteArray.extract_zero_size] at read
  exact marker.custody.readMetadata read admission.cache admission.held

/-- The actual bounded preparation reaches the WAL reader at the census
left by manifest acquisition, ordered checkpoint reads and marker release.
The scan's stream opens on that census, with the held lock and cache. -/
theorem CapturedMarkedReadReports.beforeWalScan (report : CapturedMarkedReadReports admission layout published)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (marker : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (marker.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    (readWal : Nat → UInt64 → EStateM IO.Error ReadState (WalSegmentMarkerReads × Nat)) :
    let atScan := admission.reached.afterDrops report.listing.beforeOpen
    admission.owner ∈ atScan.slots ∧ admission.cached ∈ atScan.slots ∧
    report.scanWal directory.path (admission.cache, atScan, admission.held) =
      .ok (report.listing.scan.entries directory.path) (admission.cache, report.listing.afterClose, admission.held) ∧
    (checkpoint.getD (.empty, 0)).1.committed.toNat = layout.range.watermark ∧
    (∃ length, WAL.Boundary.decode marker.bytes = .ok length ∧ length.toNat = layout.range.through * WAL.frameSize) ∧
    prepareBoundedMarkedFromReaders directory (report.readCheckpointFromCensus metadataRelease runs.released)
      (readTemporaryMetadata report.reads directory metadataRelease) readWal
      (admission.cache, admission.reached, admission.held) =
    prepareBoundedMarkedFromReaders directory (pure checkpoint) (fun _ => pure (some marker.bytes)) readWal
      (admission.cache, atScan, admission.held) := by
  intro atScan
  have drops : report.lifetime.drops = report.listing.beforeOpen ++
      (report.listing.duringScan ++ [report.listing.stream.closeEvent]) :=
    report.listing.drops.trans (List.append_assoc ..)
  have scanLive := report.lifetime.liveAtPrefix drops
  obtain ⟨watermark, _, bytes, length, bound, decoded, count⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have markerBytes : bytes = marker.bytes := Option.some.inj (bound.symm.trans marker.bound)
  refine ⟨scanLive.1, scanLive.2, report.scanWal_fromEntry, Option.some.inj (selected.watermark.symm.trans watermark),
    ⟨length, markerBytes ▸ decoded, count⟩, ?_⟩
  have capture : ((admission.reached.afterDrops manifestDrops).afterDrops
        (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))).afterDrops
          (marker.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)) = atScan := by
    simp only [atScan, chronology, DescriptorInventory.afterDrops_append]
  simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, runs.reads manifest selected, marker.reads,
    capture, Pure.pure, EStateM.pure]

/-- Interpret the actual bounded preparation over the custody reports for
the selected temporary reads and the keeper. -/
def CapturedMarkedReadReports.prepareFromCensus (report : CapturedMarkedReadReports admission layout published)
    (metadataRelease runRelease sealRelease : FilePath → List LockReferenceDrop)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error ReadState ByteArray) :
    EStateM IO.Error ReadState (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromReaders directory (report.readCheckpointFromCensus metadataRelease runRelease)
    (readTemporaryMetadata report.reads directory metadataRelease)
    (fun watermark length => readSelectedWithCachedExtents directory watermark length report.scanWal
      report.inspectWal (readTemporarySeal report.reads sealRelease) readKeeper)

/-- The admitted marked preparation carries one census through the
manifest, exact selected runs and marker, checked directory stream and
temporary seal reads. It reaches the keeper with its actual path, extent
and selected length. The continuation still checks the keeper result and
performs the original replay and plan construction. -/
theorem CapturedMarkedReadReports.beforeKeeper (report : CapturedMarkedReadReports admission layout published)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (marker : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (marker.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    (captured : CapturedKeeperOpenReports report) {released : FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)}
    (seals : CapturedSealReadChain report released required report.listing.afterClose captured.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ captured.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ retry.image.later.visible, layout.range.through < start)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error ReadState ByteArray) :
    admission.owner ∈ captured.atOpen.slots ∧ admission.cached ∈ captured.atOpen.slots ∧
    report.listing.opened.inode report.listing.stream.description = admission.reached.inode admission.cached.description ∧
    ∃ length,
      WAL.Boundary.decode marker.bytes = .ok length ∧ length.toNat = layout.range.through * WAL.frameSize ∧
      report.prepareFromCensus metadataRelease runs.released released readKeeper
        (admission.cache, admission.reached, admission.held) =
      prepareBoundedMarkedFromReaders (m := EStateM IO.Error ReadState) directory
        (pure checkpoint) (fun _ => pure (some marker.bytes))
        (fun _ _ => do
          let (last, extent) ← readCachedWalPayloads directory (length.toNat / WAL.frameSize)
            (readTemporarySeal report.reads released) readKeeper [(layout.keeper.first, report.wal.keeper.calls.metadata)]
          pure (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++ last, retry.image.later.visible⟩, extent))
        (admission.cache, captured.atOpen, admission.held) := by
  let walRead := fun watermark length => readSelectedWithCachedExtents directory watermark length report.scanWal
    report.inspectWal (readTemporarySeal report.reads released) readKeeper
  obtain ⟨_, _, _, watermark, ⟨length, decoded, count⟩, entered⟩ :=
    report.beforeWalScan manifest runs selected marker chronology walRead
  obtain ⟨extents, chosen, scanned, selection, ordered, _⟩ := report.catalog.scanSelected following later count
  have listed := (CheckedDirectoryReadReport.scan_complete directory.path report.listing.eof report.listing.closed
    report.listing.complete).1
  have entries := Except.ok.inj (report.catalog.listed.symm.trans (report.listed.trans listed))
  rw [entries] at scanned
  have reportedStat (entry) (member : entry ∈ chosen) :=
    OpenPathReadReports.walSegmentExtents_metadata scanned (selectWalExtentsThrough_required_subset selection member)
  have same := seals.matchesExtents (offsets.trans ordered.symm) reportedStat
  rw [← same] at selection
  have aligned : length.toNat % WAL.frameSize = 0 := by rw [count, Nat.mul_mod_left]
  have through : length.toNat / WAL.frameSize = layout.range.through := by
    rw [count, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have covers : layout.range.watermark ≤ length.toNat / WAL.frameSize :=
    through.symm ▸ (DirectoryPublication.Bindings.walRange_accounting layout.decoded).2.1
  obtain ⟨owner, directoryLive, earlier, prior, contents, reached⟩ :=
    report.selectedWalReachesKeeper captured aligned covers scanned selection seals retained readKeeper
  have earlierOffsets : earlier.map Prod.fst = layout.sealed.map WalSegment.first := by
    simpa only [List.map_dropLast, offsets, List.map_append, List.map_cons, List.map_nil, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil] using prior
  let exactSeals := layout.sealed.map (fun segment => (segment.first, segment.bytes))
  have exactOffsets : exactSeals.map Prod.fst = layout.sealed.map WalSegment.first := by
    simp [exactSeals, List.map_map, Function.comp_def]
  let payload (first : Nat) := (first, (retry.image.kept first).getD ByteArray.empty)
  have readsStored (files : List (Nat × ByteArray))
      (all : ∀ file ∈ files, retry.image.kept file.1 = some file.2) :
      files = (files.map Prod.fst).map payload := by
    rw [List.map_map]
    calc
      files = files.map id := (List.map_id _).symm
      _ = _ := List.map_congr_left fun file member => by cases file; simp [payload, all _ member]
  have stored : ∀ file ∈ exactSeals, retry.image.kept file.1 = some file.2 := by
    intro file member
    obtain ⟨segment, held, rfl⟩ := List.mem_map.mp member
    exact report.wal.kept segment held
  have exactEarlier : earlier = exactSeals := by
    calc
      earlier = (earlier.map Prod.fst).map payload := readsStored _ contents
      _ = (exactSeals.map Prod.fst).map payload := congrArg (List.map payload) (earlierOffsets.trans exactOffsets.symm)
      _ = exactSeals := (readsStored _ stored).symm
  refine ⟨owner, directoryLive, report.listing.sameDirectoryObject, length, decoded, count, ?_⟩
  have markerDecoded : (liftExcept ((WAL.Boundary.decode marker.bytes).mapError IO.userError) : EStateM IO.Error ReadState UInt64) =
      pure length := by rw [decoded]; rfl
  change prepareBoundedMarkedFromReaders directory (report.readCheckpointFromCensus metadataRelease runs.released)
    (readTemporaryMetadata report.reads directory metadataRelease) walRead
    (admission.cache, admission.reached, admission.held) = _
  rw [entered]
  simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, markerDecoded, watermark]
  dsimp only [walRead]
  rw [reached, exactEarlier]
  rfl

/-- Once the exact checkpoint, marker and selected WAL reads return,
the bounded prepare schedule derives the same plan and replay as its
read-only projection. It retains the heap returned by the WAL reader. -/
theorem CapturedMarkedReadReports.preparesFromSelectedWal
    (report : CapturedMarkedReadReports admission layout published)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    {marker : ByteArray} {length : UInt64}
    (markerBound : retry.image.directory.active.walBoundary = some marker)
    (decoded : WAL.Boundary.decode marker = .ok length)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (laterValid : retry.image.later.Beyond layout.range.through)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {heap : Type} {before reached : heap}
    (readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat))
    (seen : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat length before =
      .ok (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
        [(layout.keeper.first, layout.keeper.bytes)], retry.image.later.visible⟩,
        report.wal.keeper.calls.metadata.byteSize.toNat) reached) :
    ∃ opened,
      prepareBoundedMarkedFromReaders directory (pure checkpoint) (fun _ => pure (some marker)) readWal before =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) reached ∧
      report.walReads.prepare report.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) ∧
      ∃ model, opened.table.Refines model ∧ RepresentsWalHistory history model := by
  obtain ⟨watermark, _, canonicalMarker, canonicalLength, bound, canonicalDecoded, count⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  rw [Option.some.inj (bound.symm.trans markerBound), decoded] at canonicalDecoded
  have lengthEq := Except.ok.inj canonicalDecoded
  subst canonicalLength
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected report.reads
    report.stat report.chunkReads
  obtain ⟨opened, reportedCheckpoint, model, projected, exactCheckpoint, reference, generation, bytes, keeper,
    _, _, refined, represents, _⟩ :=
    report.walReads.prepares (admission.reached, admission.held) laterValid following accepted ordered
      sizes (report.metadata.manifestRead layout.decoded) (report.metadata.markerRead layout.decoded)
  have checkpointSame := exactCheckpoint.uniqueResult selected
  subst reportedCheckpoint
  let files := layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
    [(layout.keeper.first, layout.keeper.bytes)]
  have baseWatermark := Option.some.inj (selected.watermark.symm.trans watermark)
  have replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length files =
      .ok (WAL.encode (history.drop layout.first), opened.table) := by
    simpa only [files, ByteArray.append_empty] using layout.chain.replaysMarked ByteArray.empty
      (layout.through ▸ count) (baseWatermark.symm ▸ layout.covers) ordered reference
  have tableSeen : (liftExcept ((recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length files).mapError
      IO.userError) : EStateM IO.Error heap _) reached =
        .ok (WAL.encode (history.drop layout.first), opened.table) reached := by
    rw [replayed]
    rfl
  have lastFile : files.getLast? = some (layout.keeper.first, layout.keeper.bytes) := by simp [files]
  have lengthSeen : (liftExcept ((WAL.Boundary.decode marker).mapError IO.userError) : EStateM IO.Error heap UInt64) =
      pure length := by rw [decoded]; rfl
  have exactLength : opened.walBytes = length := UInt64.toNat_inj.mp (bytes.trans (layout.through ▸ count).symm)
  have exactOpened : (⟨opened.table, (checkpoint.getD (.empty, 0)).2, length, layout.keeper.first⟩ : Reopened) = opened := by
    rw [← generation, ← exactLength, ← keeper]
  have through : length.toNat / WAL.frameSize = layout.range.through := by
    rw [count, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have extent : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    report.wal.keeper.observesFile.extent
  dsimp only [files] at tableSeen lastFile
  refine ⟨opened, ?_, projected, model, refined, represents⟩
  simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, lengthSeen, seen,
    extent, tableSeen, lastFile, exactOpened, through]
  rfl

/-- The chronological preparation and the read-only projection return
the same bounded plan, replayed table, generation, and physical keeper
extent. Only the return from the chronological reader carries the reached
keeper cache and census into the next action. -/
theorem CapturedMarkedReadReports.preparesFromCensus (report : CapturedMarkedReadReports admission layout published)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (marker : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (marker.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    (captured : CapturedKeeperOpenReports report) {released : FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)}
    (seals : CapturedSealReadChain report released required report.listing.afterClose captured.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ captured.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (laterValid : retry.image.later.Beyond layout.range.through)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error ReadState ByteArray)
    {keeperCache : CensusDirectoryCache} {keeperCensus : DescriptorInventory}
    (keeperRead : readKeeper (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      report.wal.keeper.calls.metadata.byteSize.toNat (admission.cache, captured.atOpen, admission.held) =
      .ok layout.keeper.bytes (keeperCache, keeperCensus, admission.held)) :
    ∃ opened,
      report.prepareFromCensus metadataRelease runs.released released readKeeper
        (admission.cache, admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (keeperCache, keeperCensus, admission.held) ∧
      report.walReads.prepare report.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) := by
  obtain ⟨_, _, _, length, decoded, count, entered⟩ := report.beforeKeeper manifest runs selected marker chronology
    captured seals offsets retained following (laterValid _ List.mem_cons_self) readKeeper
  have through : length.toNat / WAL.frameSize = layout.range.through := by
    rw [count, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have size : layout.keeper.bytes.size = (length.toNat / WAL.frameSize - layout.keeper.first) * WAL.frameSize :=
    through.symm ▸ layout.target.trimmedSize
  have extent : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    report.wal.keeper.observesFile.extent
  have covers : layout.keeper.bytes.size ≤ report.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [extent]
    change layout.keeper.bytes.size ≤ (layout.keeper.bytes ++ layout.tail).size
    rw [ByteArray.size_append]
    exact Nat.le_add_right ..
  have keeperReturned := readCachedWalPayloads_keeperSuccess directory (length.toNat / WAL.frameSize)
    (readTemporarySeal report.reads released) readKeeper size covers keeperRead
  let readWal (_ : Nat) (_ : UInt64) : EStateM IO.Error ReadState (WalSegmentMarkerReads × Nat) := do
    let (last, extent) ← readCachedWalPayloads directory (length.toNat / WAL.frameSize)
      (readTemporarySeal report.reads released) readKeeper [(layout.keeper.first, report.wal.keeper.calls.metadata)]
    pure (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++ last, retry.image.later.visible⟩, extent)
  have observed : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat length
      (admission.cache, captured.atOpen, admission.held) =
      .ok (⟨layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
        [(layout.keeper.first, layout.keeper.bytes)], retry.image.later.visible⟩,
        report.wal.keeper.calls.metadata.byteSize.toNat) (keeperCache, keeperCensus, admission.held) := by
    simp only [readWal, Bind.bind, EStateM.bind, keeperReturned, Pure.pure, EStateM.pure]
  obtain ⟨opened, returned, projected, _⟩ :=
    report.preparesFromSelectedWal selected marker.bound decoded following laterValid accepted ordered readWal observed
  exact ⟨opened, entered.trans returned, projected⟩

/-- Chronological reports from admitted checkpoint metadata to the
exact keeper entry, shared by the aligned and longer-keeper branches. -/
structure CapturedMarkedReadCensus
    {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
    {retry : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
    {admission : CensusOpenAdmissionReports input directory inventory retry}
    (reads : CapturedMarkedReadReports admission layout published) (keeper : CapturedKeeperOpenReports reads) where
  metadataRelease : FilePath → List LockReferenceDrop
  manifestDrops : List LockReferenceDrop
  manifest : CapturedManifestCensus reads metadataRelease manifestDrops
  runs : CapturedRunReadCensus reads (admission.reached.afterDrops manifestDrops)
  marker : CapturedMarkerCensus reads ((admission.reached.afterDrops manifestDrops).afterDrops
    (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease
  beforeListing : reads.listing.beforeOpen = manifestDrops ++
    runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
    (marker.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary))
  sealRelease : FilePath → List LockReferenceDrop
  required : List (Nat × IO.FS.Metadata)
  seals : CapturedSealReadChain reads sealRelease required reads.listing.afterClose keeper.beforeOpen
  offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first
  retained : ∀ event ∈ keeper.beforeOpen,
    event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false

end Alvoki.Storage.DiskSession
