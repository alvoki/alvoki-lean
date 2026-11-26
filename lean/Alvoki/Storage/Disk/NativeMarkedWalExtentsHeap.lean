import Alvoki.Storage.Disk.NativeMarkedCheckpointHeap
import Alvoki.Storage.Disk.NativeWalSelectionReturn

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The observations at the checked directory primitive use the opaque
returned stream until closedir. The read report includes terminal errno. -/
structure MarkedDirectoryReadCalls (heap stream : Type) where
  openDir : FilePath → EStateM IO.Error heap stream
  readDir : stream → heap → (List String × Except IO.Error Unit) × heap
  closeDir : stream → EStateM IO.Error heap Unit

/-- Interpret the native checked directory result from its observed
stream callbacks, keeping the heap returned by closedir. -/
def MarkedDirectoryReadCalls.run (calls : MarkedDirectoryReadCalls heap stream) (path : FilePath) :
    EStateM IO.Error heap (Array IO.FS.DirEntry) := fun before =>
  match calls.openDir path before with
  | .error cause reached => .error cause reached
  | .ok opened entry =>
    let ((names, terminal), scanned) := calls.readDir opened entry
    let (closed, reached) := match calls.closeDir opened scanned with
      | .ok () reached => (.ok (), reached)
      | .error cause reached => (.error cause, reached)
    (liftExcept ((CheckedDirectoryReadReport.scanned ⟨names, terminal, closed⟩).result path) :
      EStateM IO.Error heap _) reached

/-- Invert the successful checked directory callback without a read plan.
The same stream supplies the names, clean EOF and successful close. -/
theorem MarkedDirectoryReadCalls.returnedScan {heap stream : Type}
    (calls : MarkedDirectoryReadCalls heap stream) (path : FilePath)
    {before reached : heap} {entries : Array IO.FS.DirEntry}
    (returned : calls.run path before = .ok entries reached) :
    ∃ (descriptor : stream) (opened scanned : heap) (names : List String),
      calls.openDir path before = .ok descriptor opened ∧
      calls.readDir descriptor opened = ((names, .ok ()), scanned) ∧
      calls.closeDir descriptor scanned = .ok () reached ∧
      entries = (⟨names, .ok (), .ok ()⟩ : OpenedDirectoryScan).entries path := by
  cases opened : calls.openDir path before with
  | error cause after =>
    simp [MarkedDirectoryReadCalls.run, opened] at returned
  | ok descriptor openHeap =>
    cases scanned : calls.readDir descriptor openHeap with
    | mk readReport scanHeap =>
      cases readReport with
      | mk names terminal =>
        cases terminal with
        | error cause =>
          cases closed : calls.closeDir descriptor scanHeap <;>
            simp [MarkedDirectoryReadCalls.run, opened, scanned, closed,
              CheckedDirectoryReadReport.result, Bind.bind, Except.bind, liftExcept,
              throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
        | ok value =>
          cases value
          cases closed : calls.closeDir descriptor scanHeap with
          | error cause after =>
            simp [MarkedDirectoryReadCalls.run, opened, scanned, closed,
              CheckedDirectoryReadReport.result, Bind.bind, Except.bind, liftExcept,
              throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
          | ok value after =>
            cases value
            simp [MarkedDirectoryReadCalls.run, opened, scanned, closed, CheckedDirectoryReadReport.result,
              Bind.bind, Except.bind, Pure.pure, Except.pure, liftExcept] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨descriptor, openHeap, scanHeap, names, rfl, scanned, closed, rfl⟩

/-- A checked listing is complete for the held root only if the actual
stream saw that root and its clean EOF report is complete. -/
theorem MarkedDirectoryReadCalls.listedRootNames {heap stream : Type}
    (calls : MarkedDirectoryReadCalls heap stream) (path : FilePath)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (streamObject : heap → stream → DeviceInode)
    {before reached : heap} {entries : Array IO.FS.DirEntry}
    (returned : calls.run path before = .ok entries reached)
    (sameRoot : ∀ descriptor opened, calls.openDir path before = .ok descriptor opened →
      streamObject opened descriptor = root)
    (complete : ∀ descriptor opened scanned names,
      calls.openDir path before = .ok descriptor opened →
      calls.readDir descriptor opened = ((names, .ok ()), scanned) →
      calls.closeDir descriptor scanned = .ok () reached →
      (⟨names, .ok (), .ok ()⟩ : OpenedDirectoryScan).visibleNames.Perm
        (namespaceView.names (streamObject opened descriptor))) :
    (entries.toList.map (·.fileName)).Perm (namespaceView.names root) := by
  obtain ⟨descriptor, opened, scanned, names, openCall, readCall, closeCall, rfl⟩ := calls.returnedScan path returned
  have truthful := complete descriptor opened scanned names openCall readCall closeCall
  rw [sameRoot descriptor opened openCall] at truthful
  exact (CheckedDirectoryReadReport.scan_complete path rfl rfl truthful).2

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}

/-- The reached checked scan opens and closes the actual reported stream
in the original held directory. Its closed heap is the inventory entry
for subsequent no-follow probes. -/
structure MarkedDirectoryReadReport (prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls)
    (calls : MarkedDirectoryReadCalls heap stream) (slotOf : heap → stream → DescriptorSlot) where
  descriptor : stream
  opened : heap
  scanned : heap
  reached : heap
  openedRaw : calls.openDir directory.path prepared.atScan = .ok descriptor opened
  openedSlot : slotOf opened descriptor = reads.listing.stream
  openedCensus : view.descriptors opened = reads.listing.opened
  readRaw : calls.readDir descriptor opened = ((reads.listing.scan.names, reads.listing.scan.terminal), scanned)
  closedSlot : slotOf scanned descriptor = slotOf opened descriptor
  scanCensus : view.descriptors scanned = reads.listing.opened.afterDrops reads.listing.duringScan
  closedRaw : calls.closeDir descriptor scanned = .ok () reached
  closedCensus : view.descriptors reached = (view.descriptors scanned).afterDrops [reads.listing.stream.closeEvent]
  openFrame : MarkedReadCacheFrame seed prepared.atScan opened
  readFrame : MarkedReadCacheFrame seed opened scanned
  closeFrame : MarkedReadCacheFrame seed scanned reached

/-- The checked directory primitive returns the exact complete listing
from the same stream it closed. The reached census is the one after
that particular stream's release. -/
theorem MarkedDirectoryReadReport.returns {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
    {slotOf : heap → stream → DescriptorSlot} (seen : MarkedDirectoryReadReport prepared directoryCalls slotOf) :
    directoryCalls.run directory.path prepared.atScan = .ok (reads.listing.scan.entries directory.path) seen.reached ∧
    view.descriptors seen.reached = reads.listing.afterClose ∧
    slotOf seen.scanned seen.descriptor = reads.listing.stream ∧
    (view.descriptors seen.reached).references reads.listing.stream.description = [] ∧
    MarkedReadCacheFrame seed prepared.atScan seen.reached := by
  have after : view.descriptors seen.reached = reads.listing.afterClose := by
    rw [seen.closedCensus, seen.scanCensus]
    rfl
  refine ⟨?_, after, seen.closedSlot.trans seen.openedSlot, after.symm ▸ reads.listing.custody.streamClosed,
    ⟨seen.closeFrame.directoryCell.trans (seen.readFrame.directoryCell.trans seen.openFrame.directoryCell),
      seen.closeFrame.activeCell.trans (seen.readFrame.activeCell.trans seen.openFrame.activeCell),
      seen.closeFrame.pendingCell.trans (seen.readFrame.pendingCell.trans seen.openFrame.pendingCell),
      seen.closeFrame.directoryHandle.trans (seen.readFrame.directoryHandle.trans seen.openFrame.directoryHandle),
      seen.closeFrame.files.trans (seen.readFrame.files.trans seen.openFrame.files)⟩⟩
  simp only [MarkedDirectoryReadCalls.run, seen.openedRaw, seen.readRaw, seen.closedRaw]
  have scan : (⟨reads.listing.scan.names, reads.listing.scan.terminal, .ok ()⟩ : OpenedDirectoryScan) = reads.listing.scan := by
    rw [reads.listing.closed.symm]
  rw [scan, (CheckedDirectoryReadReport.scan_complete directory.path reads.listing.eof reads.listing.closed
    reads.listing.complete).1]
  rfl

/-- The actual inventory lookup reads only parsed WAL names from the
reached checked listing, and returns the same no-follow reports used by
the physical catalog. These probes preserve the reached heap. -/
structure MarkedWalExtentReports (prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls)
    {slotOf : heap → stream → DescriptorSlot} (listing : MarkedDirectoryReadReport prepared directoryCalls slotOf) where
  stat : ∀ name ∈ (reads.listing.scan.entries directory.path).toList.map (·.fileName),
    ∀ first, parseWalSegmentName name = some first →
      let path := directory.file (.walSegment first)
      fileCalls.stat path listing.reached = .ok (reads.catalog.inventory.reports.lstat path) listing.reached

namespace MarkedWalExtentReports

variable {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls} {slotOf : heap → stream → DescriptorSlot}
  {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}

def inspect (fileCalls : MarkedTemporaryReadCalls heap) (path : FilePath) :
    EStateM IO.Error heap (Except IO.Error IO.FS.Metadata) :=
  inspectWalSegmentWith path (fileCalls.stat path)

private theorem scan (seen : MarkedWalExtentReports prepared listing)
    {extents : List (Nat × IO.FS.Metadata)}
    (reported : readWalSegmentExtentsWith directory (fun path => .ok (reads.catalog.inventory.reports.lstat path) :
      FilePath → Except IO.Error _) ((reads.listing.scan.entries directory.path).toList.map (·.fileName)) = .ok extents) :
    readWalSegmentExtentsWith directory (inspect fileCalls)
      ((reads.listing.scan.entries directory.path).toList.map (·.fileName)) listing.reached =
        .ok extents listing.reached := by
  let expected : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata) :=
    fun path => .ok (reads.catalog.inventory.reports.lstat path)
  let seenNames := (reads.listing.scan.entries directory.path).toList.map (·.fileName)
  have checked := (CheckedDirectoryReadReport.scan_complete directory.path reads.listing.eof reads.listing.closed
    reads.listing.complete).1
  have entries := Except.ok.inj (reads.catalog.listed.symm.trans (reads.listed.trans checked))
  have catalogNames : seenNames = reads.catalog.inventory.names := by
    change (reads.listing.scan.entries directory.path).toList.map (·.fileName) = _
    rw [← entries]
    exact reads.catalog.names
  have extent (name : String) (member : name ∈ seenNames) :
      readWalSegmentExtentWith directory (inspect fileCalls) name listing.reached =
        (liftExcept (readWalSegmentExtentWith directory expected name) : EStateM IO.Error heap _) listing.reached := by
    cases parsed : parseWalSegmentName name with
    | none => simp [readWalSegmentExtentWith, parsed, liftExcept, Pure.pure, EStateM.pure, Except.pure]
    | some first =>
      have rendering := parseWalSegmentName_eq_some_iff.mp parsed
      have found := (reads.catalog.present first).mp (rendering ▸ catalogNames ▸ member)
      obtain ⟨metadata, lookedUp, regular, privateFile⟩ := reads.catalog.regular first found
      have raw := seen.stat name member first parsed
      have observed : inspect fileCalls (directory.file (.walSegment first)) listing.reached =
          .ok (.ok metadata) listing.reached := by
        simp [inspect, inspectWalSegmentWith, checkPrivateRegularWith, Bind.bind, EStateM.bind, raw, lookedUp,
          regular, privateFile, show (IO.FS.FileType.file == .file) = true from rfl, Pure.pure, EStateM.pure]
      simp only [readWalSegmentExtentWith, parsed, Bind.bind, EStateM.bind, observed, expected, lookedUp,
        Except.bind, Pure.pure]
      cases classifyWalSegmentLookup (directory.file (.walSegment first)) first (.ok metadata) with
      | error cause => rfl
      | ok value => cases value <;> rfl
  have loop (names : List String) (listed : ∀ name ∈ names, name ∈ seenNames) :
      (names.filterMapM (readWalSegmentExtentWith directory (inspect fileCalls))) listing.reached =
        (liftExcept (names.filterMapM (readWalSegmentExtentWith directory expected)) : EStateM IO.Error heap _) listing.reached := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
      have head := extent name (listed name List.mem_cons_self)
      have tail := ih (fun later included => listed later (List.mem_cons_of_mem _ included))
      rw [List.filterMapM_cons, List.filterMapM_cons]
      cases first : readWalSegmentExtentWith directory expected name with
      | error cause =>
        simp only [first, liftExcept] at head
        simp [head, Bind.bind, EStateM.bind, Except.bind, liftExcept, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw]
      | ok found =>
        simp only [first, liftExcept] at head
        cases found with
        | none => simpa [Bind.bind, EStateM.bind, Except.bind, head, Pure.pure, EStateM.pure] using tail
        | some value =>
          cases reportedTail : rest.filterMapM (readWalSegmentExtentWith directory expected) <;>
            simp [Bind.bind, EStateM.bind, Except.bind, liftExcept, head, tail, reportedTail, Pure.pure, EStateM.pure,
              Except.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  have raw := loop seenNames (fun _ member => member)
  change (seenNames.filterMapM (readWalSegmentExtentWith directory expected) >>= fun values =>
    pure (values.mergeSort (fun left right => left.1 ≤ right.1))) = Except.ok extents at reported
  change ((seenNames.filterMapM (readWalSegmentExtentWith directory (inspect fileCalls))) >>= fun values =>
    pure (values.mergeSort (fun left right => left.1 ≤ right.1))) listing.reached = .ok extents listing.reached
  cases collected : seenNames.filterMapM (readWalSegmentExtentWith directory expected) with
  | error cause => simp [collected, Bind.bind, Except.bind] at reported
  | ok values =>
    simp only [collected, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at reported
    simp [Bind.bind, EStateM.bind, raw, collected, liftExcept, reported, Pure.pure, EStateM.pure]

/-- The actual listing and extent checks hand the exact retained extents
to the selected payload loop. The seal and keeper callbacks are still
passed through unchanged at the heap reached by the scoped scan. -/
theorem selects (seen : MarkedWalExtentReports prepared listing)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ retry.image.later.visible, layout.range.through < start)
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) :
    let watermark := (checkpoint.getD (.empty, 0)).1.committed.toNat
    ∃ (length : UInt64) (extents : List (Nat × IO.FS.Metadata)),
      WAL.Boundary.decode chronology.marker.bytes = .ok length ∧
      length.toNat = layout.range.through * WAL.frameSize ∧
      view.descriptors prepared.atScan = admission.reached.afterDrops reads.listing.beforeOpen ∧
      (view.descriptors listing.opened).inode reads.listing.stream.description = admission.reached.inode admission.cached.description ∧
      view.descriptors listing.reached = reads.listing.afterClose ∧
      (view.descriptors listing.reached).references reads.listing.stream.description = [] ∧
      view.cacheAt listing.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      view.files listing.reached = admission.held ∧
      directoryCalls.run directory.path prepared.atScan = .ok (reads.listing.scan.entries directory.path) listing.reached ∧
      readWalSegmentExtentsWith directory (inspect fileCalls)
          ((reads.listing.scan.entries directory.path).toList.map (·.fileName)) listing.reached = .ok extents listing.reached ∧
      selectWalExtentsThrough extents watermark (length.toNat / WAL.frameSize) =
        some (chronology.required, retry.image.later.visible) ∧
      readSelectedWithCachedExtents directory watermark length directoryCalls.run (inspect fileCalls) readSeal readKeeper
          prepared.atScan =
        (do
          let (files, fileSize) ← readCachedWalPayloads directory (length.toNat / WAL.frameSize) readSeal readKeeper
            chronology.required
          pure (⟨files, retry.image.later.visible⟩, fileSize) : EStateM IO.Error heap (WalSegmentMarkerReads × Nat)) listing.reached := by
  intro watermark
  let walRead := fun watermark length =>
    readSelectedWithCachedExtents directory watermark length directoryCalls.run (inspect fileCalls) readSeal readKeeper
  obtain ⟨_, _, _, scanEntry, startFrame, openedCache, heldFiles, _⟩ := prepared.reachesScan selected walRead
  obtain ⟨listed, closedCensus, _, streamClosed, frame⟩ := listing.returns
  obtain ⟨watermarked, covered, markerBytes, length, bound, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have exactMarker := Option.some.inj (bound.symm.trans chronology.marker.bound)
  rw [exactMarker] at decoded
  have exactWatermark : watermark = layout.range.watermark := Option.some.inj (selected.watermark.symm.trans watermarked)
  obtain ⟨extents, chosen, scanned, selection, offsets, _⟩ := reads.catalog.scanSelected following later absolute
  have complete := (CheckedDirectoryReadReport.scan_complete directory.path reads.listing.eof reads.listing.closed
    reads.listing.complete).1
  have entries := Except.ok.inj (reads.catalog.listed.symm.trans (reads.listed.trans complete))
  rw [entries] at scanned
  have submitted := seen.scan scanned
  have sameExtents := chronology.seals.matchesExtents (chronology.offsets.trans offsets.symm)
    (fun extent member => OpenPathReadReports.walSegmentExtents_metadata scanned (selectWalExtentsThrough_required_subset selection member))
  rw [← sameExtents, ← exactWatermark] at selection
  have aligned : length.toNat % WAL.frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have through : length.toNat / WAL.frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have covers : watermark ≤ length.toNat / WAL.frameSize := by rwa [exactWatermark, through]
  have cache : view.cacheAt listing.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
    obtain ⟨_, _, _, _, _, _, _, _, installedDirectory, installedActive, installedPending, _, _⟩ := seed.installs
    have atScan := startFrame.directoryCell.trans installedDirectory
    have noActive := startFrame.activeCell.trans installedActive
    have noPending := startFrame.pendingCell.trans installedPending
    rw [← openedCache]
    simp only [OpenCloseHeapView.cacheAt, frame.directoryCell, frame.activeCell, frame.pendingCell, atScan,
      noActive, noPending, Option.map_none, List.map_nil, Option.map_some, frame.directoryHandle]
  refine ⟨length, extents, decoded, absolute, scanEntry, ?_, closedCensus, streamClosed, cache, frame.files.trans heldFiles,
    listed, submitted, selection, ?_⟩
  · rw [listing.openedCensus]
    exact reads.listing.sameDirectoryObject
  · simp only [readSelectedWithCachedExtents, aligned, covers, and_self, ↓reduceIte, Bind.bind, EStateM.bind,
      listed, submitted, selection]

end MarkedWalExtentReports

private theorem inspectReturnedGuard {heap : Type}
    (fileCalls : MarkedTemporaryReadCalls heap) (path : FilePath)
    {before reached : heap} {report : Except IO.Error IO.FS.Metadata}
    (returned : MarkedWalExtentReports.inspect fileCalls path before = .ok report reached) :
    fileCalls.stat path before = .ok report reached ∧
      ∀ metadata, report = .ok metadata → metadata.numLinks = 1 := by
  change inspectWalSegmentWith path (fileCalls.stat path) before = _ at returned
  unfold inspectWalSegmentWith at returned
  cases stat : fileCalls.stat path before with
  | error cause after => simp [Bind.bind, EStateM.bind, stat] at returned
  | ok called after =>
    cases called with
    | error cause =>
      simp only [Bind.bind, EStateM.bind, stat, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      exact ⟨rfl, fun _ equality => by cases equality⟩
    | ok metadata =>
      cases checked : (metadata.type == .file && metadata.numLinks == 1) <;>
        simp [Bind.bind, EStateM.bind, stat, checkPrivateRegularWith, checked, Pure.pure, EStateM.pure,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      obtain ⟨rfl, rfl⟩ := returned
      have oneLink : metadata.numLinks = 1 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at checked
        exact checked.2
      exact ⟨rfl, fun _ equality => (Except.ok.inj equality) ▸ oneLink⟩

/-- The guarded inventory callback returns the exact no-follow report.
An ENOENT can come only from that actual stat. -/
theorem MarkedWalExtentReports.inspectReturned {heap : Type}
    (fileCalls : MarkedTemporaryReadCalls heap) (path : FilePath)
    {before reached : heap} {report : Except IO.Error IO.FS.Metadata}
    (returned : inspect fileCalls path before = .ok report reached) :
    fileCalls.stat path before = .ok report reached :=
  (inspectReturnedGuard fileCalls path returned).1

/-- Each required seal or keeper keeps the absolute extent reported by
its actual no-follow stat. Before the stat, the worker has processed
exactly the earlier names in the original stream order. -/
theorem MarkedWalExtentReports.selectedStat {heap : Type}
    (fileCalls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (names : List String) {listed scanned : heap}
    {extents required : List (Nat × IO.FS.Metadata)} {watermark through first : Nat}
    {later : List Nat} {metadata : IO.FS.Metadata}
    (scan : readWalSegmentExtentsWith directory (inspect fileCalls) names listed = .ok extents scanned)
    (selected : selectWalExtentsThrough extents watermark through = some (required, later))
    (member : (first, metadata) ∈ required) :
    ∃ earlier rest collected issued after,
      names = earlier ++ renderWalSegmentName first :: rest ∧
      (earlier.filterMapM (readWalSegmentExtentWith directory (inspect fileCalls))) listed = .ok collected issued ∧
      inspect fileCalls (directory.file (.walSegment first)) issued = .ok (.ok metadata) after ∧
      fileCalls.stat (directory.file (.walSegment first)) issued = .ok (.ok metadata) after ∧
      metadata.numLinks = 1 := by
  obtain ⟨earlier, name, rest, collected, issued, after, order, parsed, steps, guarded⟩ :=
    readWalSegmentExtentsWith_memberStat directory (inspect fileCalls) names scan
      (selectWalExtentsThrough_required_subset selected member)
  rw [parseWalSegmentName_eq_some_iff.mp parsed] at order
  obtain ⟨raw, checked⟩ := inspectReturnedGuard fileCalls _ guarded
  exact ⟨earlier, rest, collected, issued, after, order, steps, guarded, raw, checked metadata rfl⟩

end Alvoki.Storage.DiskSession

namespace Alvoki.Storage

open System WalSegmentRepair
open DiskSession (MarkedDirectoryReadCalls DirectoryReadNamespace DeviceInode
  MarkedTemporaryReadCalls MarkedWalExtentReports)

variable {heap : Type}

private theorem walOffsetsOrdered (values : List Nat) : values.mergeSort.Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun _ _ _ ab bc => decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
    (fun a b => Bool.or_eq_true_iff.mpr ((Nat.le_total a b).imp decide_eq_true decide_eq_true)) values).imp
      (fun bound => of_decide_eq_true bound)

/-- ENOENT at a WAL stat reached from the returned listing witnesses an
absent name in its held directory. The contract is local to this scan. -/
def DiskSession.MarkedWalExtentReports.TruthfulAbsence
    (fileCalls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (names : List String) (listed : heap) : Prop :=
  ∀ {earlier rest : List String} {name : String} {first : Nat},
    names = earlier ++ name :: rest → parseWalSegmentName name = some first →
    ∀ {collected : List (Nat × IO.FS.Metadata)} {issued after filename message},
    (earlier.filterMapM (readWalSegmentExtentWith directory (MarkedWalExtentReports.inspect fileCalls))) listed =
      .ok collected issued →
    fileCalls.stat (directory.file (.walSegment first)) issued =
      .ok (.error (.noFileOrDirectory filename 2 message)) after →
    namespaceView.child root (renderWalSegmentName first) = none

/-- The checked listing supplies every held name, and a reached no-follow
absence must agree with that binding. The actual scan then retains every
canonical WAL address, in order after its sort. -/
theorem DiskSession.MarkedWalExtentReports.exactInventory
    (fileCalls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (names : List String) {listed scanned : heap} {extents : List (Nat × IO.FS.Metadata)}
    (listedNames : names.Perm (namespaceView.names root))
    (scan : readWalSegmentExtentsWith directory (MarkedWalExtentReports.inspect fileCalls) names listed =
      .ok extents scanned)
    (absent : MarkedWalExtentReports.TruthfulAbsence fileCalls directory namespaceView root names listed) :
    extents.map Prod.fst = ((namespaceView.names root).filterMap parseWalSegmentName).mergeSort ∧
      ∀ first, first ∈ extents.map Prod.fst ↔
        ∃ object, namespaceView.child root (renderWalSegmentName first) = some object := by
  have exactOffsets := readWalSegmentExtentsWith_exactOffsets directory (MarkedWalExtentReports.inspect fileCalls) names scan
    (fun {scanned rest name first} order parsed {_ _ _ _ _} entered missing => by
      have inListing : name ∈ names :=
        order.symm ▸ List.mem_append_right scanned List.mem_cons_self
      have seen : renderWalSegmentName first ∈ names :=
        (parseWalSegmentName_eq_some_iff.mp parsed) ▸ inListing
      obtain ⟨object, bound⟩ := (namespaceView.namesExact _ _).mp (listedNames.mem_iff.mp seen)
      have raw := MarkedWalExtentReports.inspectReturned fileCalls _ missing
      exact Option.some_ne_none object (bound.symm.trans (absent order parsed entered raw)))
  have sorted := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => Nat.le_antisymm ab ba)
    (walOffsetsOrdered _) (walOffsetsOrdered _) ((List.mergeSort_perm _ _).trans
      ((listedNames.filterMap parseWalSegmentName).trans (List.mergeSort_perm _ _).symm))
  have inventory : extents.map Prod.fst = ((namespaceView.names root).filterMap parseWalSegmentName).mergeSort :=
    exactOffsets.trans sorted
  have exactNames (first : Nat) : first ∈ extents.map Prod.fst ↔
      ∃ object, namespaceView.child root (renderWalSegmentName first) = some object := by
    rw [inventory, List.mem_mergeSort, List.mem_filterMap, ← namespaceView.namesExact]
    exact ⟨fun ⟨name, listed, parsed⟩ => (parseWalSegmentName_eq_some_iff.mp parsed) ▸ listed,
      fun listed => ⟨_, listed, parseWalSegmentName_render first⟩⟩
  exact ⟨inventory, exactNames⟩

/-- A completed WAL scan determines the successful selector from the
held window. Only canonical names in that window need agree with the
replay layout. Every actual binding beyond the marker enters the later
set independently of the replay layout. -/
theorem DiskSession.MarkedWalExtentReports.selectsWindow
    (fileCalls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (names : List String) {listed scanned : heap} {extents : List (Nat × IO.FS.Metadata)}
    (listedNames : names.Perm (namespaceView.names root))
    (scan : readWalSegmentExtentsWith directory (MarkedWalExtentReports.inspect fileCalls) names listed =
      .ok extents scanned)
    (absent : MarkedWalExtentReports.TruthfulAbsence fileCalls directory namespaceView root names listed)
    {first watermark through : Nat} {expected later : List Nat} {required : List (Nat × IO.FS.Metadata)}
    (selected : selectWalExtentsThrough extents watermark through = some (required, later))
    (strict : (required.map Prod.fst).Pairwise (· < ·))
    (canonical : (first :: expected).Pairwise (· < ·))
    (covers : first ≤ watermark) (bounded : watermark ≤ through)
    (within : ∀ start ∈ expected, watermark < start ∧ start ≤ through)
    (catalog : ∀ start, first ≤ start → start ≤ through →
      ((∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ↔ start ∈ first :: expected)) :
    required.map Prod.fst = first :: expected ∧
      (∀ start, start ∈ later ↔ through < start ∧
        ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ∧
      ∀ start ∈ later, start ∈ extents.map Prod.fst := by
  obtain ⟨inventory, exactNames⟩ := exactInventory fileCalls directory namespaceView root names listedNames scan absent
  have ordered := inventory.symm ▸ walOffsetsOrdered ((namespaceView.names root).filterMap parseWalSegmentName)
  obtain ⟨offsets, rfl⟩ := selectWalExtentsThrough_matchesWindow ordered selected strict
    canonical covers bounded within (fun start lower upper => (exactNames start).trans (catalog start lower upper))
  refine ⟨offsets, ?_, fun _ later => (List.mem_filter.mp later).1⟩
  intro start
  rw [List.mem_filter, exactNames start]
  simp only [decide_eq_true_eq, and_comm]

/-- The actual successful selected WAL read consumes an exact inventory.
The scope fixes the stream's held root and makes an ENOENT report
evidence that the no-follow binding is absent, rather than a silent
omission. No healthy keeper layout is an input. -/
theorem SelectedWalReadReturn.successfulExtentInventory
    {stream : Type} {directory : DiskDirectory} {watermark : Nat} {length : UInt64}
    {listing : MarkedDirectoryReadCalls heap stream}
    {fileCalls : MarkedTemporaryReadCalls heap}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    {entry reached : heap} {reads : WalSegmentMarkerReads} {size : Nat}
    (observed : SelectedWalReadReturn directory watermark length listing.run
      (MarkedWalExtentReports.inspect fileCalls) readSeal readKeeper entry
      (.ok (reads, size) reached))
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (streamObject : heap → stream → DeviceInode)
    (sameRoot : ∀ descriptor opened, listing.openDir directory.path entry = .ok descriptor opened →
      streamObject opened descriptor = root)
    (complete : ∀ descriptor opened scanned closed names,
      listing.openDir directory.path entry = .ok descriptor opened →
      listing.readDir descriptor opened = ((names, .ok ()), scanned) →
      listing.closeDir descriptor scanned = .ok () closed →
      (⟨names, .ok (), .ok ()⟩ : OpenedDirectoryScan).visibleNames.Perm
        (namespaceView.names (streamObject opened descriptor)))
    (absent : ∀ {entries : Array IO.FS.DirEntry} {listed : heap},
      listing.run directory.path entry = .ok entries listed →
      MarkedWalExtentReports.TruthfulAbsence fileCalls directory namespaceView root
        (entries.toList.map (·.fileName)) listed) :
    ∃ (entries : Array IO.FS.DirEntry) (listed scanned : heap) (extents required : List (Nat × IO.FS.Metadata)),
      listing.run directory.path entry = .ok entries listed ∧
      (entries.toList.map (·.fileName)).Perm (namespaceView.names root) ∧
      readWalSegmentExtentsWith directory (MarkedWalExtentReports.inspect fileCalls) (entries.toList.map (·.fileName)) listed = .ok extents scanned ∧
      (extents.map Prod.fst) = ((namespaceView.names root).filterMap parseWalSegmentName).mergeSort ∧
      (∀ first, first ∈ extents.map Prod.fst ↔
        ∃ object, namespaceView.child root (renderWalSegmentName first) = some object) ∧
      selectWalExtentsThrough extents watermark (length.toNat / WAL.frameSize) = some (required, reads.newer) ∧
      (∀ first, first ∈ reads.newer ↔ length.toNat / WAL.frameSize < first ∧
        ∃ object, namespaceView.child root (renderWalSegmentName first) = some object) ∧
      readCachedWalPayloads directory (length.toNat / WAL.frameSize) readSeal readKeeper required scanned =
        .ok (reads.files, size) reached := by
  obtain ⟨entries, listed, extents, scanned, required, checked, listedCall, scan, select, payload, _⟩ :=
    observed.successfulPayloads
  have names := listing.listedRootNames directory.path namespaceView root streamObject listedCall sameRoot
    (fun _ _ _ _ opened read closed => complete _ _ _ _ _ opened read closed)
  obtain ⟨inventory, exactNames⟩ := MarkedWalExtentReports.exactInventory fileCalls directory namespaceView root
    (entries.toList.map (·.fileName)) names scan (absent listedCall)
  have selectedOffsets := selectWalExtentsThrough_offsets extents watermark (length.toNat / WAL.frameSize)
  rw [select, Option.map_some] at selectedOffsets
  have later := selectWalSegmentReadsThrough_later selectedOffsets.symm checked.2 (inventory.symm ▸ walOffsetsOrdered _)
  dsimp only at later
  refine ⟨entries, listed, scanned, extents, required, listedCall, names, scan, inventory, exactNames, select, ?_, payload⟩
  intro first
  rw [later, List.mem_filter, exactNames first]
  simp only [decide_eq_true_eq, and_comm]

end Alvoki.Storage
