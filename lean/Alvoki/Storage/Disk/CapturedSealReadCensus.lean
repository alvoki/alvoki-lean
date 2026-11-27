import Alvoki.Storage.Disk.Proofs.Keeper.CapturedKeeperCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev ReadState := CensusDirectoryCache × CensusOpenState

/-- A temporary opened description is inserted into the reached census.
The observed finalizer releases its slot after the read. This projection
accounts for intervening drops and assumes no alias of the temporary slot
is created. -/
structure TemporaryPrefixCustody {reads : CheckpointRunChunkReads} {path : FilePath} {name : String}
    {root : DeviceInode} {view : DirectoryReadNamespace}
    (opened : RunChunkPathReport reads path name root view) (initial : DescriptorInventory)
    (released : List LockReferenceDrop) where
  beforeOpen : List LockReferenceDrop
  free : ∀ slot ∈ (initial.afterDrops beforeOpen).slots, slot.address ≠ opened.slot.address
  fresh : (initial.afterDrops beforeOpen).references opened.slot.description = []
  allocated : opened.inventory = (initial.afterDrops beforeOpen).insert opened.slot free
  beforeClose : List LockReferenceDrop
  closing : released = beforeClose ++ [opened.slot.closeEvent]
  keptWhileReading : ∀ event ∈ beforeClose, event.removes opened.slot.reference = false

/-- Interpret a native exact-prefix callback on the observed handle.
The successful projection carries the slot drops reported before the next
open can be issued. -/
def readTemporaryPrefix (reads : CheckpointRunChunkReads) (mismatch : IO.Error)
    (released : FilePath → List LockReferenceDrop)
    (path : FilePath) (count : Nat) : EStateM IO.Error ReadState ByteArray := fun (cache, census, files) =>
  match reads.openRead path with
  | .error cause => .error cause (cache, census, files)
  | .ok handle =>
    match reads.readOpenedPrefix mismatch handle count with
    | .error cause => .error cause (cache, handle.1, files)
    | .ok bytes => .ok bytes (cache, handle.1.afterDrops (released path), files)

abbrev readTemporarySeal (reads : CheckpointRunChunkReads) := readTemporaryPrefix reads selectedWalSpanError

namespace TemporaryPrefixCustody

variable {reads : CheckpointRunChunkReads} {path : FilePath} {name : String} {root : DeviceInode}
  {view : DirectoryReadNamespace} {opened : RunChunkPathReport reads path name root view}
  {initial : DescriptorInventory} {released : FilePath → List LockReferenceDrop}

/-- The temporary slot is live at every reported read, including after
any prefix of the observed drops before its finalizer. -/
theorem liveAtRead (custody : TemporaryPrefixCustody opened initial (released path))
    {earlier remaining : List LockReferenceDrop} (ordered : custody.beforeClose = earlier ++ remaining) :
    opened.slot ∈ (opened.inventory.afterDrops earlier).slots := by
  refine List.mem_filter.mpr ⟨opened.live, List.all_eq_true.mpr fun event member => ?_⟩
  have observed : event ∈ custody.beforeClose := ordered ▸ List.mem_append_left _ member
  rw [custody.keptWhileReading event observed]
  rfl

/-- Allocate and release the actual opened slot. The reached census is
the original census with precisely the observed drops applied. -/
theorem closes (custody : TemporaryPrefixCustody opened initial (released path)) :
    opened.inventory.afterDrops (released path) = initial.afterDrops (custody.beforeOpen ++ released path) ∧
    (opened.inventory.afterDrops (released path)).references opened.slot.description = [] := by
  have reduced : opened.inventory.afterDrops (released path) = initial.afterDrops (custody.beforeOpen ++ released path) := by
    let before := initial.afterDrops custody.beforeOpen
    let installed := before.insert opened.slot custody.free
    calc
      opened.inventory.afterDrops (released path) = installed.afterDrops (released path) :=
        congrArg (fun census => census.afterDrops (released path)) custody.allocated
      _ = installed.afterDrops (custody.beforeClose ++ [opened.slot.closeEvent]) :=
        congrArg installed.afterDrops custody.closing
      _ = before.afterDrops (custody.beforeClose ++ [opened.slot.closeEvent]) :=
        DescriptorInventory.insert_thenClose before opened.slot custody.free custody.beforeClose
      _ = before.afterDrops (released path) := congrArg before.afterDrops custody.closing.symm
      _ = _ := DescriptorInventory.afterDrops_append _ _ _
  refine ⟨reduced, ?_⟩
  rw [reduced, ← DescriptorInventory.afterDrops_append, DescriptorInventory.references_afterDrops, custody.fresh]
  rfl

/-- The held stat and actual chunk callback produce the complete file
bytes. The reached file image and cache are unchanged and the descriptor
census records the exact temporary lifetime. -/
theorem readPrefix (custody : TemporaryPrefixCustody opened initial (released path)) (mismatch : IO.Error)
    {object : DeviceInode} {bytes : ByteArray} (bound : view.child root name = some object)
    (contents : reads.objectBytes (view.modelObject object) = some bytes) (fits : bytes.size < USize.size)
    (cache : CensusDirectoryCache) (files : LockedFileState FileImage) :
    readTemporaryPrefix reads mismatch released path bytes.size (cache, initial, files) =
      .ok bytes (cache, initial.afterDrops (custody.beforeOpen ++ released path), files) := by
  let observed := opened.observesFile bound contents
  have exact := observed.readOpenedExactPrefix mismatch bytes.size fits (Nat.le_refl _)
  change reads.readOpenedPrefix mismatch (opened.inventory, opened.slot, 0) bytes.size =
      .ok (bytes.extract 0 bytes.size) at exact
  have read : reads.readOpenedPrefix mismatch (opened.inventory, opened.slot, 0) bytes.size = .ok bytes := by
    simpa only [ByteArray.extract_zero_size] using exact
  simp only [readTemporaryPrefix, opened.opened, read, custody.closes.1]

theorem readSeal (custody : TemporaryPrefixCustody opened initial (released path))
    {object : DeviceInode} {bytes : ByteArray} (bound : view.child root name = some object)
    (contents : reads.objectBytes (view.modelObject object) = some bytes) (fits : bytes.size < USize.size)
    (cache : CensusDirectoryCache) (files : LockedFileState FileImage) :
    readTemporarySeal reads released path bytes.size (cache, initial, files) =
      .ok bytes (cache, initial.afterDrops (custody.beforeOpen ++ released path), files) :=
  custody.readPrefix selectedWalSpanError bound contents fits cache files

end TemporaryPrefixCustody

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- Read the selected seal extents in their worker order. Each report
starts from the previous temporary reader's reached census. The last
selected extent is the actual keeper from the held stat/open reports. -/
inductive CapturedSealReadChain (report : CapturedMarkedReadReports admission layout published)
    (released : FilePath → List LockReferenceDrop) :
    List (Nat × IO.FS.Metadata) → DescriptorInventory → List LockReferenceDrop → Prop where
  | keeper {initial} : CapturedSealReadChain report released
      [(layout.keeper.first, report.wal.keeper.calls.metadata)] initial []
  | sealed {initial segment next nextMetadata rest drops} (member : segment ∈ layout.sealed)
      (forward : segment.first < next) (size : segment.bytes.size = (next - segment.first) * WAL.frameSize)
      (custody : TemporaryPrefixCustody (report.wal.sealedFile segment member).calls initial
        (released (directory.file (.walSegment segment.first))))
      (remaining : CapturedSealReadChain report released ((next, nextMetadata) :: rest)
        (initial.afterDrops (custody.beforeOpen ++ released (directory.file (.walSegment segment.first)))) drops) :
      CapturedSealReadChain report released ((segment.first, (report.wal.sealedFile segment member).calls.metadata) ::
        (next, nextMetadata) :: rest) initial (custody.beforeOpen ++ released (directory.file (.walSegment segment.first)) ++ drops)

namespace CapturedSealReadChain

variable {report : CapturedMarkedReadReports admission layout published} {released : FilePath → List LockReferenceDrop}
  {required : List (Nat × IO.FS.Metadata)} {initial : DescriptorInventory} {drops : List LockReferenceDrop}

/-- A captured seal or keeper uses exactly the extent probe from the
catalog used by the selected reader. -/
theorem stat (chain : CapturedSealReadChain report released required initial drops) :
    ∀ entry ∈ required,
      report.catalog.inventory.reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2 := by
  induction chain with
  | keeper =>
    intro entry chosen
    obtain rfl := List.mem_singleton.mp chosen
    rw [report.stat, report.wal.keeper.calls.stat]
    rfl
  | @sealed initial segment next nextMetadata rest drops member forward size custody remaining ih =>
    intro entry chosen
    rcases List.mem_cons.mp chosen with rfl | later
    · rw [report.stat, (report.wal.sealedFile segment member).calls.stat]
      rfl
    · exact ih _ later

/-- A successful seal callback for its checked extent returns the bytes
of that exact retained inode. The final keeper has its own callback. -/
theorem sealPayload (chain : CapturedSealReadChain report released required initial drops) :
    ∀ entry ∈ required.dropLast, ∀ {before after bytes},
      readTemporarySeal report.reads released (directory.file (.walSegment entry.1)) entry.2.byteSize.toNat before =
        .ok bytes after → retry.image.kept entry.1 = some bytes := by
  induction chain with
  | keeper => simp
  | @sealed initial segment next nextMetadata rest drops member forward size custody remaining ih =>
    intro entry chosen before after bytes returned
    rw [List.dropLast_cons_cons] at chosen
    rcases List.mem_cons.mp chosen with rfl | tail
    · let file := report.wal.sealedFile segment member
      let seen := file.observesFile
      have exact := seen.readOpenedExactPrefix selectedWalSpanError segment.bytes.size (report.wal.sealFits segment member)
        (Nat.le_refl _)
      rw [ByteArray.extract_zero_size] at exact
      have read : report.reads.readOpenedPrefix selectedWalSpanError (file.calls.inventory, file.calls.slot, 0)
          segment.bytes.size = .ok segment.bytes := exact
      rcases before with ⟨cache, census, files⟩
      change readTemporarySeal report.reads released (directory.file (.walSegment segment.first))
        file.calls.metadata.byteSize.toNat (cache, census, files) = _ at returned
      have extent : file.calls.metadata.byteSize.toNat = segment.bytes.size := seen.extent
      rw [extent] at returned
      simp only [readTemporarySeal, readTemporaryPrefix, file.calls.opened, read] at returned
      exact (EStateM.Result.ok.inj returned).1 ▸ report.wal.kept segment member
    · exact ih entry tail returned

/-- The chronological read reports and the executable extent scan select
the same entries when their ordered offsets agree. Each lookup's own
result fixes the accompanying metadata. -/
theorem matchesExtents (chain : CapturedSealReadChain report released required initial drops)
    {scanned : List (Nat × IO.FS.Metadata)} (offsets : required.map Prod.fst = scanned.map Prod.fst)
    (scannedStat : ∀ entry ∈ scanned,
      report.catalog.inventory.reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2) :
    required = scanned := by
  have known := chain.stat
  clear chain
  induction required generalizing scanned with
  | nil => cases scanned <;> simp_all
  | cons entry rest ih =>
    cases scanned with
    | nil => simp at offsets
    | cons actual more =>
      obtain ⟨address, later⟩ := List.cons.inj offsets
      have first := known entry List.mem_cons_self
      have other := scannedStat actual List.mem_cons_self
      rw [address] at first
      have metadata := Except.ok.inj (first.symm.trans other)
      have same : entry = actual := Prod.ext address metadata
      rw [same, ih later (fun item member => scannedStat item (List.mem_cons_of_mem _ member))
        (fun item member => known item (List.mem_cons_of_mem _ member))]

/-- The actual extent-checked seal loop reaches the keeper in the census
left by the ordered temporary reads. -/
theorem reaches (chain : CapturedSealReadChain report released required initial drops)
    (cache : CensusDirectoryCache) (files : LockedFileState FileImage) :
    CachedWalKeeperReached directory (readTemporarySeal report.reads released) layout.keeper.first
      report.wal.keeper.calls.metadata required (cache, initial, files) (cache, initial.afterDrops drops, files) := by
  induction chain with
  | @keeper current =>
    have same : current.afterDrops [] = current := by
      cases current with
      | mk slots distinct inode =>
        simp only [DescriptorInventory.afterDrops, List.all_nil, List.filter_eq_self.mpr (fun _ _ => rfl)]
    rw [same]
    exact .noSeals
  | @sealed initial segment next nextMetadata rest drops member forward size custody remaining ih =>
    let file := report.wal.sealedFile segment member
    have extent := file.observesFile.extent.trans size
    have fits := size ▸ report.wal.sealFits segment member
    have read := custody.readSeal file.bound file.contents (report.wal.sealFits segment member) cache files
    rw [size] at read
    rw [← DescriptorInventory.afterDrops_append]
    exact .sealed forward extent fits read size ih

end CapturedSealReadChain

namespace CapturedMarkedReadReports

/-- Interpret the successful checked scan at the reached census. The
stream opens, reads and closes in the same captured parent. -/
def scanWal (report : CapturedMarkedReadReports admission layout published) (path : FilePath) :
    EStateM IO.Error ReadState (Array IO.FS.DirEntry) := fun (cache, census, files) =>
  match (CheckedDirectoryReadReport.scanned report.listing.scan).result path with
  | .ok entries => .ok entries (cache, census.afterDrops report.lifetime.drops, files)
  | .error cause => .error cause (cache, census, files)

theorem scanWal_closed (report : CapturedMarkedReadReports admission layout published) :
    report.scanWal directory.path (admission.cache, admission.reached, admission.held) =
      .ok (report.listing.scan.entries directory.path) (admission.cache, report.listing.afterClose, admission.held) := by
  have listing := (CheckedDirectoryReadReport.scan_complete directory.path report.listing.eof report.listing.closed
    report.listing.complete).1
  rw [scanWal, listing, report.listing.afterClose_eq]
  rfl

/-- The same checked stream can start after manifest and marker reads
have already applied the reported drops before opendir. -/
theorem scanWal_fromEntry (report : CapturedMarkedReadReports admission layout published) :
    report.scanWal directory.path
      (admission.cache, admission.reached.afterDrops report.listing.beforeOpen, admission.held) =
        .ok (report.listing.scan.entries directory.path) (admission.cache, report.listing.afterClose, admission.held) := by
  have listing := (CheckedDirectoryReadReport.scan_complete directory.path report.listing.eof report.listing.closed
    report.listing.complete).1
  have stillReached : (admission.reached.afterDrops report.listing.beforeOpen).afterDrops report.lifetime.drops =
      report.listing.afterClose := by
    rw [report.listing.afterClose_eq]
    change (admission.reached.afterDrops report.listing.beforeOpen).afterDrops report.lifetime.drops =
      admission.reached.afterDrops report.lifetime.drops
    have chronology : report.lifetime.drops = report.listing.beforeOpen ++ report.listing.duringScan ++
        [report.listing.stream.closeEvent] := report.listing.drops
    rw [chronology]
    simp [DescriptorInventory.afterDrops, List.filter_filter, List.all_append, Bool.and_comm, Bool.and_left_comm]
  rw [scanWal, listing]
  change EStateM.Result.ok (report.listing.scan.entries directory.path)
    (admission.cache, (admission.reached.afterDrops report.listing.beforeOpen).afterDrops report.lifetime.drops,
      admission.held) = _
  rw [stillReached]

/-- Interpret the native no-follow extent probe and its private regular
file guard. The catalog supplies the raw metadata observation. -/
def inspectWal (report : CapturedMarkedReadReports admission layout published) (path : FilePath) :
    EStateM IO.Error ReadState (Except IO.Error IO.FS.Metadata) :=
  inspectWalSegmentWith path (pure (report.catalog.inventory.reports.lstat path))

/-- Every listed canonical name passes the native inspection, including
older seals and later names whose payloads are not read. The resulting
extent scan is the one used by the catalog selection theorem. -/
theorem guardedWalScan (report : CapturedMarkedReadReports admission layout published) {names : List String}
    (listed : ∀ name ∈ names, name ∈ report.catalog.inventory.names) :
    readWalSegmentExtentsWith directory report.inspectWal names =
      readWalSegmentExtentsWith directory
        (fun path => liftExcept (.ok (report.catalog.inventory.reports.lstat path) : Except IO.Error _)) names := by
  have probes : names.filterMapM (readWalSegmentExtentWith directory report.inspectWal) =
      names.filterMapM (readWalSegmentExtentWith directory
        (fun path => liftExcept (.ok (report.catalog.inventory.reports.lstat path) : Except IO.Error _))) := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
      have tail := ih (fun later member => listed later (List.mem_cons_of_mem _ member))
      have head : readWalSegmentExtentWith directory report.inspectWal name =
          readWalSegmentExtentWith directory
            (fun path => liftExcept (.ok (report.catalog.inventory.reports.lstat path) : Except IO.Error _)) name := by
        cases parsed : parseWalSegmentName name with
        | none => simp [readWalSegmentExtentWith, parsed]
        | some first =>
          have rendering := parseWalSegmentName_eq_some_iff.mp parsed
          have member := (report.catalog.present first).mp (rendering ▸ listed name List.mem_cons_self)
          obtain ⟨metadata, found, regular, privateFile⟩ := report.catalog.regular first member
          have inspected : report.inspectWal (directory.file (.walSegment first)) = pure (.ok metadata) := by
            simp [inspectWal, inspectWalSegmentWith, found, checkPrivateRegularWith, regular, privateFile,
              show (IO.FS.FileType.file == .file) = true from rfl]
          simp [readWalSegmentExtentWith, parsed, inspected, found, liftExcept]
      rw [List.filterMapM_cons, List.filterMapM_cons, head, tail]
  unfold readWalSegmentExtentsWith
  rw [probes]

/-- Use the real selected WAL worker with the observed checked listing and
temporary seal effects. It begins the keeper subloop at the exact census
after the listing has closed and every selected seal read has released its
temporary slot. The keeper still uses the original cache and file image. -/
theorem selectedWalReachesKeeper (report : CapturedMarkedReadReports admission layout published)
    (captured : CapturedKeeperOpenReports report)
    {count : UInt64} (aligned : count.toNat % WAL.frameSize = 0)
    (covers : layout.range.watermark ≤ count.toNat / WAL.frameSize)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith (m := Except IO.Error) directory
      (fun path => .ok (report.catalog.inventory.reports.lstat path))
      ((report.listing.scan.entries directory.path).toList.map (·.fileName)) = .ok extents)
    (selected : selectWalExtentsThrough extents layout.range.watermark (count.toNat / WAL.frameSize) =
      some (required, newer))
    {released : FilePath → List LockReferenceDrop}
    (seals : CapturedSealReadChain report released required report.listing.afterClose captured.beforeOpen)
    (retained : ∀ event ∈ captured.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error ReadState ByteArray) :
    admission.owner ∈ captured.atOpen.slots ∧ admission.cached ∈ captured.atOpen.slots ∧
    ∃ earlier : List (Nat × ByteArray), earlier.map Prod.fst = required.dropLast.map Prod.fst ∧
      (∀ entry ∈ earlier, retry.image.kept entry.1 = some entry.2) ∧
      readSelectedWithCachedExtents directory layout.range.watermark count report.scanWal
        report.inspectWal
        (readTemporarySeal report.reads released) readKeeper
          (admission.cache, admission.reached.afterDrops report.listing.beforeOpen, admission.held) =
      (do
        let (last, size) ← readCachedWalPayloads directory (count.toNat / WAL.frameSize)
          (readTemporarySeal report.reads released) readKeeper [(layout.keeper.first, report.wal.keeper.calls.metadata)]
        pure (⟨earlier ++ last, newer⟩, size) : EStateM IO.Error ReadState (WalSegmentMarkerReads × Nat))
        (admission.cache, captured.atOpen, admission.held) := by
  have lives {slot : DescriptorSlot} (live : slot ∈ report.listing.afterClose.slots)
      (kept : ∀ event ∈ captured.beforeOpen, event.removes slot.reference = false) : slot ∈ captured.atOpen.slots := by
    refine List.mem_filter.mpr ⟨live, List.all_eq_true.mpr fun event member => ?_⟩
    rw [kept event member]
    rfl
  obtain ⟨earlier, offsets, contents, payloads⟩ := (seals.reaches admission.cache admission.held).reachesRead
    (count.toNat / WAL.frameSize) readKeeper
    (selected := fun first bytes => retry.image.kept first = some bytes) seals.sealPayload
  refine ⟨lives report.listing.custody.lockRetained (fun event member => (retained event member).1),
    lives report.listing.custody.cacheRetained (fun event member => (retained event member).2), earlier, offsets, contents, ?_⟩
  have listed := (CheckedDirectoryReadReport.scan_complete directory.path report.listing.eof report.listing.closed
    report.listing.complete).1
  have entries := Except.ok.inj (report.catalog.listed.symm.trans (report.listed.trans listed))
  have names : (report.listing.scan.entries directory.path).toList.map (·.fileName) =
      report.catalog.inventory.names := entries ▸ report.catalog.names
  have scannedState : readWalSegmentExtentsWith directory report.inspectWal
      ((report.listing.scan.entries directory.path).toList.map (·.fileName))
      (admission.cache, report.listing.afterClose, admission.held) =
      .ok extents (admission.cache, report.listing.afterClose, admission.held) := by
    rw [report.guardedWalScan (fun name member => names ▸ member), readWalSegmentExtentsWith_liftReports, scanned]
    rfl
  simp only [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate, aligned, covers, and_self, ↓reduceIte,
    Bind.bind, EStateM.bind, report.scanWal_fromEntry, scannedState, selected, Pure.pure, EStateM.pure]
  rw [payloads]
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, CapturedKeeperOpenReports.atOpen]
  cases readCachedWalPayloads directory (count.toNat / WAL.frameSize) (readTemporarySeal report.reads released)
      readKeeper [(layout.keeper.first, report.wal.keeper.calls.metadata)]
      (admission.cache, report.listing.afterClose.afterDrops captured.beforeOpen, admission.held) with
  | error cause after => rfl
  | ok value after => cases value; rfl

end CapturedMarkedReadReports
end Alvoki.Storage.DiskSession
