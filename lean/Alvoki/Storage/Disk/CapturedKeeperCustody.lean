import Alvoki.Storage.Disk.CapturedMarkedReads

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {renameMarker : Bool} {readStart : DescriptorInventory}

/-- The keeper's observed open follows the closed directory stream in
the tracked descriptor census. Any other temporary reads have finished
and retain no slot in this projection. Drops during the keeper reads
preserve the issuing keeper, lock and cached directory slots. -/
structure CapturedKeeperOpenReports (report : CapturedMarkedReadReports admission layout published renameMarker readStart) where
  beforeOpen : List LockReferenceDrop
  free : ∀ slot ∈ (report.listing.afterClose.afterDrops beforeOpen).slots,
    slot.address ≠ report.wal.keeper.calls.slot.address
  fresh : (report.listing.afterClose.afterDrops beforeOpen).references report.wal.keeper.calls.slot.description = []
  opened : report.wal.keeper.calls.inventory =
    (report.listing.afterClose.afterDrops beforeOpen).insert report.wal.keeper.calls.slot free
  duringRead : List LockReferenceDrop
  keeperRetained : report.wal.keeper.calls.slot ∈ (report.wal.keeper.calls.inventory.afterDrops duringRead).slots
  ownerRetained : admission.owner ∈ (report.wal.keeper.calls.inventory.afterDrops duringRead).slots
  directoryRetained : admission.cached ∈ (report.wal.keeper.calls.inventory.afterDrops duringRead).slots

namespace CapturedKeeperOpenReports

variable {report : CapturedMarkedReadReports admission layout published renameMarker readStart}

def atOpen (captured : CapturedKeeperOpenReports report) : DescriptorInventory :=
  report.listing.afterClose.afterDrops captured.beforeOpen

def afterRead (captured : CapturedKeeperOpenReports report) : DescriptorInventory :=
  report.wal.keeper.calls.inventory.afterDrops captured.duringRead

/-- The keeper allocation and all reported drops preserve the object map
used by the earlier marker open. -/
theorem afterRead_inode (captured : CapturedKeeperOpenReports report) :
    captured.afterRead.inode = admission.reached.inode := by
  unfold afterRead
  rw [captured.opened]
  change report.listing.afterClose.inode = _
  rw [report.listing.afterClose_eq]
  exact report.objectMap

/-- The first repair barrier uses the cached directory slot in the
inventory returned by the keeper read, including any other retained slots. -/
def directoryBarrier (captured : CapturedKeeperOpenReports report)
    (outcome : DelayedDirectorySyncOutcome) : DelayedDirectorySync directory :=
  captured.afterRead.delayedDirectorySync [] directory admission.cached.description admission.cached.reference
    (by
      rw [DescriptorInventory.references_afterDrops]
      exact List.mem_filter.mpr
        ⟨captured.afterRead.mem_references.mpr ⟨admission.cached, captured.directoryRetained, rfl, rfl⟩, rfl⟩)
    report.bindings (by
      have object : admission.view.modelObject admission.root = readStart.inode admission.cached.description :=
        report.lifetime.identifiesDirectory
      rw [captured.afterRead_inode, ← report.objectMap, ← object]
      exact report.canonicalDirectory) outcome

/-- A successful first directory barrier settles the repair namespace
and carries forward the actual keeper-read census. -/
theorem directoryBarrier_completed (captured : CapturedKeeperOpenReports report)
    (before : LockedFileState FileImage)
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error CensusOpenState Unit)
    (observed : fsync (admission.reached, admission.cached, 0) (captured.afterRead, before) =
      match (captured.directoryBarrier .completed).run before with
      | .ok value after => .ok value (captured.afterRead, after)
      | .error cause after => .error cause (captured.afterRead, after)) :
    fsync (admission.reached, admission.cached, 0) (captured.afterRead, before) =
      .ok () (captured.afterRead, { before with image := before.image.syncDirectory }) := by
  simpa only [directoryBarrier, DescriptorInventory.delayedDirectorySync, DelayedDirectorySync.run] using observed

/-- Interpret `readKeeperPrefix_fileEffects` with the same open and exact
prefix loop as the held read. In the successful projection the open adds
its reported slot, and the prefix applies the reported slot drops. -/
def readKeeperAt (captured : CapturedKeeperOpenReports report) (path : FilePath) (count physical : Nat) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) ByteArray :=
  readKeeperWith
    (fun name (cache, census, files) => match report.reads.openRead name with
      | .error cause => .error cause (cache, census, files)
      | .ok handle => .ok handle (cache, handle.1, files))
    (fun handle size (cache, census, files) =>
      match report.reads.readOpenedPrefix (IO.userError "short or oversized WAL keeper read") handle size with
      | .error cause => .error cause (cache, census, files)
      | .ok bytes => .ok bytes (cache, census.afterDrops captured.duringRead, files))
    (fun name handle (cache, state) => .ok () (cache.remember name handle, state))
    path count physical

def readKeeper (captured : CapturedKeeperOpenReports report) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) ByteArray :=
  captured.readKeeperAt (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
    report.wal.keeper.calls.metadata.byteSize.toNat

/-- Both native lookups resolve the checked keeper name at the captured
root. The reported open inserts a fresh description into the same slot
census reached after closedir. -/
theorem openedKeeper (captured : CapturedKeeperOpenReports report) :
    let file := report.wal.keeper
    let path := directory.file (.walSegment layout.keeper.first)
    report.catalog.inventory.reports.lstat path = .ok file.calls.metadata ∧
    file.calls.statLookup.child = file.object ∧ file.calls.openLookup.child = file.object ∧
    file.calls.inventory.inode file.calls.slot.description = admission.view.modelObject file.object ∧
    report.reads.openRead path = .ok (captured.atOpen.insert file.calls.slot captured.free, file.calls.slot, 0) ∧
    captured.afterRead.references file.calls.slot.description = [file.calls.slot.reference] := by
  intro file path
  refine ⟨?_, file.calls.statLookup.child_eq file.bound, file.calls.openLookup.child_eq file.bound, ?_, ?_, ?_⟩
  · rw [report.stat, file.calls.stat]
    rfl
  · rw [← file.calls.identifiedOpen, file.calls.openLookup.child_eq file.bound]
  · rw [file.calls.opened, captured.opened]
    rfl
  · change (file.calls.inventory.afterDrops captured.duringRead).references file.calls.slot.description = _
    have remains := (file.calls.inventory.afterDrops captured.duringRead).mem_references.mpr
      ⟨file.calls.slot, captured.keeperRetained, rfl, rfl⟩
    have original : file.calls.inventory.references file.calls.slot.description = [file.calls.slot.reference] := by
      rw [captured.opened, DescriptorInventory.references_insert, ite_eq_left rfl, captured.fresh]
    rw [DescriptorInventory.references_afterDrops, original] at remains ⊢
    have kept := (List.mem_filter.mp remains).2
    simp [kept]

/-- Every prefix of the drops during the read keeps the exact issuing
slots live. The same canonical keeper description supplies every chunk. -/
theorem readCensus (captured : CapturedKeeperOpenReports report) {earlier later : List LockReferenceDrop}
    (elapsed : captured.duringRead = earlier ++ later) :
    let atRead := report.wal.keeper.calls.inventory.afterDrops earlier
    report.wal.keeper.calls.slot ∈ atRead.slots ∧ admission.owner ∈ atRead.slots ∧ admission.cached ∈ atRead.slots := by
  intro atRead
  have keeps {slot : DescriptorSlot}
      (atEnd : slot ∈ (report.wal.keeper.calls.inventory.afterDrops captured.duringRead).slots) :
      slot ∈ atRead.slots := by
    rw [elapsed, ← DescriptorInventory.afterDrops_append] at atEnd
    exact (List.mem_filter.mp atEnd).1
  exact ⟨keeps captured.keeperRetained, keeps captured.ownerRetained, keeps captured.directoryRetained⟩

/-- The observed keeper open and exact chunk loop return the selected
prefix and its reached descriptor state. Cache admission depends on the
same physical extent used by the bounded reader. -/
theorem reads (captured : CapturedKeeperOpenReports report)
    (within : layout.keeper.bytes.size ≤ report.wal.keeper.calls.metadata.byteSize.toNat) :
    let file := report.wal.keeper
    let path := directory.file (.walSegment layout.keeper.first)
    let handle := (file.calls.inventory, file.calls.slot, 0)
    captured.readKeeper (admission.cache, captured.atOpen, admission.held) =
      .ok layout.keeper.bytes
        (admission.cache.captureKeeper path handle layout.keeper.bytes.size file.calls.metadata.byteSize.toNat,
          captured.afterRead, admission.held) := by
  intro file path handle
  let seen := file.observesFile
  have covered : layout.keeper.bytes.size ≤ (layout.keeper.bytes ++ layout.tail).size := by simp
  have selected := seen.readOpenedExactPrefix (IO.userError "short or oversized WAL keeper read")
    layout.keeper.bytes.size report.wal.keeperFits covered
  rw [ByteArray.extract_append_eq_left rfl] at selected
  unfold readKeeper readKeeperAt
  refine readKeeperWith_success admission.cache path layout.keeper.bytes.size file.calls.metadata.byteSize.toNat
    _ _ (openedState := (file.calls.inventory, admission.held)) ⟨within, report.wal.keeperFits⟩ ?_ ?_
  · rw [show report.reads.openRead path = .ok handle from file.calls.opened]
  · change (match report.reads.readOpenedPrefix (IO.userError "short or oversized WAL keeper read") handle
        layout.keeper.bytes.size with
      | .error cause => EStateM.Result.error cause (admission.cache, file.calls.inventory, admission.held)
      | .ok bytes => EStateM.Result.ok bytes (admission.cache, captured.afterRead, admission.held)) = _
    rw [show report.reads.readOpenedPrefix (IO.userError "short or oversized WAL keeper read") handle
      layout.keeper.bytes.size = .ok layout.keeper.bytes from selected]

/-- A successful aligned prefix remembers the issuing description. -/
theorem readsAligned (captured : CapturedKeeperOpenReports report)
    (aligned : layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat) :
    let file := report.wal.keeper
    let path := directory.file (.walSegment layout.keeper.first)
    let handle := (file.calls.inventory, file.calls.slot, 0)
    captured.readKeeper (admission.cache, captured.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache.remember path handle, captured.afterRead, admission.held) := by
  simpa only [Cache.captureKeeper, aligned, ite_true] using captured.reads (Nat.le_of_eq aligned)

/-- The old keeper is a temporary read when the physical file extends
past the selected marker. Its handle stays outside the pending cache. -/
theorem readsLong (captured : CapturedKeeperOpenReports report)
    (longer : layout.keeper.bytes.size < report.wal.keeper.calls.metadata.byteSize.toNat) :
    captured.readKeeper (admission.cache, captured.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache, captured.afterRead, admission.held) := by
  simpa only [Cache.captureKeeper, ite_eq_right (Nat.ne_of_lt longer)] using captured.reads (Nat.le_of_lt longer)

/-- Opening and reading the keeper leaves a separate marker descriptor
live in the census returned by the bounded read. -/
theorem preservesSlotAfterRead
    (keeper : CapturedKeeperOpenReports report) {slot : DescriptorSlot}
    (present : slot ∈ keeper.atOpen.slots)
    (retained : ∀ event ∈ keeper.duringRead, event.removes slot.reference = false) :
    slot ∈ keeper.afterRead.slots := by
  unfold CapturedKeeperOpenReports.afterRead
  rw [keeper.opened]
  exact List.mem_filter.mpr ⟨List.mem_cons_of_mem _ present,
    List.all_eq_true.mpr (by simpa using retained)⟩

/-- Closing the temporary keeper before staging the retained prefix
leaves the already-held marker slot available for the reopened session. -/
theorem preservesSlotAfterKeeperClose (captured : CapturedKeeperOpenReports report)
    {slot : DescriptorSlot} (present : slot ∈ captured.atOpen.slots)
    (retained : ∀ event ∈ captured.duringRead, event.removes slot.reference = false) :
    slot ∈ (captured.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent]).slots := by
  have finalizer := DescriptorInventory.closeOtherSlot present captured.free
  have atRead := captured.preservesSlotAfterRead present retained
  exact List.mem_filter.mpr ⟨atRead, by simp [finalizer]⟩

/-- The aligned finish uses the cached directory and keeper descriptions
even when the caller has already stabilized its marker. The first
barrier hands its reached files and census to the second barrier. -/
theorem finishAlignedFromCache (captured : CapturedKeeperOpenReports report)
    (aligned : layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat)
    (noLater : retry.image.later.visible = [])
    (openRead : FilePath → EStateM IO.Error CensusOpenState (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error CensusOpenState Unit)
    (removeFile : FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    {files : LockedFileState FileImage} {authorized : CensusOpenState}
    (settled : fsync (admission.reached, admission.cached, 0) (captured.afterRead, files) =
      .ok () authorized) :
    let path := directory.file (.walSegment layout.keeper.first)
    let handle := (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
    let grouped := SyncPathGroup.run (sync directory.path openRead fsync)
    finishBoundedMarkedOpen directory layout.boundedPlan report.wal.keeper.calls.metadata.byteSize.toNat
      removeFile write grouped renameFile (admission.cache.remember path handle, captured.afterRead, files) =
      match fsync handle authorized with
      | .ok () reached => .ok () (admission.cache, reached)
      | .error cause reached => .error (IO.userError s!"sync failed for '{path}': {cause}") (admission.cache, reached) := by
  intro path handle grouped
  let remembered := admission.cache.remember path handle
  have directorySync : grouped #[directory.path] (remembered, captured.afterRead, files) =
      .ok () (remembered, authorized) := by
    dsimp only [grouped]
    rw [SyncPathGroup.run_single]
    simp [sync, Cache.resolve, remembered, Cache.remember, CensusOpenAdmissionReports.cache, settled, withCache]
  have measured : report.wal.keeper.calls.metadata.byteSize.toNat = layout.boundedPlan.keeperSize :=
    aligned.symm.trans layout.target.trimmedSize
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have empty : layout.boundedPlan.newer = [] := noLater
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq size.symm, by simp [empty]⟩
  simp only [finishBoundedMarkedOpen, measured, valid, size, beq_self_eq_true,
    decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, empty, List.isEmpty_nil]
  change (grouped #[directory.path] >>= fun _ => grouped #[path])
    (remembered, captured.afterRead, files) = _
  simp only [Bind.bind, EStateM.bind, directorySync]
  change grouped #[path] (remembered, authorized) = _
  dsimp only [grouped, remembered]
  rw [SyncPathGroup.run_single, syncRemembered (file_ne_directory directory (.walSegment layout.keeper.first))]
  cases fsync handle authorized with
  | error cause reached => rfl
  | ok value reached => cases value; rfl

/-- The aligned read and first directory barrier reach the authorized files
and the same pending keeper handle. The reported intervening drops keep
the keeper and lock slots live. The next singleton barrier uses that
keeper description and consumes the entry before invoking fsync. -/
theorem syncFromRead (captured : CapturedKeeperOpenReports report)
    (aligned : layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat)
    (noLater : retry.image.later.visible = [])
    (openRead : FilePath → EStateM IO.Error CensusOpenState (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error CensusOpenState Unit)
    (removeFile : FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (afterRead : List LockReferenceDrop)
    (keeperLive : ∀ event ∈ afterRead, event.removes report.wal.keeper.calls.slot.reference = false)
    (ownerLive : ∀ event ∈ afterRead, event.removes admission.owner.reference = false)
    (settled : fsync (admission.reached, admission.cached, 0) (captured.afterRead, admission.held) =
      .ok () (captured.afterRead.afterDrops afterRead, { admission.held with image := retry.image.syncDirectory })) :
    let path := directory.file (.walSegment layout.keeper.first)
    let handle := (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
    let grouped := SyncPathGroup.run (sync directory.path openRead fsync)
    let authorized : CensusOpenState :=
      (captured.afterRead.afterDrops afterRead, { admission.held with image := retry.image.syncDirectory })
    report.wal.keeper.calls.slot ∈ authorized.1.slots ∧ admission.owner ∈ authorized.1.slots ∧
    authorized.1.inode report.wal.keeper.calls.slot.description = admission.view.modelObject report.wal.keeper.object ∧
    (captured.readKeeper >>= fun _ => finishBoundedMarkedOpen directory layout.boundedPlan
      report.wal.keeper.calls.metadata.byteSize.toNat removeFile write grouped renameFile)
      (admission.cache, captured.atOpen, admission.held) =
      match fsync handle authorized with
      | .ok () reached => .ok () (admission.cache, reached)
      | .error cause reached => .error (IO.userError s!"sync failed for '{path}': {cause}") (admission.cache, reached) := by
  intro path handle grouped authorized
  have survives {slot : DescriptorSlot} (present : slot ∈ captured.afterRead.slots)
      (retained : ∀ event ∈ afterRead, event.removes slot.reference = false) : slot ∈ authorized.1.slots := by
    exact List.mem_filter.mpr ⟨present, List.all_eq_true.mpr fun event member => by rw [retained event member]; rfl⟩
  refine ⟨survives captured.keeperRetained keeperLive, survives captured.ownerRetained ownerLive,
    captured.openedKeeper.2.2.2.1, ?_⟩
  have readResult : captured.readKeeper (admission.cache, captured.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache.remember path handle, captured.afterRead, admission.held) :=
    captured.readsAligned aligned
  simp only [Bind.bind, EStateM.bind, readResult]
  exact captured.finishAlignedFromCache aligned noLater openRead fsync removeFile write renameFile settled

end CapturedKeeperOpenReports
end Alvoki.Storage.DiskSession
