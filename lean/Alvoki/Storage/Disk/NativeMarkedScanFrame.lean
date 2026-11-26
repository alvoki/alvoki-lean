import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.RetainedWriterReopen
import Alvoki.Storage.Disk.NativeDurableWriteReboot

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

/-- The independent projections a read-only callback frames. The names
also cover the later alias check. Live bytes are needed only for the
one keeper that the selected plan will open. -/
structure MarkedOpenReadFrame (directory : DiskDirectory) (protectedPaths : FilePath → Prop)
    (keeperPath : FilePath) (before after : CheckpointStorageObservation)
    (beforeBytes afterBytes : Nat → ByteArray) : Prop where
  durable : before.Frames protectedPaths after
  names : ∀ path, (path = directory.path ∨ ∃ file, path = directory.file file) →
    after.files.names path = before.files.names path
  keeper : (CheckpointSurvivingFiles.mk before.files.names fun inode => [beforeBytes inode]).Frames
    (· = keeperPath) ⟨after.files.names, fun inode => [afterBytes inode]⟩

theorem MarkedOpenReadFrame.refl (directory : DiskDirectory) (protectedPaths : FilePath → Prop)
    (keeperPath : FilePath) (storage : CheckpointStorageObservation) (bytes : Nat → ByteArray) :
    MarkedOpenReadFrame directory protectedPaths keeperPath storage storage bytes bytes :=
  ⟨.refl _ _, fun _ _ => rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

theorem MarkedOpenReadFrame.trans {directory : DiskDirectory} {protectedPaths : FilePath → Prop}
    {keeperPath : FilePath} {before middle after : CheckpointStorageObservation}
    {beforeBytes middleBytes afterBytes : Nat → ByteArray}
    (first : MarkedOpenReadFrame directory protectedPaths keeperPath before middle beforeBytes middleBytes)
    (second : MarkedOpenReadFrame directory protectedPaths keeperPath middle after middleBytes afterBytes) :
    MarkedOpenReadFrame directory protectedPaths keeperPath before after beforeBytes afterBytes :=
  ⟨first.durable.trans second.durable, fun path inside => (second.names path inside).trans (first.names path inside),
    first.keeper.trans second.keeper⟩

structure MarkedDirectoryReadCalls.ScopeFrames {heap stream : Type}
    (calls : MarkedDirectoryReadCalls heap stream) (directory : DiskDirectory)
    (frame : heap → heap → Prop) : Prop where
  openDir : ∀ {entry reached handle}, calls.openDir directory.path entry = .ok handle reached → frame entry reached
  readDir : ∀ {entry opened handle}, calls.openDir directory.path entry = .ok handle opened →
    frame opened (calls.readDir handle opened).2
  closeDir : ∀ {entry opened scanned reached handle report}, calls.openDir directory.path entry = .ok handle opened →
    calls.readDir handle opened = (report, scanned) → calls.closeDir handle scanned = .ok () reached →
    frame scanned reached

section Listing

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}

variable {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot}

/-- Apply a scoped frame through the actual directory stream's open,
scan and close. Local laws can frame both bytes and parent settlement. -/
theorem MarkedDirectoryReadReport.framesScan
    (seen : MarkedDirectoryReadReport prepared directoryCalls slotOf)
    (frame : heap → heap → Prop) (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (effects : directoryCalls.ScopeFrames directory frame) :
    frame prepared.atScan seen.reached := by
  have scan := effects.readDir seen.openedRaw
  rw [seen.readRaw] at scan
  exact trans (trans (effects.openDir seen.openedRaw) scan) (effects.closeDir seen.openedRaw seen.readRaw seen.closedRaw)

/-- Each selected seal read carries the same scope through its actual
returned heap, including the release. The keeper is still unread. -/
theorem MarkedSealReadChain.framesSeals {released : FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)} {initial : DescriptorInventory} {drops : List LockReferenceDrop}
    {physical : CapturedSealReadChain reads released required initial drops} {before reached : heap}
    (observed : MarkedSealReadChain seed fileCalls physical before reached)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (one : ∀ first count {start finish bytes},
      fileCalls.seal (directory.file (.walSegment first)) count start = .ok bytes finish → frame start finish) :
    frame before reached := by
  induction observed with
  | keeper => exact refl _
  | sealed _ _ _ _ raw _ rest =>
    exact trans (one _ _ raw.returns.1) rest

/-- Follow the same read-only checkpoint, directory and sealed-WAL
callbacks regardless of how the selected recovery will repair the keeper. -/
theorem MarkedDirectoryReadReport.framesThroughSeals
    (seen : MarkedDirectoryReadReport prepared directoryCalls slotOf)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    {beforeKeeper : heap} (seals : MarkedSealReadChain seed fileCalls chronology.seals seen.reached beforeKeeper)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (readEffects : fileCalls.ScopeFrames frame) (listingEffects : directoryCalls.ScopeFrames directory frame) :
    frame seed.afterPending seen.reached ∧ frame seen.reached beforeKeeper := by
  exact ⟨trans (prepared.framesScan selected readEffects refl trans)
    (seen.framesScan frame trans listingEffects),
    seals.framesSeals frame refl trans (fun first count {_ _ _} returned =>
      fileCalls.readSealKeepsFrame readEffects refl trans (directory.file (.walSegment first)) count returned)⟩

end Listing

section Healthy

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit} {stream : Type}

variable {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}

/-- Carry the frame to the checked listing and separately through the
ordered seal reads to the keeper entry. The extent probes did not move
the heap. The split exposes the point where the link census was read. -/
theorem RawHealthyMarkedOpenEffects.framesReadPrefix
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (reads : raw.fileCalls.ScopeFrames frame)
    (listing : raw.directoryCalls.ScopeFrames directory frame) :
    frame raw.seed.afterPending raw.listing.reached ∧ frame raw.listing.reached raw.beforeKeeper := by
  exact raw.listing.framesThroughSeals selected raw.seals frame refl trans reads listing

end Healthy

section ActualWalStat

variable {heap : Type} {frame : heap → heap → Prop}

theorem MarkedDirectoryReadCalls.successKeepsFrame {stream : Type} (calls : MarkedDirectoryReadCalls heap stream)
    (directory : DiskDirectory) (laws : calls.ScopeFrames directory frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    {before after : heap} {entries : Array IO.FS.DirEntry}
    (returned : calls.run directory.path before = .ok entries after) : frame before after := by
  obtain ⟨file, opened, scanned, names, openedCall, readCall, closed, returnedEntries⟩ :=
    calls.returnedScan directory.path returned
  have readFrame := laws.readDir openedCall
  rw [readCall] at readFrame
  exact trans (laws.openDir openedCall) (trans readFrame (laws.closeDir openedCall readCall closed))

private theorem filterMapM_success_frames {α β : Type} (run : α → EStateM IO.Error heap (Option β))
    (items : List α) (refl : ∀ before, frame before before)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (step : ∀ item {before after value}, run item before = .ok value after → frame before after)
    {before after : heap} {results : List β} (returned : (items.filterMapM run) before = .ok results after) :
    frame before after := by
  induction items generalizing before after results with
  | nil =>
    have equal : before = after := (EStateM.Result.ok.inj returned).2
    exact equal ▸ refl before
  | cons item rest ih =>
    simp only [List.filterMapM_cons, Bind.bind, EStateM.bind] at returned
    cases head : run item before with
    | error cause failed => simp [head] at returned
    | ok value middle =>
      cases tail : (rest.filterMapM run) middle with
      | error cause failed => cases value <;> simp [head, tail, EStateM.bind] at returned
      | ok values endAt =>
        have tailFrame := ih tail
        have whole := trans (step item head) tailFrame
        cases value <;> simp [head, tail, EStateM.bind, Pure.pure, EStateM.pure] at returned <;> exact returned.2 ▸ whole

private theorem walExtentProbe_success_frame (fileCalls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    (refl : ∀ before, frame before before)
    (stat : ∀ path before, frame before (reachedState (fileCalls.stat path before)))
    (name : String) {before after : heap} {value : Option (Nat × IO.FS.Metadata)}
    (returned : readWalSegmentExtentWith directory (MarkedWalExtentReports.inspect fileCalls) name before =
      .ok value after) : frame before after := by
  cases parsed : parseWalSegmentName name with
  | none =>
    simp only [readWalSegmentExtentWith, parsed, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
    exact returned.2 ▸ refl before
  | some first =>
    let path := directory.file (.walSegment first)
    simp only [readWalSegmentExtentWith, parsed, Bind.bind, EStateM.bind] at returned
    cases observed : MarkedWalExtentReports.inspect fileCalls path before with
    | error cause failed => simp [path, observed] at returned
    | ok report reached =>
      have raw := MarkedWalExtentReports.inspectReturned fileCalls path observed
      have framed : frame before reached := by simpa only [raw, reachedState] using stat path before
      cases answer : classifyWalSegmentLookup path first report with
      | error cause =>
        simp [path, observed, answer, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      | ok payload =>
        cases payload <;> simp [path, observed, answer, Pure.pure, EStateM.pure] at returned <;>
          exact returned.2 ▸ framed

private theorem walExtentScan_success_frame (fileCalls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) (names : List String) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (stat : ∀ path before, frame before (reachedState (fileCalls.stat path before)))
    {before after : heap} {extents : List (Nat × IO.FS.Metadata)}
    (returned : readWalSegmentExtentsWith directory (MarkedWalExtentReports.inspect fileCalls) names before =
      .ok extents after) : frame before after := by
  simp only [readWalSegmentExtentsWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at returned
  cases scan : (names.filterMapM (readWalSegmentExtentWith directory (MarkedWalExtentReports.inspect fileCalls))) before with
  | error cause failed => simp [scan] at returned
  | ok found reached =>
    simp only [scan, EStateM.Result.ok.injEq] at returned
    obtain ⟨_, rfl⟩ := returned
    exact filterMapM_success_frames _ names refl trans (walExtentProbe_success_frame fileCalls directory refl stat) scan

/-- On a successful selected WAL read, carry one relation through the
actual checked listing, guarded stat scan, seal traversal and keeper.
The relation can track physical storage or live descriptor state. -/
theorem MarkedTemporaryReadCalls.selectedWalKeepsFrame {stream : Type}
    (fileCalls : MarkedTemporaryReadCalls heap) (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (directory : DiskDirectory) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (reads : fileCalls.ScopeFrames frame) (listing : directoryCalls.ScopeFrames directory frame)
    (stat : ∀ path before, frame before (reachedState (fileCalls.stat path before)))
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after → frame before after)
    {watermark : Nat} {length : UInt64} {entry reached : heap} {payload : WalSegmentMarkerReads × Nat}
    (returned : readSelectedWithCachedExtents directory watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal (fileCalls.readKeeperWithRelease remember) entry =
        .ok payload reached) : frame entry reached := by
  obtain ⟨files, size⟩ := payload
  have actual := SelectedWalReadReturn.classifies directory watermark length directoryCalls.run
    (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal (fileCalls.readKeeperWithRelease remember) entry
  rw [returned] at actual
  obtain ⟨_, _, _, _, _, _, listed, scanned, _, _, ordered⟩ := actual.successfulPayloads
  exact trans (directoryCalls.successKeepsFrame directory listing trans listed)
    (trans (walExtentScan_success_frame fileCalls directory _ refl trans stat scanned)
      (fileCalls.walPayloadKeepsFrame reads refl trans remember remembers ordered rfl))

private def visibleImage (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [visible atHeap inode]⟩

/-- The successful stat order determines which inode and full extent
each selected pair describes. The local stat observation and the same
file frame carry that binding through the scan, ready for the payload read. -/
theorem MarkedWalExtentReports.selectedPhysicalExtent (fileCalls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (scope : FilePath → Prop) (statObject : FilePath → heap → heap → Option Nat)
    (observeStat : ∀ {path before after metadata}, fileCalls.stat path before = .ok (.ok metadata) after →
      ∃ inode, statObject path before after = some inode ∧ names before path = some inode ∧
        metadata.byteSize.toNat = (visible before inode).size)
    (statFrame : ∀ path before, (visibleImage names visible before).Frames scope
      (visibleImage names visible (reachedState (fileCalls.stat path before))))
    (namesInOrder : List String) {origin listed scanned : heap}
    (starts : (visibleImage names visible origin).Frames scope (visibleImage names visible listed))
    {extents required : List (Nat × IO.FS.Metadata)} {watermark through first : Nat}
    {later : List Nat} {metadata : IO.FS.Metadata}
    (scan : readWalSegmentExtentsWith directory (inspect fileCalls) namesInOrder listed = .ok extents scanned)
    (selected : selectWalExtentsThrough extents watermark through = some (required, later))
    (member : (first, metadata) ∈ required)
    (inScope : scope (directory.file (.walSegment first))) :
    let path := directory.file (.walSegment first)
    ∃ (issued statHeap : heap) (inode : Nat),
      fileCalls.stat path issued = .ok (.ok metadata) statHeap ∧
      statObject path issued statHeap = some inode ∧ names origin path = some inode ∧
      names scanned path = some inode ∧ metadata.byteSize.toNat = (visible origin inode).size ∧
      names issued path = some inode ∧ metadata.numLinks = 1 ∧
      (visibleImage names visible origin).Frames scope (visibleImage names visible issued) ∧
      (visibleImage names visible origin).Frames scope (visibleImage names visible scanned) := by
  intro path
  obtain ⟨earlier, _, _, issued, statHeap, _, priorReports, _, raw, oneLink⟩ :=
    selectedStat fileCalls directory namesInOrder scan selected member
  let framed (before after : heap) :=
    (visibleImage names visible before).Frames scope (visibleImage names visible after)
  have refl (atHeap : heap) : framed atHeap atHeap := fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  have prior : framed listed issued := filterMapM_success_frames _ earlier refl
    CheckpointSurvivingFiles.Frames.trans (walExtentProbe_success_frame fileCalls directory refl statFrame) priorReports
  have full : framed listed scanned :=
    walExtentScan_success_frame fileCalls directory namesInOrder refl CheckpointSurvivingFiles.Frames.trans statFrame scan
  obtain ⟨inode, exactObject, bound, trueSize⟩ := observeStat raw
  obtain ⟨sameName, sameBytes⟩ := starts.trans prior path inScope
  have original : names origin path = some inode := sameName.symm.trans bound
  have contentEq : visible issued inode = visible origin inode := (List.cons.inj (sameBytes inode original)).1
  exact ⟨issued, statHeap, inode, raw, exactObject, original,
    ((starts.trans full path inScope).1).trans original, trueSize.trans (congrArg ByteArray.size contentEq),
    bound, oneLink, starts.trans prior, starts.trans full⟩

/-- The full keeper extent comes from the same inode that supplied the
bounded prefix. The reached cache callback or release is selected by the
prefix length and that actual inode extent. -/
theorem MarkedTemporaryReadCalls.readsMarkedKeeperWithPhysicalExtent
    {stream image : Type} (fileCalls : MarkedTemporaryReadCalls heap)
    (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (directory : DiskDirectory) (view : OpenCloseHeapView heap image)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (scope : FilePath → Prop) (inScope : ∀ first, scope (directory.file (.walSegment first)))
    (opens : fileCalls.OpensReadSlot view names visible) (reads : fileCalls.ReadsAtCursor view visible)
    (scopedReads : fileCalls.ScopeFrames (fun before after =>
      (visibleImage names visible before).Frames scope (visibleImage names visible after)))
    (listingFrames : directoryCalls.ScopeFrames directory (fun before after =>
      (visibleImage names visible before).Frames scope (visibleImage names visible after)))
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after →
      (visibleImage names visible before).Frames scope (visibleImage names visible after))
    (statObject : FilePath → heap → heap → Option Nat)
    (statTruth : ∀ {path before after metadata}, fileCalls.stat path before = .ok (.ok metadata) after →
      ∃ inode, statObject path before after = some inode ∧ names before path = some inode ∧
        metadata.byteSize.toNat = (visible before inode).size)
    (statFrame : ∀ path before, (visibleImage names visible before).Frames scope
      (visibleImage names visible (reachedState (fileCalls.stat path before))))
    {entry reached : heap} {watermark : Nat} {length : UInt64} {payloads : WalSegmentMarkerReads} {extent : Nat}
    (returned : readSelectedWithCachedExtents directory watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal
      (fileCalls.readKeeperWithRelease remember) entry = .ok (payloads, extent) reached) :
    let through := length.toNat / WAL.frameSize
    ∃ (keeper : Nat) (metadata : IO.FS.Metadata) (file : IO.FS.Handle) (slot : DescriptorSlot)
      (inode : Nat) (issued statHeap beforeKeeper opened readHeap : heap) (prefixBytes : ByteArray),
      let path := directory.file (.walSegment keeper)
      let count := (through - keeper) * WAL.frameSize
      fileCalls.stat path issued = .ok (.ok metadata) statHeap ∧
      statObject path issued statHeap = some inode ∧ names entry path = some inode ∧
      fileCalls.openRead path beforeKeeper = .ok file opened ∧ attachedReadSlot view file slot inode readHeap ∧
      payloads.files.getLast? = some (keeper, prefixBytes) ∧
      prefixBytes = (visible entry inode).extract 0 count ∧ extent = (visible entry inode).size ∧
      ((count = extent ∧ remember path file readHeap = .ok () reached) ∨
        (count < extent ∧ fileCalls.release file readHeap = .ok () reached)) ∧
      (visibleImage names visible entry).Frames scope (visibleImage names visible reached) := by
  intro through
  have observed := SelectedWalReadReturn.classifies directory watermark length directoryCalls.run
    (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal (fileCalls.readKeeperWithRelease remember) entry
  rw [returned] at observed
  obtain ⟨entries, listed, extents, scanned, required, _, listing, scan, selected, _, observedFiles⟩ :=
    observed.successfulPayloads
  let frame (before after : heap) := (visibleImage names visible before).Frames scope
    (visibleImage names visible after)
  have refl (atHeap : heap) : frame atHeap atHeap := fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  have listedFrame : frame entry listed :=
    directoryCalls.successKeepsFrame directory listingFrames CheckpointSurvivingFiles.Frames.trans listing
  have statFrames : frame listed scanned :=
    walExtentScan_success_frame fileCalls directory _ refl CheckpointSurvivingFiles.Frames.trans statFrame scan
  obtain ⟨keeper, metadata, earlier, bytes, beforeKeeper, opened, readHeap, file, slot, openedInode, last,
    _, files, expectedSize, named, acquired, held, exactPrefix, route, _, finalFrame⟩ :=
    fileCalls.restoresSelectedWalBytes view names visible scope opens reads scopedReads remember remembers
      (fun extent _ => inScope extent.1) (listedFrame.trans statFrames) observedFiles rfl
  have selectedKeeper : (keeper, metadata) ∈ required := List.mem_of_getLast? last
  obtain ⟨issued, statHeap, inode, stat, measured, original, _, trueSize, _, _, _, _⟩ :=
    MarkedWalExtentReports.selectedPhysicalExtent fileCalls directory names visible scope statObject statTruth
      statFrame _ listedFrame scan selected selectedKeeper (inScope keeper)
  have sameInode := Option.some.inj (original.symm.trans named)
  subst openedInode
  exact ⟨keeper, metadata, file, slot, inode, issued, statHeap, beforeKeeper, opened, readHeap, bytes,
    stat, measured, original, acquired, held, by simp [files], exactPrefix, expectedSize.trans trueSize, route, finalFrame⟩

private theorem mapM_matchesKeys {α β γ δ : Type} (read : α → Option β)
    (sourceKey : α → γ) (canonicalKey : δ → γ) (payload : δ → β)
    (source : List α) (canonical : List δ)
    (keys : source.map sourceKey = canonical.map canonicalKey)
    (agrees : ∀ entry ∈ source, ∀ item ∈ canonical, sourceKey entry = canonicalKey item →
      read entry = some (payload item)) :
    source.mapM read = some (canonical.map payload) := by
  induction source generalizing canonical with
  | nil =>
    cases canonical with
    | nil => rfl
    | cons item rest => simp at keys
  | cons entry rest ih =>
    cases canonical with
    | nil => simp at keys
    | cons item tail =>
      obtain ⟨same, remaining⟩ := List.cons.inj keys
      have first := agrees entry List.mem_cons_self item List.mem_cons_self same
      have restReads := ih tail remaining (fun entry member item named =>
        agrees entry (List.mem_cons_of_mem _ member) item (List.mem_cons_of_mem _ named))
      simp [List.mapM_cons, first, restReads, Pure.pure, Bind.bind, Option.bind]

/-- The literal WAL payload fold is canonical once the actual selected
metadata has the corresponding offsets and reached physical extents.
The keeper remains a prefix of its full visible bytes. -/
theorem CanonicalKeeperLayout.matchesSelectedWalPayloads
    {image : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout image history)
    {required : List (Nat × IO.FS.Metadata)} {keeper : Nat} {metadata : IO.FS.Metadata}
    {earlier : List (Nat × ByteArray)} {bytes : ByteArray} {inode : Nat}
    (atName : Nat → Option Nat) (visible : Nat → ByteArray)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (last : required.getLast? = some (keeper, metadata))
    (reads : required.dropLast.mapM (fun extent => (atName extent.1).map fun i =>
      (extent.1, (visible i).extract 0 extent.2.byteSize.toNat)) = some earlier)
    (stat : ∀ extent ∈ required, ∀ i, atName extent.1 = some i →
      extent.2.byteSize.toNat = (visible i).size)
    (sealed : ∀ segment ∈ layout.sealed, (atName segment.first).map visible = some segment.bytes)
    (keeperName : atName keeper = some inode)
    (keeperContent : (atName layout.keeper.first).map visible = some (layout.keeper.bytes ++ layout.tail))
    (keeperPrefix : bytes = (visible inode).extract 0 ((layout.range.through - keeper) * WAL.frameSize)) :
    earlier ++ [(keeper, bytes)] =
      (layout.sealed ++ [layout.keeper]).map (fun segment => (segment.first, segment.bytes)) ∧
      metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size := by
  have keeperFirst : keeper = layout.keeper.first := by
    have seen := congrArg List.getLast? offsets
    simpa [last] using seen
  have seals : required.dropLast.map Prod.fst = layout.sealed.map WalSegment.first := by
    rw [List.map_dropLast, offsets]
    simp
  have actualSeals := mapM_matchesKeys
    (fun extent : Nat × IO.FS.Metadata => (atName extent.1).map fun i =>
      (extent.1, (visible i).extract 0 extent.2.byteSize.toNat)) Prod.fst WalSegment.first (fun segment => (segment.first, segment.bytes))
    required.dropLast layout.sealed seals (by
      intro extent seen segment member key
      obtain ⟨i, named, exactBytes⟩ := Option.map_eq_some_iff.mp (sealed segment member)
      have ownName : atName extent.1 = some i := key.symm ▸ named
      have full := stat extent ((List.dropLast_sublist required).subset seen) i ownName
      simp only [key, named, Option.map_some, full, exactBytes, ByteArray.extract_zero_size])
  have exactSeals := Option.some.inj (reads.symm.trans actualSeals)
  have exactKeeper : visible inode = layout.keeper.bytes ++ layout.tail := by
    rw [← keeperFirst, keeperName, Option.map_some] at keeperContent
    exact Option.some.inj keeperContent
  have keeperBytes : bytes = layout.keeper.bytes := by
    have count : layout.keeper.bytes.size = (layout.range.through - keeper) * WAL.frameSize := by
      simpa [keeperFirst, CanonicalKeeperLayout.target] using layout.target.trimmedSize
    rw [keeperPrefix, exactKeeper, ← count, ByteArray.extract_append_eq_left rfl]
  rw [exactSeals, keeperFirst, keeperBytes, List.map_append]
  exact ⟨rfl, (stat (keeper, metadata) (List.mem_of_getLast? last) inode keeperName).trans (congrArg ByteArray.size exactKeeper)⟩

private theorem chainStarts {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history first segments) (nonempty : segments ≠ []) :
    ∃ rest, segments.map WalSegment.first = first :: rest := by
  cases chain with
  | endOfHistory => contradiction
  | cons => exact ⟨_, rfl⟩

/-- The abstract writer's successful selector already identifies the
whole logical suffix from the covering start. This gives the exact cut
where separately framed native name agreement is needed. -/
theorem NativeReadPosition.SelectedWritePlan.modeledWindow
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition prior log} {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image) :
    let wal := current.state.writer.wal.appendSelectedView image.directory.active plan.history
    (∀ start, plan.layout.first ≤ start →
      (start ∈ wal.segments.map WalSegment.first ↔
        start ∈ (plan.layout.sealed ++ [plan.layout.keeper]).map WalSegment.first)) ∧
    (∀ start ∈ ((plan.layout.sealed ++ [plan.layout.keeper]).map WalSegment.first).drop 1,
      plan.layout.range.watermark < start) := by
  intro wal
  have offsets := plan.offsets
  change selectWalSegmentReads (wal.segments.map WalSegment.first) plan.layout.range.watermark =
    some (plan.layout.first, (wal.readDescriptors plan.layout.range.watermark).map WalSegment.first) at offsets
  rw [← plan.descriptors] at offsets
  unfold selectWalSegmentReads at offsets
  let selected := (plan.layout.sealed ++ [plan.layout.keeper]).map WalSegment.first
  cases best : ((wal.segments.map WalSegment.first).filter
      (fun start => decide (start ≤ plan.layout.range.watermark))).max? with
  | none => simp [best, Bind.bind, Option.bind] at offsets
  | some first =>
    have details : first = plan.layout.first ∧
        (wal.segments.map WalSegment.first).filter (fun start => decide (first ≤ start)) = selected := by
      simpa only [best, Bind.bind, Option.bind, Pure.pure, Option.some.injEq, Prod.mk.injEq] using offsets
    obtain ⟨rfl, exactOffsets⟩ := details
    have membership (start : Nat) (cover : plan.layout.first ≤ start) :
        start ∈ wal.segments.map WalSegment.first ↔ start ∈ selected := by
      rw [← exactOffsets, List.mem_filter, decide_eq_true_eq, and_iff_left cover]
    refine ⟨membership, ?_⟩
    have shape : ∃ rest, selected = plan.layout.first :: rest :=
      chainStarts plan.layout.chain (by simp)
    obtain ⟨rest, shape⟩ := shape
    have strict := List.pairwise_map.mpr plan.layout.chain.startsStrict
    change selected.Pairwise (· < ·) at strict
    rw [shape] at strict
    intro start inRest
    change start ∈ selected.drop 1 at inRest
    rw [shape, List.drop_succ_cons, List.drop_zero] at inRest
    have after := (List.pairwise_cons.mp strict).1 start inRest
    apply Nat.lt_of_not_ge
    intro high
    have stored := (membership start (Nat.le_of_lt after)).mpr (shape.symm ▸ List.mem_cons_of_mem _ inRest)
    have below := (List.max?_eq_some_iff.mp best).2 start
      (List.mem_filter.mpr ⟨stored, decide_eq_true high⟩)
    exact (Nat.not_le_of_gt after) below


theorem _root_.Alvoki.Storage.WalSegmentImage.appendSelectedView_starts (wal : WalSegmentImage) (pair : DirectoryPublication.Bindings)
    (history : List WAL.Write) :
    (wal.appendSelectedView pair history).segments.map WalSegment.first = wal.segments.map WalSegment.first := by
  rw [WalSegmentImage.segments, List.map_append, WalSegmentImage.segments, List.map_append]
  rfl

/-- The actual marked scan identifies the later names independently of
the retained catalog. Below the cutoff use the carried window, which
can include older seals skipped by the checkpoint reader. Above it
use the scan's complete canonical child projection. -/
theorem NativeReadPosition.SelectedWritePlan.walNamespaceAtPreparation
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition prior log} {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image)
    {entryNames preparedNames : FilePath → Option Nat} {first : Nat} {newer : List Nat}
    (priorWindow : current.state.writer.wal.NamespaceWindow current.state.session.directory first
      (prior ++ batch).length entryNames)
    (framed : ∀ start, preparedNames (current.state.session.directory.file (.walSegment start)) =
      entryNames (current.state.session.directory.file (.walSegment start)))
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (child : ∀ start, plan.layout.range.through < start →
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        entryNames (current.state.session.directory.file (.walSegment start)))
    (listed : ∀ start, start ∈ newer ↔ plan.layout.range.through < start ∧
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) :
    let directory := current.state.session.directory
    let wal := current.state.writer.wal.appendSelectedView image.directory.active plan.history
    wal.NamespaceWindow directory first plan.layout.range.through preparedNames ∧
    (∀ start ∈ wal.segments.map WalSegment.first, start ≤ plan.layout.range.through) ∧
    (∀ start ∈ newer, plan.layout.range.through < start) ∧
    ∀ start, plan.layout.range.through < start →
      ((preparedNames (directory.file (.walSegment start))).isSome = true ↔ start ∈ newer) := by
  intro directory wal
  have through : plan.layout.range.through ≤ (prior ++ batch).length := by
    rw [plan.layout.through]
    rcases plan.allowed with old | complete
    · simp [old]
    · simp [complete]
  refine ⟨?_, ?_, fun start member => (listed start).mp member |>.1, ?_⟩
  · intro start lower upper
    have alignedNames := priorWindow start lower (Nat.le_trans upper through)
    rw [framed start, WalSegmentImage.appendSelectedView_starts]
    exact alignedNames
  · intro start member
    obtain ⟨segment, present, rfl⟩ := List.mem_map.mp member
    have active : wal.active.first ≤ plan.layout.range.through := by
      simpa only [CanonicalKeeperLayout.target, plan.keeper] using plan.layout.target.firstCovered
    rcases List.mem_append.mp present with sealed | keeper
    · have before := (List.pairwise_append.mp plan.walLayout.ordered).2.2 _ sealed _ (List.mem_singleton_self _)
      exact Nat.le_trans (plan.walLayout.forward _ present) (Nat.le_trans before.2 active)
    · obtain rfl := List.mem_singleton.mp keeper
      exact active
  · intro start beyond
    rw [framed start, ← child start beyond, Option.isSome_map, listed start]
    cases found : namespaceView.child root (renderWalSegmentName start) <;> simp [beyond]

/-- The selected append changes the active bytes and end, while leaving
the segment starts used by the native reader fixed. -/
theorem NativeReadPosition.SelectedWritePlan.liveWalWindow
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition prior log} {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image) (names : FilePath → Option Nat)
    (window : current.state.writer.wal.NamespaceWindow current.state.session.directory
      plan.layout.first plan.layout.range.through names) :
    ∀ start, plan.layout.first ≤ start → start ≤ plan.layout.range.through →
      ((names (current.state.session.directory.file (.walSegment start))).isSome = true ↔
        start ∈ (plan.layout.sealed ++ [plan.layout.keeper]).map WalSegment.first) := by
  intro start lower upper
  have selected := plan.modeledWindow.1 start lower
  rw [WalSegmentImage.appendSelectedView_starts] at selected
  exact (window start lower upper).trans selected

/-- At a recovery boundary, the live name map agrees with the selected
window, the seal bytes, and the keeper including any uncommitted tail. -/
structure CanonicalKeeperLayout.VisibleWal {files : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout files history) (directory : DiskDirectory)
    (names : FilePath → Option Nat) (visible : Nat → ByteArray) : Prop where
  window : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
    ((names (directory.file (.walSegment start))).isSome = true ↔
      start ∈ (layout.sealed ++ [layout.keeper]).map WalSegment.first)
  sealed : ∀ segment ∈ layout.sealed,
    (names (directory.file (.walSegment segment.first))).map visible = some segment.bytes
  keeper : (names (directory.file (.walSegment layout.keeper.first))).map visible =
    some (layout.keeper.bytes ++ layout.tail)

/-- The entry of the next open combines the immutable seal footprint
with the independently framed names and live keeper of that retry. -/
theorem NativeReadPosition.SelectedWritePlan.visibleWal
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition prior log} {batch : List WAL.Write} {target : Target}
    {view : OpenCloseHeapView heap FileImage} {entry : heap}
    (plan : current.SelectedWritePlan batch target (view.files entry).image)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (window : current.state.writer.wal.NamespaceWindow current.state.session.directory
      plan.layout.first plan.layout.range.through (names entry))
    (protectedFiles : NativeReadyProtectedStorage current.state ⟨names entry, fun inode => [visible entry inode]⟩)
    (keeper : RawOpenRetryTrace.KeeperAt view current.state.session.directory target names visible entry) :
    plan.layout.VisibleWal current.state.session.directory (names entry) (visible entry) := by
  refine ⟨plan.liveWalWindow (names entry) window, ?_, ?_⟩
  · intro segment selected
    obtain ⟨inode, bound, bytes⟩ := protectedFiles.sealedFiles segment
      (NativeReadPosition.SelectedWritePlan.retainsSeal current plan selected)
    change names entry (current.state.session.directory.file (.walSegment segment.first)) = some inode at bound
    rw [bound, Option.map_some]
    exact congrArg some (List.cons.inj bytes).1
  · have sameFirst : plan.layout.keeper.first = target.first := congrArg Target.first plan.targetEq
    rw [sameFirst]
    exact keeper.symm.trans plan.layout.visible

private theorem NativeReadPosition.preparesVisibleWriteRetryFromEffects
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {prior : List WAL.Write} {log : List DatabaseSubmissions} (current : NativeReadPosition prior log)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {view : OpenCloseHeapView heap FileImage} {start reached : heap}
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {first : Nat} (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, first ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target names visible start)
    {returns : List (FilePath × IO.Error)} {attempts : source.FailedCalls start returns reached} {keep : heap → Prop}
    (effects : RawOpenRetryTrace.SelectedEffects view source start target (visibleImage names visible)
      current.state.selectedRetryPath keep attempts)
    (atEntry : keep start)
    (atReached : keep reached →
      current.state.writer.wal.NamespaceWindow current.state.session.directory first (prior ++ batch).length
        (names reached) ∧ RawOpenRetryTrace.KeeperAt view current.state.session.directory target names visible reached) :
    ∃ plan : current.SelectedWritePlan batch target (view.files reached).image,
      plan.layout.VisibleWal current.state.session.directory (names reached) (visible reached) ∧
      RawOpenRetryTrace.SelectedEntry view current.state target names visible reached ∧ keep reached := by
  obtain ⟨valid, kept, protectedFrame, carries⟩ := effects.preserves initial.valid
  obtain ⟨plan⟩ := current.preparesSelectedWrite prepared fits admitted valid initial.manifest
  have preserved := carries atEntry
  obtain ⟨reachedWindow, reachedKeeper⟩ := atReached preserved
  obtain ⟨rest, firstRead⟩ := chainStarts plan.layout.chain (by simp)
  have firstInWal := (plan.modeledWindow.1 plan.layout.first (Nat.le_refl _)).mpr
    (firstRead ▸ List.mem_cons_self (a := plan.layout.first) (l := rest))
  rw [WalSegmentImage.appendSelectedView_starts] at firstInWal
  have upper : plan.layout.range.through ≤ (prior ++ batch).length := by
    rw [plan.layout.through]
    rcases plan.allowed with old | complete
    · simp [old]
    · simp [complete]
  have keptFiles := initial.protectedFiles.frame (fun path keep => protectedFrame path (.inr keep))
  refine ⟨plan, plan.visibleWal names visible (reachedWindow.restrict (covers _ firstInWal) upper) keptFiles reachedKeeper,
    ⟨valid, kept.trans initial.kept, initial.manifest, keptFiles, reachedKeeper, ?_⟩, preserved⟩
  exact (protectedFrame.visiblePayload (.inl rfl)).trans initial.marker

/-- Carry the WAL window and the live keeper through the same failed
calls as the protected checkpoint. The initial name bound reaches as
far as either marker after the uncertain batch. -/
theorem NativeReadPosition.preparesVisibleWriteRetry
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {prior : List WAL.Write} {log : List DatabaseSubmissions} (current : NativeReadPosition prior log)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {view : OpenCloseHeapView heap FileImage} {start reached : heap}
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {first : Nat} (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, first ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target names visible start)
    (window : current.state.writer.wal.NamespaceWindow current.state.session.directory first
      (prior ++ batch).length (names start))
    {returns : List (FilePath × IO.Error)} {attempts : source.FailedCalls start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source start target (visibleImage names visible)
      current.state.selectedRetryPath (fun atHeap =>
        current.state.writer.wal.NamespaceWindow current.state.session.directory first (prior ++ batch).length
          (names atHeap) ∧ RawOpenRetryTrace.KeeperAt view current.state.session.directory target names visible atHeap)
      attempts) :
    ∃ plan : current.SelectedWritePlan batch target (view.files reached).image,
      plan.layout.VisibleWal current.state.session.directory (names reached) (visible reached) := by
  obtain ⟨plan, physical, _⟩ := current.preparesVisibleWriteRetryFromEffects prepared fits admitted names visible
    covers initial effects ⟨window, initial.keeper⟩ id
  exact ⟨plan, physical⟩

/-- The exact failed opens carry the live WAL, protected checkpoint and
marker, and durable storage to the same heap for the next reader. -/
theorem NativeReadPosition.preparesDurableVisibleWriteRetry
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {prior : List WAL.Write} {log : List DatabaseSubmissions} (current : NativeReadPosition prior log)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target}
    (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {view : OpenCloseHeapView heap FileImage} {start reached : heap}
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {first : Nat} (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, first ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target (fun heap => (storage heap).files.names) visible start)
    (window : current.state.writer.wal.NamespaceWindow current.state.session.directory first
      (prior ++ batch).length (storage start).files.names)
    (durable : current.state.SelectedRetryDurability target (storage start))
    {keep : heap → Prop} (initialKeep : keep start)
    {returns : List (FilePath × IO.Error)} {attempts : source.FailedCalls start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source start target
      (visibleImage (fun heap => (storage heap).files.names) visible) current.state.selectedRetryPath
      (fun atHeap =>
        current.state.writer.wal.NamespaceWindow current.state.session.directory first (prior ++ batch).length
          (storage atHeap).files.names ∧
        RawOpenRetryTrace.KeeperAt view current.state.session.directory target
          (fun heap => (storage heap).files.names) visible atHeap ∧
        current.state.SelectedRetryDurability target (storage atHeap) ∧ keep atHeap) attempts) :
    ∃ plan : current.SelectedWritePlan batch target (view.files reached).image,
      plan.layout.VisibleWal current.state.session.directory (storage reached).files.names (visible reached) ∧
      RawOpenRetryTrace.SelectedEntry view current.state target (fun heap => (storage heap).files.names) visible reached ∧
      current.state.SelectedRetryDurability target (storage reached) ∧ keep reached ∧
      current.state.writer.wal.NamespaceWindow current.state.session.directory first
        (prior ++ batch).length (storage reached).files.names := by
  obtain ⟨plan, physical, selected, reachedWindow, _, settled, kept⟩ :=
    current.preparesVisibleWriteRetryFromEffects prepared fits admitted (fun heap => (storage heap).files.names) visible
      covers initial effects ⟨window, initial.keeper, durable, initialKeep⟩ (fun kept => ⟨kept.1, kept.2.1⟩)
  exact ⟨plan, physical, selected, settled, kept, reachedWindow⟩

/-- Refine the actual WAL return using only the held recovery window
and reached file effects. Both the canonical replay bytes and the
actual keeper route come from the same payload traversal. The keeper's
one-link guard excludes a distinct managed binding when such bindings
count as separate links at the actual stat. -/
theorem MarkedTemporaryReadCalls.readsCanonicalWal
    {stream image : Type} (fileCalls : MarkedTemporaryReadCalls heap)
    (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (directory : DiskDirectory) (view : OpenCloseHeapView heap image)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {files : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout files history)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (scope : FilePath → Prop)
    (opens : fileCalls.OpensReadSlot view names visible) (reads : fileCalls.ReadsAtCursor view visible)
    (scopedReads : fileCalls.ScopeFrames (fun before after =>
      (visibleImage names visible before).Frames scope (visibleImage names visible after)))
    (listingFrames : directoryCalls.ScopeFrames directory (fun before after =>
      (visibleImage names visible before).Frames scope (visibleImage names visible after)))
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after →
      (visibleImage names visible before).Frames scope (visibleImage names visible after))
    (statObject : FilePath → heap → heap → Option Nat)
    (statTruth : ∀ {path before after metadata}, fileCalls.stat path before = .ok (.ok metadata) after →
      ∃ inode, statObject path before after = some inode ∧ names before path = some inode ∧
        metadata.byteSize.toNat = (visible before inode).size)
    (statFrame : ∀ path before, (visibleImage names visible before).Frames scope
      (visibleImage names visible (reachedState (fileCalls.stat path before))))
    {initial entry reached : heap} {length : UInt64} {payloads : WalSegmentMarkerReads} {extent : Nat}
    (starts : (visibleImage names visible initial).Frames scope (visibleImage names visible entry))
    (listedNames : ∀ {entries : Array IO.FS.DirEntry} {listed : heap},
      directoryCalls.run directory.path entry = .ok entries listed →
      (entries.toList.map (·.fileName)).Perm (namespaceView.names root))
    (absent : ∀ {entries : Array IO.FS.DirEntry} {listed : heap},
      directoryCalls.run directory.path entry = .ok entries listed →
      MarkedWalExtentReports.TruthfulAbsence fileCalls directory namespaceView root
        (entries.toList.map (·.fileName)) listed)
    (through : length.toNat / WAL.frameSize = layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (physical : layout.VisibleWal directory (names initial) (visible initial))
    (scopedWindow : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
      scope (directory.file (.walSegment start)))
    (child : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names entry (directory.file (.walSegment start)))
    (returned : readSelectedWithCachedExtents directory layout.range.watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal (fileCalls.readKeeperWithRelease remember) entry =
        .ok (payloads, extent) reached) :
    payloads.files = (layout.sealed ++ [layout.keeper]).map (fun segment => (segment.first, segment.bytes)) ∧
    extent = (layout.keeper.bytes ++ layout.tail).size ∧
    (∀ start, start ∈ payloads.newer ↔ layout.range.through < start ∧
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ∧
    ∃ (file : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat) (beforeKeeper opened readHeap : heap),
      let path := directory.file (.walSegment layout.keeper.first)
      names initial path = some inode ∧
      fileCalls.openRead path beforeKeeper = .ok file opened ∧ attachedReadSlot view file slot inode readHeap ∧
      ((layout.keeper.bytes.size = extent ∧ remember path file readHeap = .ok () reached) ∨
        (layout.keeper.bytes.size < extent ∧ fileCalls.release file readHeap = .ok () reached)) ∧
      (visibleImage names visible initial).Frames scope (visibleImage names visible reached) ∧
      ((∀ {issued statHeap metadata other}, fileCalls.stat path issued = .ok (.ok metadata) statHeap →
        statObject path issued statHeap = some inode → scope path → scope other →
        (other = directory.path ∨ ∃ file, other = directory.file file) → other ≠ path →
        names issued path = some inode → names issued other = some inode → 2 ≤ metadata.numLinks.toNat) →
        ∀ other, scope other → (other = directory.path ∨ ∃ file, other = directory.file file) →
          names reached other = some inode → other = path) := by
  have observed := SelectedWalReadReturn.classifies directory layout.range.watermark length directoryCalls.run
    (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal (fileCalls.readKeeperWithRelease remember) entry
  rw [returned] at observed
  obtain ⟨entries, listed, extents, scanned, required, aligned, listedCall, scan, selected, _, orderedReads⟩ :=
    observed.successfulPayloads
  rw [through] at selected orderedReads
  let segments := layout.sealed ++ [layout.keeper]
  obtain ⟨expected, first⟩ := chainStarts layout.chain (by simp)
  have canonical := List.pairwise_map.mpr layout.chain.startsStrict
  change (segments.map WalSegment.first).Pairwise (· < ·) at canonical
  rw [first] at canonical
  have bounds : ∀ start ∈ expected, layout.range.watermark < start ∧ start ≤ layout.range.through := by
    intro start member
    have afterCover := following start (by simpa only [first, List.drop_succ_cons, List.drop_zero] using member)
    have mapped : start ∈ segments.map WalSegment.first := by rw [first]; exact List.mem_cons_of_mem _ member
    obtain ⟨segment, part, rfl⟩ := List.mem_map.mp mapped
    exact ⟨afterCover, layout.through ▸ layout.chain.startsWithin segment part⟩
  have heldWindow (start : Nat) (lower : layout.first ≤ start) (upper : start ≤ layout.range.through) :
      ((∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ↔
        start ∈ layout.first :: expected) := by
    have atInitial := (child start lower upper).trans (starts _ (scopedWindow start lower upper)).1
    change (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
      names initial (directory.file (.walSegment start)) at atInitial
    have present := physical.window start lower upper
    rw [← atInitial, Option.isSome_map, first] at present
    exact Option.isSome_iff_exists.symm.trans present
  obtain ⟨need, laterNames⟩ :=
    MarkedWalExtentReports.selectsWindow fileCalls directory namespaceView root _ (listedNames listedCall) scan
      (absent listedCall) selected (orderedReads.successfulOrder rfl) canonical layout.covers
      (through ▸ aligned.2) bounds heldWindow
  have offsets : required.map Prod.fst = segments.map WalSegment.first := need.trans first.symm
  have protectedExtent : ∀ extent ∈ required, scope (directory.file (.walSegment extent.1)) := by
    intro extent member
    have selectedOffset : extent.1 ∈ required.map Prod.fst := List.mem_map.mpr ⟨extent, member, rfl⟩
    have within : extent.1 ∈ layout.first :: expected := need ▸ selectedOffset
    rcases List.mem_cons.mp within with same | later
    · exact scopedWindow extent.1 (Nat.le_of_eq same.symm) (same ▸ Nat.le_trans layout.covers (through ▸ aligned.2))
    · exact scopedWindow extent.1 (Nat.le_trans layout.covers (Nat.le_of_lt (bounds _ later).1)) (bounds _ later).2
  let frame (before after : heap) := (visibleImage names visible before).Frames scope
    (visibleImage names visible after)
  have refl (atHeap : heap) : frame atHeap atHeap := fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  have listedFrame : frame initial listed :=
    starts.trans (directoryCalls.successKeepsFrame directory listingFrames CheckpointSurvivingFiles.Frames.trans listedCall)
  have scannedFrame : frame listed scanned :=
    walExtentScan_success_frame fileCalls directory _ refl CheckpointSurvivingFiles.Frames.trans statFrame scan
  obtain ⟨keeper, metadata, earlier, bytes, beforeKeeper, opened, readHeap, file, slot, inode, last,
    sealReads, fileList, extentEq, named, acquired, held, exactPrefix, route, _, finalFrame⟩ :=
    fileCalls.restoresSelectedWalBytes view names visible scope opens reads scopedReads remember remembers
      protectedExtent (listedFrame.trans scannedFrame) orderedReads rfl
  have selectedExtent {offset metadata} (member : (offset, metadata) ∈ required) :=
    MarkedWalExtentReports.selectedPhysicalExtent fileCalls directory names visible scope statObject statTruth statFrame
      _ listedFrame scan selected member (protectedExtent (offset, metadata) member)
  let atName := fun start => names initial (directory.file (.walSegment start))
  have truthfulExtent : ∀ extent ∈ required, ∀ inode, atName extent.1 = some inode →
      extent.2.byteSize.toNat = (visible initial inode).size := by
    rintro ⟨offset, metadata⟩ member inode name
    obtain ⟨_, _, measuredInode, _, _, same, _, size, _, _, _, _⟩ := selectedExtent member
    exact (Option.some.inj (same.symm.trans name)) ▸ size
  obtain ⟨sameFiles, sameExtent⟩ := layout.matchesSelectedWalPayloads atName (visible initial) offsets last
    sealReads truthfulExtent physical.sealed named physical.keeper exactPrefix
  have keeperFirst : keeper = layout.keeper.first := by
    have seen := congrArg List.getLast? offsets
    simpa [segments, last] using seen
  have count : layout.keeper.bytes.size = (layout.range.through - keeper) * WAL.frameSize := by
    simpa [keeperFirst, CanonicalKeeperLayout.target] using layout.target.trimmedSize
  refine ⟨fileList.trans sameFiles, extentEq.trans sameExtent, laterNames,
    file, slot, inode, beforeKeeper, opened, readHeap, ?_, ?_, held, ?_, finalFrame, ?_⟩
  · simpa only [keeperFirst] using named
  · simpa only [keeperFirst] using acquired
  · rw [count]
    simpa only [keeperFirst] using route
  · intro countLinks other inside managed aliased
    by_cases samePath : other = directory.file (.walSegment layout.keeper.first)
    · exact samePath
    · exfalso
      have member := List.mem_of_getLast? last
      obtain ⟨issued, statHeap, statInode, called, object, original, _, _, bound, oneLink, prior, _⟩ :=
        selectedExtent member
      have same := Option.some.inj (original.symm.trans named)
      subst statInode
      have aliasAtStat : names issued other = some inode :=
        (prior other inside).1.trans ((finalFrame other inside).1.symm.trans aliased)
      have two := countLinks (keeperFirst ▸ called) (keeperFirst ▸ object)
        (keeperFirst ▸ protectedExtent (keeper, metadata) member) inside managed samePath (keeperFirst ▸ bound) aliasAtStat
      rw [oneLink] at two
      change 2 ≤ 1 at two
      omega

end ActualWalStat

/-- Replay the exact decoded marker and bounded selected WAL payloads
from the restored checkpoint. A physical tail has already been left
outside the bounded reader's result. -/
theorem CanonicalKeeperLayout.replaysSelected {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) {published : CheckpointPublication.Image}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable image.directory.active.manifest checkpoint)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {marker : ByteArray} {count : UInt64}
    (markerName : image.directory.active.walBoundary = some marker)
    (markerRead : WAL.Boundary.decode marker = .ok count)
    {files : List (Nat × ByteArray)}
    (payloads : files = layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(layout.keeper.first, layout.keeper.bytes)]) :
    ∃ table model,
      recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files =
        .ok (WAL.encode (history.drop layout.first), table) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
      count.toNat = history.length * WAL.frameSize ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧
      table.pins = (checkpoint.getD (.empty, 0)).1.pins ∧ table.pins.active = [] := by
  obtain ⟨watermark, _, _, canonical, markerAt, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  obtain rfl := Option.some.inj (markerName.symm.trans markerAt)
  obtain rfl := Except.ok.inj (markerRead.symm.trans decoded)
  rw [layout.through] at absolute
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [WAL.encode_size, absolute, Nat.mul_comm]
  obtain ⟨base, table, model, known, full, committed, bounded, refined, represents, fresh⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  obtain rfl := known.uniqueResult selected
  have clock := Option.some.inj (selected.watermark.symm.trans watermark)
  have replay := layout.chain.replaysMarked ByteArray.empty absolute (clock.symm ▸ layout.covers) ordered full
  obtain ⟨_, _, applied, _⟩ := recoverSelected_success full
  refine ⟨table, model, ?_, full, absolute, committed, bounded, refined, represents, replay_pins applied, fresh⟩
  simpa only [payloads, ByteArray.append_empty] using replay

/-- Assemble the ordinary retained writer from the actual replay return
and the held files at the actual repaired heap. The replay supplies the
table and marker count; the repair supplies readiness and lock ownership. -/
theorem CanonicalKeeperLayout.retainedFromActualReplay
    {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) {published : CheckpointPublication.Image}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable image.directory.active.manifest checkpoint)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {marker : ByteArray} {count : UInt64}
    (markerName : image.directory.active.walBoundary = some marker)
    (markerRead : WAL.Boundary.decode marker = .ok count)
    {files : List (Nat × ByteArray)} {patched : ByteArray} {table : PackedTable}
    (payloads : files = (layout.sealed ++ [layout.keeper]).map (fun segment => (segment.first, segment.bytes)))
    (replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files = .ok (patched, table))
    {wal : WalSegmentImage} {final : LockedFileState FileImage}
    {directory : DiskDirectory} {descriptor : Nat}
    (walLayout : wal.ReadLayout history) (valid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (walPair : wal.directory.active = layout.target.pair)
    (keeper : layout.keeper.first = wal.active.first)
    (ready : final.image.Ready layout.target)
    (sealed : final.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    (held : final.owners.Owns directory descriptor) :
    let installed := Reopened.installed ⟨table, (checkpoint.getD (.empty, 0)).2, count, layout.keeper.first⟩
    let writer := SegmentedWriterState.ofReopen installed wal history published layout.target checkpoint final
    writer.RetainedReady directory descriptor ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok writer.installed.table ∧
      writer.installed.table.pins = (checkpoint.getD (.empty, 0)).1.pins ∧
      writer.installed.table.pins.active = [] := by
  obtain ⟨recovered, model, returned, replay, absolute, _, rowBounds, refines, historyModel, pins, inactive⟩ :=
    layout.replaysSelected selected accepted ordered markerName markerRead (by simpa [List.map_append] using payloads)
  have same := (Prod.mk.inj (Except.ok.inj (returned.symm.trans replayed))).2
  subst recovered
  intro installed writer
  have byteCount : count.toNat = (WAL.encode history).size := by
    rw [absolute, WAL.encode_size, Nat.mul_comm]
  have resumed : ResumedAppendReady writer.installed writer.files writer.target writer.history
      writer.published writer.checkpoint :=
    ⟨ready, layout.through, rfl, byteCount, layout.chain.keeperBytes, rfl, selected, accepted, ordered,
      rowBounds, ⟨model, refines, historyModel⟩⟩
  exact ⟨SegmentedWriterState.ofReopenRetained walLayout valid spans walPair keeper sealed held resumed,
    replay, pins, inactive⟩

end Alvoki.Storage.DiskSession
