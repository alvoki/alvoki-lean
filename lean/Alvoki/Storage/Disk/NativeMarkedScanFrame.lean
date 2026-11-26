import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.RetainedWriterReopen

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
  readDir : ∀ handle entry, frame entry (calls.readDir handle entry).2
  closeDir : ∀ {entry reached handle}, calls.closeDir handle entry = .ok () reached → frame entry reached

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
  have scan := effects.readDir seen.descriptor seen.opened
  rw [seen.readRaw] at scan
  exact trans (trans (effects.openDir seen.openedRaw) scan) (effects.closeDir seen.closedRaw)

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
  have sealFrame (first count : Nat) {start finish : heap} {bytes : ByteArray}
      (returned : fileCalls.seal (directory.file (.walSegment first)) count start = .ok bytes finish) :
      frame start finish := by
    have read := fileCalls.readWithFrames readEffects trans (directory.file (.walSegment first)) _
      (fun file => exactReadFrames refl trans selectedWalSpanError (fileCalls.readChunk file)
        (readEffects.readChunk file) count ByteArray.empty) start
    change frame start (reachedState (fileCalls.seal (directory.file (.walSegment first)) count start)) at read
    simpa only [returned, reachedState] using read
  exact ⟨trans (prepared.framesScan selected readEffects refl trans)
    (seen.framesScan frame trans listingEffects), seals.framesSeals frame refl trans sealFrame⟩

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
  have readFrame := laws.readDir file opened
  rw [readCall] at readFrame
  exact trans (laws.openDir openedCall) (trans readFrame (laws.closeDir closed))

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
      (visibleImage names visible origin).Frames scope (visibleImage names visible scanned) := by
  intro path
  obtain ⟨earlier, _, _, issued, statHeap, _, priorReports, _, raw⟩ :=
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
    ((starts.trans full path inScope).1).trans original, trueSize.trans (congrArg ByteArray.size contentEq), starts.trans full⟩

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
  obtain ⟨issued, statHeap, inode, stat, measured, original, _, trueSize, _⟩ :=
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

/-- Refine the actual WAL return using only the held recovery window
and reached file effects. Both the canonical replay bytes and the
actual keeper route come from the same payload traversal. -/
theorem MarkedTemporaryReadCalls.readsCanonicalWal
    {stream image : Type} (fileCalls : MarkedTemporaryReadCalls heap)
    (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (directory : DiskDirectory) (view : OpenCloseHeapView heap image)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {files : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout files history)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (scope : FilePath → Prop)
    (scopedSegments : ∀ segment ∈ layout.sealed ++ [layout.keeper],
      scope (directory.file (.walSegment segment.first)))
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
    (catalog : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
      ((∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ↔
        start ∈ (layout.sealed ++ [layout.keeper]).map WalSegment.first))
    (sealed : ∀ segment ∈ layout.sealed,
      (names initial (directory.file (.walSegment segment.first))).map (visible initial) = some segment.bytes)
    (keeperContent : (names initial (directory.file (.walSegment layout.keeper.first))).map (visible initial) =
      some (layout.keeper.bytes ++ layout.tail))
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
      (visibleImage names visible initial).Frames scope (visibleImage names visible reached) := by
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
  obtain ⟨need, laterNames⟩ :=
    MarkedWalExtentReports.selectsWindow fileCalls directory namespaceView root _ (listedNames listedCall) scan
      (absent listedCall) selected (orderedReads.successfulOrder rfl) canonical layout.covers
      (through ▸ aligned.2) bounds (fun start lower upper => by simpa only [first] using catalog start lower upper)
  have offsets : required.map Prod.fst = segments.map WalSegment.first := need.trans first.symm
  have protectedExtent : ∀ extent ∈ required, scope (directory.file (.walSegment extent.1)) := by
    intro extent member
    have selectedOffset : extent.1 ∈ required.map Prod.fst := List.mem_map.mpr ⟨extent, member, rfl⟩
    rw [offsets] at selectedOffset
    obtain ⟨segment, part, agrees⟩ := List.mem_map.mp selectedOffset
    simpa only [agrees] using scopedSegments segment part
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
  let atName := fun start => names initial (directory.file (.walSegment start))
  have truthfulExtent : ∀ extent ∈ required, ∀ inode, atName extent.1 = some inode →
      extent.2.byteSize.toNat = (visible initial inode).size := by
    rintro ⟨offset, metadata⟩ member inode name
    obtain ⟨_, _, measuredInode, _, _, same, _, size, _⟩ :=
      MarkedWalExtentReports.selectedPhysicalExtent fileCalls directory names visible scope statObject statTruth statFrame
        _ listedFrame scan selected member (protectedExtent (offset, metadata) member)
    exact (Option.some.inj (same.symm.trans name)) ▸ size
  obtain ⟨sameFiles, sameExtent⟩ := layout.matchesSelectedWalPayloads atName (visible initial) offsets last
    sealReads truthfulExtent sealed named keeperContent exactPrefix
  have keeperFirst : keeper = layout.keeper.first := by
    have seen := congrArg List.getLast? offsets
    simpa [segments, last] using seen
  have count : layout.keeper.bytes.size = (layout.range.through - keeper) * WAL.frameSize := by
    simpa [keeperFirst, CanonicalKeeperLayout.target] using layout.target.trimmedSize
  refine ⟨fileList.trans sameFiles, extentEq.trans sameExtent, laterNames,
    file, slot, inode, beforeKeeper, opened, readHeap, ?_, ?_, held, ?_, finalFrame⟩
  · simpa only [keeperFirst] using named
  · simpa only [keeperFirst] using acquired
  · rw [count]
    simpa only [keeperFirst] using route

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
