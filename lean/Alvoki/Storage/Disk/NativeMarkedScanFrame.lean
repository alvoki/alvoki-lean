import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects

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

end ActualWalStat

end Alvoki.Storage.DiskSession
