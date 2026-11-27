import Alvoki.Storage.Disk.NativeAlignedMarkedWorker
import Alvoki.Storage.Disk.Proofs.Keeper.NativeLongKeeperSettlementHeap
import Alvoki.Storage.Disk.NativeWalPayloadReturn
import Alvoki.Storage.Disk.Checkpoint.BarrierRetryObservations

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Keep the native length guard and pending selection. The successful
long read scope also observes the release of its temporary descriptor. -/
def MarkedTemporaryReadCalls.readKeeperWithRelease (reader : MarkedTemporaryReadCalls heap)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (path : FilePath) (count physical : Nat) : EStateM IO.Error heap ByteArray :=
  readKeeperWith reader.openRead (fun file size => do
    let bytes ← readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (reader.readChunk file) size ByteArray.empty
    if size < physical then reader.release file
    pure bytes) remember path count physical

/-- Recover the actual prefix read and final callback from a successful
keeper return. Only an aligned keeper is remembered. A longer keeper
returns after the separate release of that same read handle. -/
theorem MarkedTemporaryReadCalls.readKeeperWithRelease_ok (calls : MarkedTemporaryReadCalls heap)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (path : FilePath) (count physical : Nat) {before reached : heap} {bytes : ByteArray}
    (returned : calls.readKeeperWithRelease remember path count physical before = .ok bytes reached) :
    ∃ (file : IO.FS.Handle) (opened readHeap : heap),
      count ≤ physical ∧ count < USize.size ∧ calls.openRead path before = .ok file opened ∧
      readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
        (calls.readChunk file) count .empty opened = .ok bytes readHeap ∧
      ((count = physical ∧ remember path file readHeap = .ok () reached) ∨
        (count < physical ∧ calls.release file readHeap = .ok () reached)) := by
  unfold readKeeperWithRelease readKeeperWith at returned
  by_cases admitted : count ≤ physical ∧ count < USize.size
  · simp only [ite_eq_left admitted, Bind.bind, EStateM.bind, Pure.pure] at returned
    cases acquired : calls.openRead path before with
    | error cause after => simp [acquired] at returned
    | ok file opened =>
      simp only [acquired] at returned
      cases read : readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
          (calls.readChunk file) count .empty opened with
      | error cause after => simp [read] at returned
      | ok payload readHeap =>
        simp only [read] at returned
        by_cases aligned : count = physical
        · have finalized := returned
          subst physical
          simp only [Nat.lt_irrefl, ↓reduceIte, BEq.rfl, EStateM.bind, EStateM.pure] at finalized
          cases remembered : remember path file readHeap with
          | error cause after => simp [remembered] at finalized
          | ok value after =>
            cases value
            obtain ⟨rfl, rfl⟩ : payload = bytes ∧ after = reached := by
              simpa only [remembered, EStateM.Result.ok.injEq] using finalized
            exact ⟨file, opened, readHeap, admitted.1, admitted.2, rfl, read, .inl ⟨rfl, remembered⟩⟩
        · have longer := Nat.lt_of_le_of_ne admitted.1 aligned
          simp only [longer, ↓reduceIte, EStateM.bind, EStateM.pure, beq_iff_eq, aligned] at returned
          cases released : calls.release file readHeap with
          | error cause after => simp [released] at returned
          | ok value after =>
            cases value
            obtain ⟨rfl, rfl⟩ : payload = bytes ∧ after = reached := by
              simpa only [released, EStateM.Result.ok.injEq] using returned
            exact ⟨file, opened, readHeap, admitted.1, admitted.2, rfl, read, .inr ⟨longer, released⟩⟩
  · simp [admitted, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned

/-- The literal keeper prefix comes from the chosen inode at the read heap.
The reported physical extent controls how that same handle is finalized.
It is independent of the length of the consumed prefix. -/
theorem MarkedTemporaryReadCalls.readSelectedKeeper (calls : MarkedTemporaryReadCalls heap)
    (view : OpenCloseHeapView heap image) (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (path : FilePath) (count physical : Nat) {before reached : heap} {bytes : ByteArray}
    (returned : calls.readKeeperWithRelease remember path count physical before = .ok bytes reached) :
    ∃ (file : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat) (opened readHeap : heap),
      count ≤ physical ∧ count < USize.size ∧ calls.openRead path before = .ok file opened ∧
      names before path = some inode ∧ attachedReadSlot view file slot inode opened ∧
      attachedReadSlot view file slot inode readHeap ∧ (view.handle readHeap file).2.2 = count ∧
      visible readHeap inode = visible before inode ∧ bytes = (visible readHeap inode).extract 0 count ∧
      ((count = physical ∧ remember path file readHeap = .ok () reached) ∨
        (count < physical ∧ calls.release file readHeap = .ok () reached)) := by
  obtain ⟨file, opened, readHeap, covered, fits, acquired, payload, finished⟩ :=
    calls.readKeeperWithRelease_ok remember path count physical returned
  obtain ⟨slot, inode, name, openedSlot, readSlot, cursor, stable, bytes⟩ :=
    calls.readExactOpenedFile view names visible opens reads path (IO.userError "short or oversized WAL keeper read")
      count acquired payload
  exact ⟨file, slot, inode, opened, readHeap, covered, fits, acquired, name, openedSlot, readSlot, cursor, stable, bytes, finished⟩

section WalPayloadFrames

variable {heap : Type} {frame : heap → heap → Prop}

/-- A seal's open, bounded chunk loop and release frame its actual return. -/
theorem MarkedTemporaryReadCalls.sealFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (path : FilePath) (count : Nat) (entry : heap) : frame entry (reachedState (calls.seal path count entry)) :=
  calls.readWithFrames laws trans path
    (fun file => readExactPrefixWith selectedWalSpanError (calls.readChunk file) count .empty)
    (calls.exactPrefixFrames refl trans selectedWalSpanError count) entry

theorem MarkedTemporaryReadCalls.readSealKeepsFrame (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (path : FilePath) (count : Nat) {entry reached : heap} {bytes : ByteArray}
    (returned : calls.seal path count entry = .ok bytes reached) : frame entry reached := by
  simpa only [returned, reachedState] using calls.sealFrames laws refl trans path count entry

/-- Follow each reached keeper operation. The full prefix can lead to
an explicit release or a cache update. A returned callback error ends
the modeled read at that callback's reached heap. -/
theorem MarkedTemporaryReadCalls.keeperFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ path file before, frame before (reachedState (remember path file before)))
    (path : FilePath) (count physical : Nat) (entry : heap) :
    frame entry (reachedState (calls.readKeeperWithRelease remember path count physical entry)) := by
  unfold readKeeperWithRelease readKeeperWith
  by_cases admitted : count ≤ physical ∧ count < USize.size
  · simp only [ite_eq_left admitted, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    obtain ⟨temporary, guarded⟩ := laws
    have opened := guarded.openRead path entry
    cases acquired : calls.openRead path entry with
    | error cause after => simpa only [acquired, reachedState] using opened
    | ok file openedAt =>
      simp only [acquired]
      have openFrame : frame entry openedAt := by simpa only [acquired, reachedState] using opened
      have readFrame := calls.exactPrefixFrames refl trans (IO.userError "short or oversized WAL keeper read")
        count temporary file (guarded.readChunk file) openedAt
      change GuardedReadFrame frame temporary file openedAt (reachedState (readExactPrefixWith
        (IO.userError "short or oversized WAL keeper read") (calls.readChunk file) count .empty openedAt)) at readFrame
      cases read : readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
          (calls.readChunk file) count .empty openedAt with
      | error cause after =>
        rw [read, reachedState] at readFrame
        simpa only [read, reachedState] using trans openFrame readFrame.1
      | ok bytes after =>
        rw [read, reachedState] at readFrame
        have prefixFrame := trans openFrame readFrame.1
        by_cases aligned : count = physical
        · subst physical
          have kept := trans prefixFrame (remembers path file after)
          cases recorded : remember path file after <;>
            simpa only [read, Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true, EStateM.bind, EStateM.pure,
              recorded, reachedState] using kept
        · have longer := Nat.lt_of_le_of_ne admitted.1 aligned
          have live := readFrame.2 (guarded.opensTemporary acquired)
          have kept := trans prefixFrame (guarded.release file after live)
          cases released : calls.release file after <;>
            simpa only [read, longer, ↓reduceIte, beq_iff_eq, aligned, EStateM.bind, EStateM.pure,
              released, dataErrorDropState, reachedState] using kept
  · simpa [admitted, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      reachedState] using refl entry

/-- The keeper carries the frame through the same bounded chunk loop and
then through the callback that was actually reached, remember or release. -/
theorem MarkedTemporaryReadCalls.readKeeperKeepsFrame (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after → frame before after)
    (path : FilePath) (count physical : Nat) {before reached : heap} {bytes : ByteArray}
    (returned : calls.readKeeperWithRelease remember path count physical before = .ok bytes reached) :
    frame before reached := by
  obtain ⟨file, opened, readHeap, _, _, acquired, payload, finished⟩ :=
    calls.readKeeperWithRelease_ok remember path count physical returned
  obtain ⟨temporary, guarded⟩ := laws
  have openFrame := guarded.openRead path before
  rw [acquired, reachedState] at openFrame
  have readFrame := calls.exactPrefixFrames refl trans (IO.userError "short or oversized WAL keeper read") count
    temporary file (guarded.readChunk file) opened
  change GuardedReadFrame frame temporary file opened
    (reachedState (readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (calls.readChunk file) count ByteArray.empty opened)) at readFrame
  rw [payload, reachedState] at readFrame
  have finalFrame : frame readHeap reached := by
    rcases finished with ⟨_, retained⟩ | ⟨_, released⟩
    · exact remembers retained
    · have live := readFrame.2 (guarded.opensTemporary acquired)
      simpa only [dataErrorDropState, released] using guarded.release file readHeap live
  exact trans openFrame (trans readFrame.1 finalFrame)

/-- The accepted payload traversal composes the frame through its actual
seal releases and the final keeper callback, in observed heap order. -/
theorem MarkedTemporaryReadCalls.walPayloadKeepsFrame (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.ScopeFrames frame) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after → frame before after)
    {directory : DiskDirectory} {through : Nat} {required : List (Nat × IO.FS.Metadata)} {entry : heap}
    {result : EStateM.Result IO.Error heap (List (Nat × ByteArray) × Nat)}
    (observed : CachedWalPayloadReturn directory through calls.seal (calls.readKeeperWithRelease remember)
      required entry result)
    {payload : List (Nat × ByteArray) × Nat} {reached : heap}
    (returned : result = .ok payload reached) : frame entry reached := by
  induction observed generalizing payload reached with
  | noKeeper _ | keeperError _ | invalidKeeper _ _ | invalidOrder _ | sealError _ _ | sealedThenError _ _ _ =>
    cases returned
  | kept read _ =>
    obtain ⟨_, rfl⟩ := EStateM.Result.ok.inj returned
    exact calls.readKeeperKeepsFrame laws refl trans remember remembers _ _ _ read
  | sealed _ read _ ih =>
    obtain ⟨_, rfl⟩ := EStateM.Result.ok.inj returned
    cases read with
    | accepted sized _ readSeal _ =>
      obtain ⟨_, rfl⟩ := EStateM.Result.ok.inj sized
      exact trans (calls.readSealKeepsFrame laws refl trans _ _ readSeal) (ih rfl)

end WalPayloadFrames

section VisibleWal

variable {heap image : Type} {directory : DiskDirectory}
  (calls : MarkedTemporaryReadCalls heap) (view : OpenCloseHeapView heap image)
  (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray) (scope : FilePath → Prop)

private def visibleWalFiles (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [visible atHeap inode]⟩

local notation "frames" => fun first last =>
  CheckpointSurvivingFiles.Frames scope (visibleWalFiles names visible first) (visibleWalFiles names visible last)

/-- The successful selected WAL payload loop frames the same visible names
and inode bytes across its actual seal releases and last keeper callback.
Cached extents determine the requested seal lengths. The marker bounds the
keeper prefix even if its inode has a longer visible tail. -/
theorem MarkedTemporaryReadCalls.restoresSelectedWalBytes
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    (scopedReads : calls.ScopeFrames (frames))
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit)
    (remembers : ∀ {path file before after}, remember path file before = .ok () after → (frames) before after)
    {through : Nat} {initial entry : heap} {required : List (Nat × IO.FS.Metadata)}
    (inScope : ∀ extent ∈ required, scope (directory.file (.walSegment extent.1)))
    (starts : (frames) initial entry)
    {result : EStateM.Result IO.Error heap (List (Nat × ByteArray) × Nat)}
    (observed : CachedWalPayloadReturn directory through calls.seal (calls.readKeeperWithRelease remember)
      required entry result)
    {files : List (Nat × ByteArray)} {size : Nat} {reached : heap}
    (returned : result = .ok (files, size) reached) :
    let sealBytes := fun extent : Nat × IO.FS.Metadata =>
      (names initial (directory.file (.walSegment extent.1))).map fun inode =>
        (extent.1, (visible initial inode).extract 0 extent.2.byteSize.toNat)
    ∃ (keeper : Nat) (metadata : IO.FS.Metadata) (earlier : List (Nat × ByteArray)) (bytes : ByteArray)
      (beforeKeeper opened readHeap : heap) (file : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat),
      required.getLast? = some (keeper, metadata) ∧ required.dropLast.mapM sealBytes = some earlier ∧
      files = earlier ++ [(keeper, bytes)] ∧ size = metadata.byteSize.toNat ∧
      names initial (directory.file (.walSegment keeper)) = some inode ∧
      calls.openRead (directory.file (.walSegment keeper)) beforeKeeper = .ok file opened ∧
      attachedReadSlot view file slot inode readHeap ∧
      bytes = (visible initial inode).extract 0 ((through - keeper) * WAL.frameSize) ∧
      (let count := (through - keeper) * WAL.frameSize
       (count = size ∧ remember (directory.file (.walSegment keeper)) file readHeap = .ok () reached) ∨
        (count < size ∧ calls.release file readHeap = .ok () reached)) ∧
      (frames) initial beforeKeeper ∧ (frames) initial reached := by
  have refl (atHeap : heap) : (frames) atHeap atHeap := fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  induction observed generalizing files size reached with
  | noKeeper _ | keeperError _ | invalidKeeper _ _ | invalidOrder _ | sealError _ _ | sealedThenError _ _ _ =>
    cases returned
  | @kept keeper metadata entry reachedRead keeperBytes read checked =>
    obtain ⟨payload, rfl⟩ := EStateM.Result.ok.inj returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj payload
    let path := directory.file (.walSegment keeper)
    let count := (through - keeper) * WAL.frameSize
    let mismatch := IO.userError "short or oversized WAL keeper read"
    obtain ⟨file, opened, readHeap, _, _, acquired, payloadRead, closed⟩ :=
      calls.readKeeperWithRelease_ok remember path count metadata.byteSize.toNat read
    obtain ⟨slot, inode, named, _, live, _, sameBytes, payload⟩ :=
      calls.readExactOpenedFile view names visible opens reads path mismatch count acquired payloadRead
    have selected : scope path := inScope (keeper, metadata) (List.mem_singleton_self _)
    obtain ⟨sameName, beforeBytes⟩ := starts path selected
    have original := sameName.symm.trans named
    have visibleAtRead := sameBytes.trans (List.cons.inj (beforeBytes _ original)).1
    have keeperFrame := calls.readKeeperKeepsFrame scopedReads refl CheckpointSurvivingFiles.Frames.trans
      remember remembers path count metadata.byteSize.toNat read
    refine ⟨keeper, metadata, [], keeperBytes, entry, opened, readHeap, file, slot, inode, rfl, rfl, rfl, rfl,
      original, acquired, live, ?_, closed, starts, starts.trans keeperFrame⟩
    rwa [visibleAtRead] at payload
  | @sealed first next metadata nextMetadata rest entry afterSeal reachedRead sealBytes restFiles fileSize forward read tail ih =>
    obtain ⟨payload, rfl⟩ := EStateM.Result.ok.inj returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj payload
    let path := directory.file (.walSegment first)
    let count := (next - first) * WAL.frameSize
    cases read with
    | accepted sized fits readSeal exactSize =>
      obtain ⟨extent, atEntry⟩ := EStateM.Result.ok.inj sized
      subst atEntry
      obtain ⟨file, slot, inode, opened, readHeap, _, named, _, _, _, stable, bytes, _⟩ :=
        calls.readSelectedSeal view names visible opens reads path count readSeal
      have selected : scope path := inScope (first, metadata) List.mem_cons_self
      obtain ⟨sameName, contents⟩ := starts path selected
      have namedInitially : names initial (directory.file (.walSegment first)) = some inode := sameName.symm.trans named
      change metadata.byteSize.toNat = count at extent
      have exactPrefix : sealBytes = (visible initial inode).extract 0 metadata.byteSize.toNat := by
        rw [stable, (List.cons.inj (contents _ namedInitially)).1, ← extent] at bytes
        exact bytes
      have sealedFrame := calls.readSealKeepsFrame scopedReads refl CheckpointSurvivingFiles.Frames.trans
        path count readSeal
      obtain ⟨keeper, keeperMetadata, earlier, bytes, beforeKeeper, opened, readHeap, file, slot, inode, last, sealed,
        exactFiles, size, bound, acquired, live, keeperPrefix, closed, beforeFrame, frame⟩ :=
        ih (fun extent member => inScope extent (List.mem_cons_of_mem _ member)) (starts.trans sealedFrame) rfl
      refine ⟨keeper, keeperMetadata, (first, sealBytes) :: earlier, bytes, beforeKeeper, opened, readHeap, file, slot, inode,
        ?_, ?_, congrArg (List.cons (first, sealBytes)) exactFiles, size, bound, acquired, live, keeperPrefix, closed,
        beforeFrame, frame⟩
      · simpa only [List.getLast?_cons_cons] using last
      · simp only [List.dropLast_cons_cons, List.mapM_cons, namedInitially, Option.map_some, ← exactPrefix,
          sealed, Bind.bind, Option.bind, Pure.pure]

end VisibleWal

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {beforeKeeper : heap}

/-- The scoped keeper callback uses the same bounded open and chunk
reads, then returns on the observed post-release heap. -/
theorem NativeLongKeeperReadHeap.readsScoped (seen : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit) :
    fileCalls.readKeeperWithRelease remember (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper =
        .ok layout.keeper.bytes seen.closed := by
  have prefixRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (fileCalls.readChunk seen.raw.file) layout.keeper.bytes.size ByteArray.empty seen.raw.opened =
        .ok layout.keeper.bytes seen.raw.finished := seen.raw.readRaw
  simp [MarkedTemporaryReadCalls.readKeeperWithRelease, readKeeperWith, Bind.bind, EStateM.bind,
    Nat.le_of_lt finish.longer, reads.wal.keeperFits, finish.longer, Nat.ne_of_lt finish.longer,
    seen.raw.openedRaw, prefixRead, seen.raw.releasedRaw, Pure.pure, EStateM.pure]

variable {stream : Type} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {chronology : CapturedMarkedReadCensus reads finish.reader}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
  {callbacks : AlignedKeeperCacheCallbacks heap}
  {read : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper}
  {authorization : NativeLongKeeperAuthorizationHeap read (callbacks.withFileReads fileCalls)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {suffix : NativeLongKeeperSuffixHeap authorization remove} {stage : LongKeeperStageCallbacks heap}
  {staged : NativeLongKeeperFreshStageHeap suffix stage} {names : heap → FilePath → Option Nat}
  {synced : NativeLongKeeperStagedSyncHeap staged names}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {renamed : NativeLongKeeperRenameHeap synced rename}

/-- The held worker reads the same selected checkpoint, marker and WAL
bytes as chronological recovery. Its longer keeper read releases the
original handle, and replay leaves that heap for the replacement. The
healthy fresh-stage route returns the same recovered value and settled
files, inventory and cache. -/
theorem NativeLongKeeperSettlementHeap.recoversFromOpenedCache
    (seen : NativeLongKeeperSettlementHeap renamed)
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (bootstrap : EStateM IO.Error heap Reopened) :
    let keeper := callbacks.withFileReads fileCalls
    let remember := fun path file => keeper.modifyPending seed.pendingRef (pushPending path file)
    let write := stage.stage seed.pendingRef keeper.modifyPending
    let grouped := keeper.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    ∃ opened,
      recoverSegmentedWalWith
        (rejectFlatWalWith directory (optionalMetadataWith (fileCalls.stat (directory.file .wal))))
        (optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)))
        (reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
          fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
          fileCalls.seal (fileCalls.readKeeperWithRelease remember) remove write grouped rename)
        bootstrap seed.afterPending = .ok opened seen.reached ∧
      finish.recoverFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
        directory admission.cache (admission.reached, admission.held) =
          .ok opened (view.descriptors seen.reached, view.files seen.reached) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  intro keeper remember write grouped
  obtain ⟨opened, ran, projected⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered flat marker
    (fileCalls.readKeeperWithRelease remember) (read.readsScoped remember) remove write grouped rename seen.returns.ran bootstrap
  obtain ⟨captured, samePreparation, normalized⟩ :=
    finish.recoversWithSelectedPreparation chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  have physical := seen.returns.final
  refine ⟨opened, ran, ?_, congrArg Prod.fst physical⟩
  rw [show (view.descriptors seen.reached, view.files seen.reached) = (finish.census, finish.settled) from
    congrArg Prod.snd physical]
  exact normalized

end Alvoki.Storage.DiskSession
