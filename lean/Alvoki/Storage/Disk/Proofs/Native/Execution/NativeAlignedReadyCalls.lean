import Alvoki.Storage.Disk.Proofs.Write.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyCallRefinement

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage}
  {entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}

/-- The postcondition of an actual aligned reopen followed by supported
ready calls on its returned table. -/
abbrev RawMarkedOpenInterpreter.AlignedReadyCalls
    (source : RawMarkedOpenInterpreter heap stream) (input : FilePath) (entry returnedAt : heap) (table : DiskTable)
    (directory : DiskDirectory) (cache : HeldOpenCache heap) (view : OpenCloseHeapView heap FileImage)
    {repaired : heap} (writer : SegmentedWriterState)
    (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (origin : NativeExecutionPosition) (earlier : List NativeExecutionEvent)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation) (lower : Nat) : Prop :=
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (refs : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      source.openTable input entry = .ok handle.table start.reached ∧ handle.table = table ∧ start.reached = returnedAt ∧
      (handle.phase, handle.token) = (allocation.phase, allocation.token) ∧ start.pins = [] ∧
      (refs.directory, refs.active, refs.pending) = (cache.directoryRef, cache.activeRef, cache.pendingRef) ∧
      start.current.ready.state = allocation.readyState writer directory cache.owner cache.rootSlot
        cache.directoryRef cache.activeRef cache.pendingRef phaseIdentity tokenIdentity ∧
      origin.LedgerSuffix earlier start.current ∧
      start.WriteStorageEntry view refs (observe returnedAt) (inodes returnedAt).visible ∧
      (∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow start.current.ready.state.session.directory
        lower through (observe returnedAt)) ∧
      start.ContinuesReadyCalls refs view inodes runs observe origin earlier lower

/-- Start the common ready-call induction on the exact table returned by
an aligned open. The previous client ledger survives the reopen, while
its old pins do not enter the newly allocated handle. -/
theorem RawMarkedOpenInterpreter.LiteralAlignedReturn.refinesReadyCalls
    {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} {published : CheckpointPublication.Image}
    {checkpoint : Option (PackedTable × UInt64)} {wal : WalSegmentImage} {cache : HeldOpenCache heap}
    {writer : SegmentedWriterState} {repaired returnedAt : heap} {table : DiskTable}
    {allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired}
    (installed : source.LiteralAlignedReturn directory layout published checkpoint wal cache view
      phaseIdentity tokenIdentity writer allocation returnedAt table)
    (returned : source.openTable input entry = .ok table returnedAt)
    {previous origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (sameHistory : history = previous.history) (priorLedger : origin.LedgerSuffix earlier previous)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) {readScope : FilePath → Prop}
    (seen : source.LiteralAlignedSyncs directory layout cache view observe (fun atHeap => (inodes atHeap).visible)
      namespaceView root readScope entry repaired)
    (physical : source.ObservedAlignedRepairEffects (view := view) cache directory layout entry observe
      (fun atHeap => (inodes atHeap).visible))
    (allocates : source.LiteralAllocationEffects view directory cache observe (fun atHeap => (inodes atHeap).visible)
      layout.keeper.first)
    (protectedFiles : NativeReadyProtectedStorage
      (allocation.readyState writer directory cache.owner cache.rootSlot cache.directoryRef cache.activeRef cache.pendingRef
        phaseIdentity tokenIdentity) (observe seen.prepared).files)
    (marker : (observe seen.prepared).files.Stored (directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe seen.prepared).crashNames,
      names directory.path = (observe seen.prepared).files.names directory.path)
    (aligned : layout.tail = .empty) (keeper : layout.keeper = wal.active)
    (keeperAtEntry : ((observe entry).files.names (directory.file (.walSegment layout.keeper.first))).map
      (inodes entry).visible = some (layout.keeper.bytes ++ layout.tail))
    {lower : Nat}
    (window : wal.NamespaceWindow directory lower layout.range.through (observe entry).files.names)
    (boundedStarts : ∀ start ∈ wal.segments.map WalSegment.first, start ≤ layout.range.through)
    (laterComplete : ∀ start, layout.range.through < start →
      (∃ inode, (observe entry).files.names (directory.file (.walSegment start)) = some inode) →
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object)
    (effects : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    source.AlignedReadyCalls input entry returnedAt table directory cache view writer allocation phaseIdentity tokenIdentity
      origin earlier inodes runs observe lower := by
  unfold RawMarkedOpenInterpreter.AlignedReadyCalls
  let files := RawMarkedOpenInterpreter.makeCache directory cache.directoryRef cache.activeRef cache.pendingRef
  let state := allocation.readyState writer directory cache.owner cache.rootSlot
    cache.directoryRef cache.activeRef cache.pendingRef phaseIdentity tokenIdentity
  obtain ⟨valid, authority, history, _, _, _, walEq, tableEq, _, tokenHeap, _, _, _, _, _, _⟩ := installed
  have activeKeeper : writer.wal.active = layout.keeper :=
    (congrArg WalSegmentImage.active walEq).trans keeper.symm
  have keeperBytes : (inodes entry).visible seen.inode = writer.wal.active.bytes := by
    rw [seen.named, Option.map_some, aligned, ByteArray.append_empty, ← activeKeeper] at keeperAtEntry
    exact Option.some.inj keeperAtEntry
  have exactWindow : writer.wal.NamespaceWindow directory lower layout.range.through (observe entry).files.names := by
    rw [walEq]
    exact window
  have allBounded : ∀ start ∈ writer.wal.segments.map WalSegment.first, start ≤ layout.range.through := by
    rw [walEq]
    exact boundedStarts
  obtain ⟨settled, live, _, repairedWindow⟩ := seen.readyStorage valid rfl rfl rfl
    (congrArg WalSegment.first activeKeeper) authority physical protectedFiles marker rootSettled
    keeperBytes exactWindow allBounded laterComplete
  have carriedHistory : state.writer.history = previous.history := history.trans sameHistory
  have replay : PendingClientReplay previous.submissions previous.ready.reads state.writer.history := by
    rw [carriedHistory]
    exact previous.ready.readPrefix.refines.2.2
  have bounded : ∀ read ∈ previous.ready.reads, read.BoundedBy state.writer.history.length := by
    rw [carriedHistory]
    exact previous.ready.readPrefix.readsBounded
  have exactReturn : source.openTable input entry =
      .ok (RawMarkedOpenInterpreter.assemble directory cache.lock files allocation.phase allocation.token) allocation.afterToken := by
    rw [returned, tableEq, tokenHeap]
  obtain ⟨uses, atDirectory⟩ := RawMarkedOpenInterpreter.cacheReferences directory cache.directoryRef cache.activeRef cache.pendingRef
  let refs : OpenSyncCacheRefs files directory.path :=
    ⟨cache.directoryRef, cache.activeRef, cache.pendingRef, uses, atDirectory⟩
  obtain ⟨_, phaseCache, phaseFiles, phaseVisible⟩ := allocates.allocatesPhase allocation.phaseAllocated
  obtain ⟨_, tokenCache, tokenFiles, tokenVisible⟩ := allocates.allocatesToken allocation.tokenAllocated
  obtain ⟨handle, start, nextCache, opened, reached, references, cacheRefs, startHistory, submissions, stateEq,
    reads, _, writeEntry, emptyPins⟩ := allocation.opensReadyWriter valid
      (RawMarkedOpenInterpreter.assembles directory cache.lock files) refs exactReturn effects ptrEq
      replay bounded observe (fun atHeap => (inodes atHeap).visible) settled live rfl authority.ownerAttached.1 rfl
      phaseCache tokenCache ⟨cache.captured, authority.cacheRoot⟩
      (phaseFiles.weaken fun _ path => NativeReadyState.crashPath_rootOrChild (state := state) path)
      (tokenFiles.weaken fun _ path => NativeReadyState.crashPath_rootOrChild (state := state) path)
      (fun inode named => phaseVisible inode (by simpa only [OpenReferenceAllocations.readyState, activeKeeper] using named))
      (fun inode named => tokenVisible inode (by simpa only [OpenReferenceAllocations.readyState, activeKeeper] using named))
  obtain ⟨sameTable, sameHeap⟩ := EStateM.Result.ok.inj (opened.symm.trans returned)
  have unchanged : previous.LedgerSuffix [] start.current :=
    ⟨by simpa using startHistory.trans carriedHistory, by simpa using submissions, by simpa using reads, by simp⟩
  have across : origin.LedgerSuffix earlier start.current := by
    simpa only [List.append_nil] using priorLedger.append unchanged
  have installedWindow (through : Nat) :
      start.current.ready.state.writer.wal.SettledNamespaceWindow start.current.ready.state.session.directory
        lower through (observe returnedAt) := by
    have readyWindow := repairedWindow through
    rw [stateEq, ← tokenHeap]
    exact allocation.walWindowAfterAllocations observe writer.wal directory readyWindow.1 readyWindow.2
      (fun _ => WalNamePresenceFrame.ofStorageFrame phaseFiles (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
      (fun _ => WalNamePresenceFrame.ofStorageFrame tokenFiles (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
  refine ⟨handle, start, nextCache, opened, sameTable, sameHeap, references, emptyPins, cacheRefs, stateEq,
    across, ?_, installedWindow, ?_⟩
  · simpa only [← sameHeap] using writeEntry
  · apply start.continuesReadyCalls nextCache view inodes runs observe origin earlier lower emptyPins across writeEntry
    simpa only [sameHeap] using installedWindow

/-- Repair can unlink canonical names from the captured listing. Looking up
each candidate again at the reached heap reflects an accepted removal. -/
def OpenCloseHeapView.withLaterWalFromScan (view : OpenCloseHeapView heap FileImage)
    (directory : DiskDirectory) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (through : Nat) (bindings : heap → FilePath → Option Nat) : OpenCloseHeapView heap FileImage :=
  view.withFileProjection fun atHeap =>
    let files := view.files atHeap
    let later := (namespaceView.laterWalStarts root through).filter fun start =>
      (bindings atHeap (directory.file (.walSegment start))).isSome
    { files with image.later.visible := later }

/-- Continue from one retained WAL namespace through the literal open and
start supported calls on the allocated table. The repair and allocation
laws are indexed by the exact cache and keeper reached by the open.
Bounded absence at entry makes the same attempt skip suffix pruning
when its complete held listing has no candidates above the bound. -/
abbrev RawMarkedOpenInterpreter.WritesAfterWalOpen
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream) (view : OpenCloseHeapView heap FileImage)
    (directory : DiskDirectory) (writer : SegmentedWriterState) (entry : heap)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (origin : NativeExecutionPosition) (earlier : List NativeExecutionEvent)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage) (observe : heap → CheckpointStorageObservation) : Prop :=
  let names := fun atHeap => (observe atHeap).files.names
  let visible := fun atHeap => (inodes atHeap).visible
  let scope := writer.walOpenDurablePath directory
  let view := (view.withObservedWalFiles directory writer.wal.active.first names visible).withLaterWalFromScan
    directory namespaceView root writer.history.length names
  ∀ {input : FilePath} (_admission : source.ObservedAdmissionEffects view directory scope input entry observe visible)
    {returnedAt : heap} {table : DiskTable} (_returned : source.openTable input entry = .ok table returnedAt)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (_phaseEffects : OpenPhaseCellEffects view.phase get set)
    (_ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
    ∃ (layout : CanonicalKeeperLayout (view.files entry).image writer.history) (cache : HeldOpenCache heap),
      layout.target = writer.target ∧ layout.keeper = writer.wal.active ∧ LiteralOpenAuthority view directory cache cache.ready ∧
      ∀ (_reads : source.AlignedReadEffects view directory cache.pendingRef names visible namespaceView root
          (managedPath directory) (observedOpenReadFrame view directory scope cache observe))
        (_child : ∀ start ≤ writer.history.length,
          (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
            names entry (directory.file (.walSegment start)))
        (_physicalScan : source.directoryCalls.ObservesWalNames directory _reads.streamObject root names
          (writer.history.length < ·))
        (_repair : source.ObservedAlignedRepairEffects (view := view) cache directory layout entry observe visible)
        (_allocates : source.LiteralAllocationEffects view directory cache observe visible layout.keeper.first),
        ∃ (repaired : heap) (reopened : SegmentedWriterState)
          (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase reopened.installed repaired),
          source.AlignedReadyCalls input entry returnedAt table directory cache view reopened allocation phaseIdentity tokenIdentity
            origin earlier inodes runs observe 0 ∧
          ∀ horizon, (∀ start ∈ namespaceView.laterWalStarts root writer.history.length, start ≤ horizon) →
            (∀ start, writer.history.length < start → start ≤ horizon →
              names entry (directory.file (.walSegment start)) = none) →
            ∃ seen : source.LiteralAlignedSyncs directory layout cache view observe visible namespaceView root scope entry repaired,
              seen.newer = [] ∧ seen.keeperEntry = seen.authorized

section WalOnly

variable {directory : DiskDirectory} {writer : SegmentedWriterState} {descriptor : Nat}
  {namespaceView : DirectoryReadNamespace} {root : DeviceInode}
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage) (observe : heap → CheckpointStorageObservation)

local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (observe atHeap))
local notation "visible" => fun atHeap => WalInodeImage.visible (inodes atHeap)
local notation "scope" => writer.walOpenDurablePath directory

/-- The literal successful WAL-only open selects the aligned keeper,
repairs its actual held cache and installs a writer with the incoming
client ledger. The same returned handle starts the ready-call induction. -/
theorem RawMarkedOpenInterpreter.opensRetainedWalForCalls
    (ready : writer.RetainedReady directory descriptor) (missing : writer.target.pair.manifest = none)
    (files : writer.VisibleWalFiles directory (names entry) (visible entry))
    (durable : writer.WalOpenDurability directory (observe entry))
    {previous origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (sameHistory : writer.history = previous.history) (prior : origin.LedgerSuffix earlier previous) :
    source.WritesAfterWalOpen view directory writer entry namespaceView root origin earlier inodes runs observe := by
  intro input admission returnedAt table returned
    phaseIdentity tokenIdentity get set phaseEffects ptrEq
  let projected := (view.withObservedWalFiles directory writer.wal.active.first names visible).withLaterWalFromScan
    directory namespaceView root writer.history.length names
  obtain ⟨layout, target, keeper, aligned, wal, following⟩ :=
    files.alignedLayout (image := (projected.files entry).image) ready missing rfl rfl
  have sealsAt : (projected.files entry).image.kept = (writer.wal.checkpointReopenFiles writer.wal.directory none).kept :=
    files.keptWalFromNames ready
  obtain ⟨inode, lock⟩ := files.lock
  obtain ⟨cache, frame, authority, rootNamed, lockNamed, _, _, worker⟩ := source.reachesAlignedCache admission lock returned
  refine ⟨layout, cache, target, keeper, authority, ?_⟩
  intro reads child physicalScan repair allocates
  have absent := (congrArg (fun target : Target => target.pair.manifest) target).trans missing
  have marker := files.marker.trans (congrArg (fun target : Target => target.pair.walBoundary) target).symm
  have laterAtScan {before listed : heap} {entries : Array IO.FS.DirEntry}
      (listedAt : source.directoryCalls.run directory.path before = .ok entries listed)
      (start : Nat) (later : layout.range.through < start) :
      (∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ↔
        (names listed (directory.file (.walSegment start))).isSome = true :=
    source.directoryCalls.liveWalChildren directory namespaceView root reads.streamObject physicalScan listedAt
      (fun _ _ opened => reads.streamRoot opened)
      (fun _ _ _ _ opened read closed => reads.complete opened read closed) start (layout.through ▸ later)
  obtain ⟨literal, ⟨_, listed, _, scan, entryToScan⟩⟩ := source.readsLiteralWalOnly layout cache absent files.manifest marker
    observedOpenReadFrame.refl (fun first last => first.trans last) (frame.entersReader authority) reads following
    (fun start _ bound => child start (layout.through ▸ bound))
    (fun scanned _ => source.fileCalls.absenceOnFromNamePresence directory names visible namespaceView root
      (managedPath directory) (fun _ _ => ⟨rfl, fun _ _ => rfl⟩)
      (fun path before => (reads.statFrame path before).1) reads.statMissing
      (fun start _ => .inr ⟨.walSegment start, rfl⟩) (laterAtScan scanned)) wal worker
  have walNameAtScan (start : Nat) :
      names listed (directory.file (.walSegment start)) = names entry (directory.file (.walSegment start)) :=
    (entryToScan _ (.inr ⟨.walSegment start, rfl⟩)).1
  have completeLater (start : Nat) (beyond : layout.range.through < start)
      (found : ∃ inode, names entry (directory.file (.walSegment start)) = some inode) :
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object := by
    apply (laterAtScan scan start beyond).mpr
    rw [walNameAtScan]
    exact Option.isSome_iff_exists.mpr found
  have suffix (start : Nat) (member : start ∈ (projected.files entry).image.later.visible) :
      layout.range.through < start ∧ ∃ object, namespaceView.child root (renderWalSegmentName start) = some object := by
    rw [layout.through]
    exact (namespaceView.mem_laterWalStarts root writer.history.length start).mp (List.mem_filter.mp member).1
  let published : CheckpointPublication.Image := ⟨.settled none, fun _ _ => none⟩
  obtain ⟨repaired, reopened, allocation, installed, ⟨seen⟩⟩ :=
    source.retainsLiteralAlignedReturn directory layout
      (layout.walOnlyCheckpoint (durable := published.durable) absent) (layout.walOnlyAccepted published absent)
      ready.resumed.ordered ready.layout ready.valid ready.spans (ready.walPair.trans (congrArg Target.pair target).symm)
      (congrArg WalSegment.first keeper) aligned cache authority observe visible namespaceView root scope literal rfl
      (by simpa only [CanonicalKeeperLayout.target, aligned, ByteArray.append_empty] using layout.visible)
      sealsAt suffix
      repair.toLiteralAlignedFinishEffects allocates phaseIdentity tokenIdentity
  let state := allocation.readyState reopened directory cache.owner cache.rootSlot
    cache.directoryRef cache.activeRef cache.pendingRef phaseIdentity tokenIdentity
  have stable := durable.frame seen.storageFrame
  have installedFacts := installed
  obtain ⟨_, authorityAfter, historyAtRepair, _, targetAtRepair, _, walAtRepair, _⟩ := installedFacts
  have protectedFiles : NativeReadyProtectedStorage state (observe seen.prepared).files := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (seen.liveFrame _ (.inl rfl)).1.trans
        (rootNamed.trans (congrArg some authorityAfter.rootAttached.2.2.symm))
    · exact (seen.liveFrame _ (.inr ⟨.lock, rfl⟩)).1.trans
        (lockNamed.trans (congrArg some authorityAfter.ownerAttached.2.2.symm))
    · change match reopened.target.pair.manifest with | none => _ | some _ => _
      rw [targetAtRepair, absent]
      exact (seen.liveFrame _ (.inr ⟨.manifest, rfl⟩)).1.trans files.manifest
    · intro segment member
      have earlier : segment ∈ writer.wal.sealed := congrArg WalSegmentImage.sealed walAtRepair ▸ member
      exact stable.sealed segment earlier
    · intro payload metadata selected
      have absentAtRepair := (congrArg (fun target : Target => target.pair.manifest) targetAtRepair).trans absent
      change reopened.target.pair.manifest = some payload at selected
      rw [absentAtRepair] at selected
      contradiction
  have atMarker : (observe seen.prepared).files.Stored (directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode reopened.history).size.toUInt64) :=
    historyAtRepair.symm ▸ stable.marker
  have bounded (start : Nat) (member : start ∈ writer.wal.segments.map WalSegment.first) : start ≤ layout.range.through := by
    obtain ⟨segment, occurs, rfl⟩ := List.mem_map.mp member
    exact layout.through.symm ▸ ready.layout.firstAtOrBeforeEnd occurs
  have atKeeper : (names entry (directory.file (.walSegment layout.keeper.first))).map (visible entry) =
      some (layout.keeper.bytes ++ layout.tail) := by
    simpa only [keeper, aligned, ByteArray.append_empty] using files.active
  refine ⟨repaired, reopened, allocation, installed.refinesReadyCalls returned sameHistory prior inodes runs observe
    namespaceView root seen repair allocates protectedFiles atMarker stable.parentSettled aligned keeper atKeeper
    (fun start low high => files.catalog start low (layout.through ▸ high)) bounded completeLater phaseEffects ptrEq, ?_⟩
  intro horizon scanBound absentAtEntry
  have empty : seen.newer = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro start member
    obtain ⟨beyond, named⟩ := (seen.scanned start).mp member
    have cutoff := layout.through ▸ beyond
    have upper := scanBound start
      ((namespaceView.mem_laterWalStarts root writer.history.length start).mpr ⟨cutoff, named⟩)
    have present := (laterAtScan scan start beyond).mp named
    simp only [walNameAtScan, absentAtEntry start cutoff upper, Option.isSome_none, Bool.false_eq_true] at present
  exact ⟨seen, empty, by simpa only [empty, ite_true] using seen.pruned⟩

/-- Scoped file frames carry the selected WAL and bounded gaps across
failed attempts to the next entry. The literal lookup uses these visible
files. With durability at that entry, the writer also takes the client ledger. -/
theorem RawMarkedOpenInterpreter.FailedCalls.reopensSampledWal
    {rebooted : heap} {errors : List (FilePath × IO.Error)} {horizon : Nat}
    (attempts : source.FailedCalls rebooted errors entry)
    (ready : writer.RetainedReady directory descriptor) (missing : writer.target.pair.manifest = none)
    (bootFiles : writer.VisibleWalFiles directory (names rebooted) (visible rebooted))
    (covers : writer.history.length ≤ horizon)
    (effects : attempts.PreserveWalFiles (directory := directory) horizon names visible) :
    ((∀ start, writer.history.length < start → start ≤ horizon →
      names rebooted (directory.file (.walSegment start)) = none) →
      ∀ start, writer.history.length < start → start ≤ horizon →
        names entry (directory.file (.walSegment start)) = none) ∧
    source.ReplaysWalBeforeCheckpointAtOpen (view.withObservedWalFiles directory writer.wal.active.first names visible)
      directory writer.wal.active.first observe visible entry namespaceView root writer.history ∧
    ∀ {previous origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent},
      writer.history = previous.history → origin.LedgerSuffix earlier previous →
      writer.WalOpenDurability directory (observe entry) →
      source.WritesAfterWalOpen view directory writer entry namespaceView root origin earlier inodes runs observe := by
  have frame := attempts.visibleWalFrame (directory := directory) (bindings := names) (contents := visible) effects
  have files := bootFiles.frame ready.layout covers frame
  refine ⟨fun absent start past bound => (VisibleWalFrame.segment frame bound).1.trans (absent start past bound), ?_, ?_⟩
  · exact @RawMarkedOpenInterpreter.replaysRetainedWalAtOpen
      (source := source) (view := view) («storage» := observe) («visible» := visible) (entry := entry)
      (namespaceView := namespaceView) (root := root) (ready := ready) (missing := missing) (files := files)
  · intro previous origin earlier sameHistory prior durable
    exact @RawMarkedOpenInterpreter.opensRetainedWalForCalls
      (source := source) (view := view) (entry := entry) (namespaceView := namespaceView) (root := root)
      (inodes := inodes) (runs := runs) (observe := observe) (ready := ready) (missing := missing)
      (files := files) (durable := durable) (sameHistory := sameHistory) (prior := prior)

end WalOnly

end Alvoki.Storage.DiskSession
