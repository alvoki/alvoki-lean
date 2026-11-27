import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativeReadyCallRefinement

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
      ∀ (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
        (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
        (rename : FilePath → FilePath → EStateM IO.Error heap Unit),
        let writes := start.readyWriteCalls refs appender stager syncer lookup rename
        ∀ (issuer : handle.LatestIssuer) (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
          (_reported : writes.ReturnEffects view inodes runs observe inode buffered)
          {calls : List (NativeReturnedCall handle)} {reached : heap},
          NativeReturnedCalls writes issuer returnedAt [] calls reached →
          NativeReturnedCalls.ReadyResponses calls →
          ∃ (last : NativeOpenedPosition handle) (events : List NativeExecutionEvent),
            last.reached = reached ∧
            last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins call => call.pinsAfter pins) [] ∧
            writes.StorageAt view observe (fun atHeap => (inodes atHeap).visible) last ∧
            events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
            origin.LedgerSuffix (earlier ++ events) last.current ∧
            InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
              last.current.ready.state.writer.installed last.current.ready.state.session ∧
            ∀ extra, (∀ offset ∈ writer.wal.segments.map WalSegment.first, lower ≤ offset) →
              writes.WalWindowEffects observe lower
                (writer.history.length + (calls.map NativeReturnedCall.requestedRows).sum + extra) →
              last.WalWindowAt observe lower (last.current.history.length + extra)

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
  · intro appender stager syncer lookup rename writes issuer inode buffered reported calls reached executed covered
    have initial : writes.StorageAt view observe (fun atHeap => (inodes atHeap).visible) start := writeEntry
    obtain ⟨last, events, heap, pins, physical, length, records, ledger, budget, frames⟩ :=
      executed.refinesReadyFramed covered view inodes runs observe inode buffered reported start sameHeap
        (by rw [emptyPins]; rfl) initial
    refine ⟨last, events, heap, pins, physical, length, records, across.append ledger,
      last.current.ready.readPrefix.guardedReplay, ?_⟩
    intro extra covers names
    have fromOpen : start.WalWindowAt observe lower
        (writer.history.length + (calls.map NativeReturnedCall.requestedRows).sum + extra) := by
      constructor
      · rw [stateEq]
        exact covers
      · rw [sameHeap]
        exact installedWindow _
    exact (frames names fromOpen).restrictUpper
      (by simpa only [startHistory, OpenReferenceAllocations.readyState] using Nat.add_le_add_right budget extra)

/-- Continue from one retained WAL namespace through the literal open and
start supported calls on the allocated table. The repair and allocation
laws are indexed by the exact cache and keeper reached by the open. -/
abbrev RawMarkedOpenInterpreter.WritesAfterWalOpen
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream) (view : OpenCloseHeapView heap FileImage)
    (directory : DiskDirectory) (writer : SegmentedWriterState) (entry : heap)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (origin : NativeExecutionPosition) (earlier : List NativeExecutionEvent)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage) (observe : heap → CheckpointStorageObservation) : Prop :=
  let names := fun atHeap => (observe atHeap).files.names
  let visible := fun atHeap => (inodes atHeap).visible
  let scope := writer.walOpenDurablePath directory
  ∀ (_pairAt : (view.files entry).image.directory.active =
      ⟨(names entry (directory.file .manifest)).map (visible entry),
        (names entry (directory.file .walBoundary)).map (visible entry)⟩)
    (_keeperAt : (view.files entry).image.keeper.active =
      (names entry (directory.file (.walSegment writer.wal.active.first))).map (visible entry))
    (_sealsAt : (view.files entry).image.kept = (writer.wal.checkpointReopenFiles writer.wal.directory none).kept)
    (_suffix : ∀ ordinal ∈ (view.files entry).image.later.visible, writer.history.length < ordinal ∧
      ∃ object, namespaceView.child root (renderWalSegmentName ordinal) = some object)
    (_complete : ∀ ordinal, writer.history.length < ordinal →
      (∃ inode, names entry (directory.file (.walSegment ordinal)) = some inode) →
      ∃ object, namespaceView.child root (renderWalSegmentName ordinal) = some object)
    {input : FilePath} (_admission : source.ObservedAdmissionEffects view directory scope input entry observe visible)
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
        (_laterAbsent : ∀ {before entries listed}, source.directoryCalls.run directory.path before = .ok entries listed →
          (⟨names entry, fun inode => [visible entry inode]⟩ : CheckpointSurvivingFiles).Frames
            (managedPath directory) ⟨names listed, fun inode => [visible listed inode]⟩ →
          MarkedWalExtentReports.TruthfulAbsenceOn (writer.history.length < ·) source.fileCalls directory
            namespaceView root (entries.toList.map (·.fileName)) listed)
        (_repair : source.ObservedAlignedRepairEffects (view := view) cache directory layout entry observe visible)
        (_allocates : source.LiteralAllocationEffects view directory cache observe visible layout.keeper.first),
        ∃ (repaired : heap) (reopened : SegmentedWriterState)
          (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase reopened.installed repaired),
          source.AlignedReadyCalls input entry returnedAt table directory cache view reopened allocation phaseIdentity tokenIdentity
            origin earlier inodes runs observe 0

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
  intro pairAt keeperAt sealsAt suffix complete input admission returnedAt table returned
    phaseIdentity tokenIdentity get set phaseEffects ptrEq
  obtain ⟨layout, target, keeper, aligned, wal, following⟩ := files.alignedLayout ready missing pairAt keeperAt
  obtain ⟨inode, lock⟩ := files.lock
  obtain ⟨cache, frame, authority, rootNamed, lockNamed, _, _, worker⟩ := source.reachesAlignedCache admission lock returned
  refine ⟨layout, cache, target, keeper, authority, ?_⟩
  intro reads child laterAbsent repair allocates
  have absent := (congrArg (fun target : Target => target.pair.manifest) target).trans missing
  have marker := files.marker.trans (congrArg (fun target : Target => target.pair.walBoundary) target).symm
  have literal := (source.readsLiteralWalOnly layout cache absent files.manifest marker
    observedOpenReadFrame.refl (fun first last => first.trans last) (frame.entersReader authority) reads following
    (fun start _ bound => child start (layout.through ▸ bound))
    (fun {before entries listed} scan kept => by
      rw [layout.through]
      exact @laterAbsent before entries listed scan kept) wal worker).1
  have completeLater (start : Nat) (beyond : layout.range.through < start)
      (found : ∃ inode, names entry (directory.file (.walSegment start)) = some inode) :
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object :=
    complete start (layout.through ▸ beyond) found
  let published : CheckpointPublication.Image := ⟨.settled none, fun _ _ => none⟩
  obtain ⟨repaired, reopened, allocation, installed, ⟨seen⟩⟩ :=
    source.retainsLiteralAlignedReturn directory layout
      (layout.walOnlyCheckpoint (durable := published.durable) absent) (layout.walOnlyAccepted published absent)
      ready.resumed.ordered ready.layout ready.valid ready.spans (ready.walPair.trans (congrArg Target.pair target).symm)
      (congrArg WalSegment.first keeper) aligned cache authority observe visible namespaceView root scope literal rfl
      (by simpa only [CanonicalKeeperLayout.target, aligned, ByteArray.append_empty] using layout.visible)
      sealsAt (fun start member => (suffix start member).imp_left (fun beyond => layout.through.symm ▸ beyond))
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
  exact ⟨repaired, reopened, allocation, installed.refinesReadyCalls returned sameHistory prior inodes runs observe
    namespaceView root seen repair allocates protectedFiles atMarker stable.parentSettled aligned keeper atKeeper
    (fun start low high => files.catalog start low (layout.through ▸ high)) bounded completeLater phaseEffects ptrEq⟩

end WalOnly

end Alvoki.Storage.DiskSession
