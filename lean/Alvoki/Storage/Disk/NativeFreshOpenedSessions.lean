import Alvoki.Storage.Disk.NativeFreshTableOpen
import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.NativeEarlyCheckpointTerminal
import Alvoki.Storage.Disk.NativeReadyCallRefinement
import Alvoki.Storage.Disk.NativeRawWriteReboot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WAL.Boundary (WalInodeImage)

namespace NativeOpenedTrace

variable {heap : Type} {opened : NativeOpenedHandle heap} {start last : NativeOpenedPosition opened}

/-- The write instructions in a returned prefix already determine the
matching client instructions. Ack and preflight denial both retain the
request that was actually issued. -/
theorem writeInstructions (trace : NativeOpenedTrace start instructions events last)
    {requests : List WriteRequest}
    (asWrites : instructions = requests.map NativeOpenedInstruction.write) :
    NativeExecutionInstructions (requests.map NativeExecutionInstruction.write) events := by
  induction trace generalizing requests with
  | empty =>
    have empty : requests = [] := List.map_eq_nil_iff.mp asWrites.symm
    subst requests
    exact .empty
  | @step instructions events current instruction event reached prior report next earlier =>
    rcases List.eq_nil_or_concat requests with empty | ⟨previous, request, appended⟩
    · simp [empty] at asWrites
    · subst requests
      simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil] at asWrites ⊢
      obtain ⟨priorWrites, sameInstruction⟩ := List.append_inj' asWrites (by simp)
      have same := (List.cons.inj sameInstruction).1
      subst instruction
      have matched : (NativeExecutionInstruction.write request).Matches event := by
        cases report with
        | write =>
          obtain ⟨_, _, _, _, eventEq, _⟩ := next.returned
          rw [eventEq]
          rfl
        | writePreflight =>
          obtain ⟨_, _, _, _, _, eventEq, _⟩ := next.returned
          rw [eventEq]
          rfl
      exact .step (earlier priorWrites) matched

end NativeOpenedTrace

namespace FreshBootstrapOpenHeap.Returned

variable {heap : Type} {call : EStateM IO.Error heap DiskTable} {entry : heap}
  (opened : FreshBootstrapOpenHeap.Returned call entry)

/-- Source transitions and modeled traces share the empty ledgers
established by the fresh installer. -/
theorem refinesLedger (ledger : opened.start.current.LedgerSuffix events last) :
    last.history = events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
    InstalledClientReplay last.submissions last.ready.reads last.history
      last.ready.state.writer.installed last.ready.state.session := by
  exact ⟨by simpa only [opened.emptyHistory, List.nil_append] using ledger.history,
    by simpa only [opened.emptySubmissions, List.nil_append] using ledger.submissions,
    by simpa only [opened.emptyReads, List.nil_append] using ledger.reads,
    last.ready.readPrefix.guardedReplay⟩

theorem refinesTrace (trace : NativeExecutionTrace opened.start.current events last) :
    last.history = events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
    InstalledClientReplay last.submissions last.ready.reads last.history
      last.ready.state.writer.installed last.ready.state.session :=
  opened.refinesLedger trace.ledgerSuffix

private theorem freshEmptyWAL {state : NativeReadyState} (valid : state.Valid)
    (empty : state.writer.history = []) :
    state.writer.wal.active.first = 0 ∧ state.writer.wal.active.bytes = ByteArray.empty ∧ state.writer.wal.sealed = [] := by
  let wal := state.writer.wal
  have layout := valid.retained.layout
  have last : wal.active.last = 0 := by rw [layout.activeEnd, empty]; rfl
  have start : wal.active.first ≤ wal.active.last := layout.forward _ (List.mem_append_right _ (List.mem_singleton_self _))
  have first : wal.active.first = 0 := Nat.eq_zero_of_le_zero (last ▸ start)
  refine ⟨first, ?_, List.eq_nil_iff_forall_not_mem.mpr ?_⟩
  · rw [layout.activeBytes, empty, List.drop_nil]
    rfl
  · intro segment member
    have order := (List.pairwise_append.mp layout.ordered).2.2 segment member wal.active (List.mem_singleton_self _)
    exact Nat.not_lt_zero _ (first ▸ order.1)

private theorem renderWalSegmentName_ne_marker {name : String} (offset : Nat)
    (marker : name.toList[3]? = some '.') : renderWalSegmentName offset ≠ name := by
  intro equal
  have fourth := congrArg (fun child : String => child.toList[3]?) equal
  rw [marker] at fourth
  simp only [renderWalSegmentName, String.toList_append] at fourth
  change some '-' = some '.' at fourth
  exact (by decide : (some '-' : Option Char) ≠ some '.') fourth

private theorem walConflictsWhenNonzero {offset : Nat} (positive : offset ≠ 0) :
    WalSegmentRepair.conflictsWithBootstrap (renderWalSegmentName offset) = true := by
  have different : renderWalSegmentName offset ≠ renderWalSegmentName 0 := by
    intro equal
    apply positive
    exact Option.some.inj (by simpa only [parseWalSegmentName_render] using congrArg parseWalSegmentName equal)
  have starts : (renderWalSegmentName offset).startsWith "WAL-segment-" = true := by
    simp [renderWalSegmentName]
  simp [WalSegmentRepair.conflictsWithBootstrap, starts, different]


/-- The fresh listing rules out other canonical segments. The keeper
create, marker publication and installer retain their absence through
the requested window, including future offsets an append might reach. -/
theorem walNamespace {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory}
    {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {admitted : heap}
    {seed : OpenSyncCacheAllocations report.captured.opened view init admitted} {calls : FreshBootstrapCacheCalls heap}
    {raw : FreshBootstrapCacheChronology seed calls} (seen : FreshBootstrapOpenHeap report raw)
    (resolved : opened.handle.directory = directory) (observe : heap → CheckpointStorageObservation) (through : Nat)
    (createdKeeps : ∀ start, start ≠ 0 → seen.keeper.namespaceView.child report.captured.root (renderWalSegmentName start) =
      report.captured.view.child report.captured.root (renderWalSegmentName start))
    (children : ∀ start ≤ through,
      let stored := observe raw.markerDirectory.reached
      let path := directory.file (.walSegment start)
      let name := renderWalSegmentName start
      let object := report.marker.renamedView.modelObject
      stored.files.names path = (report.marker.renamedView.child report.captured.root name).map object ∧
      ∀ surviving ∈ stored.crashNames,
        surviving path ∈ (report.handoff.afterMarkerNames name).map (Option.map object))
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : WalSegmentRepair.Reopened).installed raw.markerDirectory.reached)
    (returnedAt : (opened.handle.phase, opened.handle.token, opened.start.reached) =
      (allocation.phase, allocation.token, allocation.afterToken))
    (phaseFrame : WalNamePresenceFrame directory 0 through (observe raw.markerDirectory.reached)
      (observe allocation.afterPhase))
    (tokenFrame : WalNamePresenceFrame directory 0 through (observe allocation.afterPhase)
      (observe allocation.afterToken)) :
    opened.start.WalWindowAt observe 0 through := by
  let state := opened.start.current.ready.state
  let stored := observe raw.markerDirectory.reached
  have directoryEq : state.session.directory = directory := opened.start.directory.trans resolved
  obtain ⟨valid, history, _⟩ := opened.start.current.ready.readPrefix.refines
  obtain ⟨first, _, seals⟩ := freshEmptyWAL valid (history.trans opened.emptyHistory)
  change state.writer.wal.active.first = 0 at first
  obtain ⟨_, _, keeperBinding, _, _, _, _, _, _, _, _, _, _⟩ := report.handoff.preservesKeeper
  have catalog : state.writer.wal.NamespaceWindow directory 0 through stored.files.names := by
    intro start _ upper
    obtain ⟨binding, _⟩ := children start upper
    change stored.files.names (directory.file (.walSegment start)) =
      (report.marker.renamedView.child report.captured.root (renderWalSegmentName start)).map _ at binding
    rw [binding, Option.isSome_map, WalSegmentImage.segments, seals]
    by_cases zero : start = 0
    · subst start
      simp [keeperBinding, first]
    · have missing : report.captured.view.child report.captured.root (renderWalSegmentName start) = none := by
        cases found : report.captured.view.child report.captured.root (renderWalSegmentName start) with
        | none => rfl
        | some child =>
          have listed := (report.captured.view.namesExact _ _).mpr ⟨child, found⟩
          exact False.elim (Bool.noConfusion ((report.listed.noConflict _ listed).symm.trans (walConflictsWhenNonzero zero)))
      rw [report.handoff.renameNames _ (renderWalSegmentName_ne_marker start rfl)
        (renderWalSegmentName_ne_marker start rfl),
        report.handoff.stageNames _ (renderWalSegmentName_ne_marker start rfl), seen.route]
      change (seen.keeper.namespaceView.child report.captured.root (renderWalSegmentName start)).isSome = true ↔ _
      rw [createdKeeps start zero, missing]
      simp [first, zero]
  have settled (names) (survives : names ∈ stored.crashNames) (start : Nat) (_ : 0 ≤ start) (upper : start ≤ through) :
      (names (directory.file (.walSegment start))).isSome =
        (stored.files.names (directory.file (.walSegment start))).isSome := by
    obtain ⟨binding, chosen⟩ := children start upper
    have same := chosen names survives
    rw [report.handoff.markerSettlement, List.map_singleton, List.mem_singleton, ← binding] at same
    exact congrArg Option.isSome same
  refine ⟨fun offset _ => Nat.zero_le offset, ?_⟩
  change state.writer.wal.NamespaceWindow state.session.directory 0 through (observe opened.start.reached).files.names ∧
    ∀ names ∈ (observe opened.start.reached).crashNames,
      state.writer.wal.NamespaceWindow state.session.directory 0 through names
  have reached : opened.start.reached = allocation.afterToken := congrArg (fun result => result.2.2) returnedAt
  rw [directoryEq, reached]
  have allocated := phaseFrame.trans tokenFrame
  exact allocated.preservesNamespaceWindow ⟨catalog, fun names survives => catalog.frame (settled names survives)⟩

/-- The fresh public open starts with settled storage and visible empty
keeper bytes on its returned heap. The keeper create frames the listed
lock and absent manifest. The final directory barrier supplies the child
bindings, and installing the phase and token preserves those files. -/
theorem readyStorage {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory}
    {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {admitted : heap}
    {seed : OpenSyncCacheAllocations report.captured.opened view init admitted} {calls : FreshBootstrapCacheCalls heap}
    {raw : FreshBootstrapCacheChronology seed calls} (seen : FreshBootstrapOpenHeap report raw)
    (resolved : opened.handle.directory = directory)
    {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (observe : heap → CheckpointStorageObservation)
    (createdKeeps : ∀ name ∈ ["LOCK", "MANIFEST"],
      seen.keeper.namespaceView.child report.captured.root name = report.captured.view.child report.captured.root name)
    (rootNames : let stored := observe raw.markerDirectory.reached
      stored.files.names directory.path = some (report.captured.view.modelObject report.captured.root) ∧
      ∀ names ∈ stored.crashNames, names directory.path = stored.files.names directory.path)
    (children : ∀ name ∈ ["LOCK", "MANIFEST", renderWalSegmentName 0, "WAL.commit"],
      let stored := observe raw.markerDirectory.reached
      let path : FilePath := ⟨directory.path.toString ++ "/" ++ name⟩
      let object := report.marker.renamedView.modelObject
      stored.files.names path = (report.marker.renamedView.child report.captured.root name).map object ∧
      ∀ names ∈ stored.crashNames, names path ∈ (report.handoff.afterMarkerNames name).map (Option.map object))
    (inodeBytes : (observe raw.markerDirectory.reached).files.bytes =
      (seen.keeperPhysical.inodes raw.markerDirectory.reached).crashBytes)
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : WalSegmentRepair.Reopened).installed raw.markerDirectory.reached)
    (returnedAt : (opened.handle.phase, opened.handle.token, opened.start.reached) =
      (allocation.phase, allocation.token, allocation.afterToken))
    (phaseFrame : (observe raw.markerDirectory.reached).Frames opened.start.current.ready.state.crashPath
      (observe allocation.afterPhase))
    (tokenFrame : (observe allocation.afterPhase).Frames opened.start.current.ready.state.crashPath
      (observe allocation.afterToken))
    (phaseInodes : seen.keeperPhysical.inodes allocation.afterPhase =
      seen.keeperPhysical.inodes raw.markerDirectory.reached)
    (tokenInodes : seen.keeperPhysical.inodes allocation.afterToken =
      seen.keeperPhysical.inodes allocation.afterPhase) :
    let state := opened.start.current.ready.state
    NativeReadyStorage state (observe opened.start.reached) ∧
    ∀ inode, (observe opened.start.reached).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      (seen.keeperPhysical.inodes opened.start.reached).visible inode = state.writer.wal.active.bytes := by
  let state := opened.start.current.ready.state
  let stored := observe raw.markerDirectory.reached
  have directoryEq : state.session.directory = directory := opened.start.directory.trans resolved
  obtain ⟨valid, history, _⟩ := opened.start.current.ready.readPrefix.refines
  have empty : state.writer.history = [] := history.trans opened.emptyHistory
  obtain ⟨first, emptyKeeper, seals⟩ := freshEmptyWAL valid empty
  obtain ⟨bootstrap, census, image, _, _, owner, directorySlot, _⟩ := used
  have manifest : state.writer.target.pair.manifest = none := by
    rw [← valid.retained.resumed.ready.selected]
    exact (congrArg (fun image : DirectoryPublication.Image => image.active.manifest) image).trans bootstrap.manifestAbsent
  have renamedKeeps (name) (wanted : name ∈ ["LOCK", "MANIFEST"]) :
      report.marker.renamedView.child report.captured.root name = report.captured.view.child report.captured.root name := by
    have unchanged := createdKeeps name wanted
    simp only [List.mem_cons, List.not_mem_nil, or_false] at wanted
    have stage : name ≠ "WAL.commit.next" := by rcases wanted with rfl | rfl <;> decide
    have live : name ≠ "WAL.commit" := by rcases wanted with rfl | rfl <;> decide
    rw [report.handoff.renameNames name stage live, report.handoff.stageNames name stage, seen.route]
    exact unchanged
  have listedAbsent : report.captured.view.child report.captured.root "MANIFEST" = none := by
    cases exactChild : report.captured.view.child report.captured.root "MANIFEST" with
    | none => rfl
    | some child =>
      have listed := (report.captured.view.namesExact report.captured.root "MANIFEST").mpr ⟨child, exactChild⟩
      exact False.elim (Bool.noConfusion (report.listed.noConflict _ listed))
  have manifestMissing : stored.files.names (directory.file .manifest) = none := by
    change stored.files.names ⟨directory.path.toString ++ "/" ++ "MANIFEST"⟩ = none
    rw [(children "MANIFEST" (by simp)).1, renamedKeeps "MANIFEST" (by simp), listedAbsent]
    rfl
  have lockName := report.listed.lifetime.lockEntry
  rw [report.listed.sameView, report.listed.sameRoot] at lockName
  have lockObject := report.listed.lifetime.identifiesLock
  rw [report.listed.sameView, report.handoff.renameObjects.symm] at lockObject
  have lockBound : stored.files.names (directory.file .lock) = some (state.census.inode state.owner.description) := by
    change stored.files.names ⟨directory.path.toString ++ "/" ++ "LOCK"⟩ = _
    rw [(children "LOCK" (by simp)).1, renamedKeeps "LOCK" (by simp), lockName]
    change some (report.marker.renamedView.modelObject report.listed.lifetime.lock) = _
    rw [lockObject, census, owner]
    rfl
  have directoryBound : stored.files.names directory.path = some (state.census.inode state.directorySlot.description) := by
    obtain ⟨_, _, _, _, rootObject⟩ := report.captured.captures
    rw [rootNames.1, rootObject, census, directorySlot]
    rfl
  obtain ⟨_, _, keeperBinding, keeperObject, _, _, _, _, _, _, _, visibleKeeper, _⟩ := report.handoff.preservesKeeper
  obtain ⟨_, _, _, _, _, _, markerBinding, _⟩ := report.marker.settledInode
  have markerObject : report.marker.renamedView.modelObject report.marker.stageChild.child = report.marker.inodeState.active := by
    rw [report.handoff.renameObjects, ← report.handoff.stageObjects]
    exact report.marker.stageInode.symm
  obtain ⟨_, _, _, _, _, finalInodes, _, _, keeperBytes, markerBytes, _⟩ := seen.markerPhysical.settles
  have keeperBound : stored.files.names (directory.file (.walSegment 0)) = some report.keeper.settledImage.active := by
    rw [directory.walSegment_path, (children (renderWalSegmentName 0) (by simp)).1, keeperBinding]
    exact congrArg some keeperObject
  have markerBound : stored.files.names (directory.file .walBoundary) = some report.marker.inodeState.active := by
    change stored.files.names ⟨directory.path.toString ++ "/" ++ "WAL.commit"⟩ = _
    rw [(children "WAL.commit" (by simp)).1, markerBinding]
    exact congrArg some markerObject
  have childSettled (names) (allowed : names ∈ stored.crashNames) (name)
      (wanted : name ∈ ["LOCK", "MANIFEST", renderWalSegmentName 0, "WAL.commit"]) :
      let path : FilePath := ⟨directory.path.toString ++ "/" ++ name⟩
      names path = stored.files.names path := by
    intro path
    obtain ⟨visible, surviving⟩ := children name wanted
    rw [visible]
    simpa only [report.handoff.markerSettlement name, List.map_singleton, List.mem_singleton] using surviving names allowed
  have reached : opened.start.reached = allocation.afterToken := congrArg (fun result => result.2.2) returnedAt
  have visibleBeforeAllocation (inode) (bound : stored.files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode) :
      (seen.keeperPhysical.inodes raw.markerDirectory.reached).visible inode = state.writer.wal.active.bytes := by
    rw [directoryEq, first, keeperBound] at bound
    rw [finalInodes, emptyKeeper, ← Option.some.inj bound]
    exact visibleKeeper
  rw [reached]
  refine allocation.framesReadyStorage observe (fun h inode => (seen.keeperPhysical.inodes h).visible inode)
    ?_ visibleBeforeAllocation phaseFrame tokenFrame
    (fun inode _ => congrArg (fun inodes => inodes.visible inode) phaseInodes)
    (fun inode _ => congrArg (fun inodes => inodes.visible inode) tokenInodes)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [directoryEq]
    exact directoryBound
  · rw [directoryEq]
    exact lockBound
  · rw [manifest, directoryEq]
    exact manifestMissing
  · intro segment member
    rw [seals] at member
    exact False.elim (List.not_mem_nil member)
  · intro payload metadata present
    rw [manifest] at present
    contradiction
  · rw [directoryEq, empty]
    exact ⟨_, markerBound, inodeBytes.symm ▸ markerBytes⟩
  · rw [directoryEq, first, emptyKeeper]
    refine ⟨_, keeperBound, ?_⟩
    rw [inodeBytes, seen.route]
    exact keeperBytes
  · intro names allowed path selected
    rcases NativeReadyState.crashPath_iff_write.mp selected with rfl | rfl | frame
    · rw [directoryEq]
      exact childSettled names allowed "WAL.commit" (by simp)
    · rw [directoryEq, first, directory.walSegment_path]
      exact childSettled names allowed (renderWalSegmentName 0) (by simp)
    · rcases frame with rfl | rfl | rfl | ⟨segment, member, _⟩ | ⟨payload, metadata, index, present, _⟩
      · rw [directoryEq]
        exact rootNames.2 names allowed
      · rw [directoryEq]
        exact childSettled names allowed "LOCK" (by simp)
      · rw [directoryEq]
        exact childSettled names allowed "MANIFEST" (by simp)
      · rw [seals] at member
        exact False.elim (List.not_mem_nil member)
      · rw [manifest] at present
        contradiction

/-- The first write uses the returned table's phase and the same three
cache references that the bootstrap initialized. The storage evidence
and the live directory handle refer to that same returned heap. -/
theorem writeStorageEntry {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    {image : Type} (view : OpenCloseHeapView heap image)
    {directoryRef : IO.Ref (Option IO.FS.Handle)}
    {activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))}
    (resolved : opened.handle.directory = directory)
    (references : opened.handle.files.UsesCacheReferences activeRef pendingRef directoryRef)
    (atDirectory : opened.handle.files.AtDirectory directory.path)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached directoryRef activeRef pendingRef = opened.start.current.ready.state.cache)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state storage ∧
      ∀ inode, storage.files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
        visible inode = state.writer.wal.active.bytes) :
    ∃ cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path,
      cache.directory = directoryRef ∧ cache.active = activeRef ∧ cache.pending = pendingRef ∧
      opened.start.WriteStorageEntry view cache storage visible := by
  have directoryEq := opened.start.directory.trans resolved
  let cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path :=
    ⟨directoryRef, activeRef, pendingRef, references, by rw [directoryEq]; exact atDirectory⟩
  obtain ⟨_, reachedCensus, _, _, captured, _, slot, _⟩ := used
  have sameObjects : report.captured.reached.inode = opened.start.current.ready.state.census.inode := by
    rw [reachedCensus]
    rfl
  refine ⟨cache, rfl, rfl, rfl, census, cacheAt, settled.1, settled.2, ?_⟩
  intro literal found
  exact settled.1.bindsOpenCacheDirectory view cacheAt (by rw [captured, slot]; rfl) (congrFun sameObjects _) found

/-- Consume a fixed sequence of observed public calls directly on the
fresh returned table. The actual bootstrap cache supplies the first
physical write entry and its empty ledgers supply the replay origin. -/
theorem refinesReadyCallsFramed {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (resolved : opened.handle.directory = directory)
    (writes : NativeReadyWriteCalls opened.handle) (issuer : opened.handle.LatestIssuer)
    {image : Type} (view : OpenCloseHeapView heap image)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached writes.cache.directory writes.cache.active writes.cache.pending =
      opened.start.current.ready.state.cache)
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state (storage opened.start.reached) ∧
      ∀ inode, (storage opened.start.reached).files.names
        (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
        (inodes opened.start.reached).visible inode = state.writer.wal.active.bytes)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    {calls : List (NativeReturnedCall opened.handle)} {reached : heap}
    (executed : NativeReturnedCalls writes issuer opened.start.reached [] calls reached)
    (covered : NativeReturnedCalls.ReadyFrom writes issuer opened.start.reached [] calls) :
    call entry = .ok opened.handle.table opened.start.reached ∧
    ∃ (last : NativeOpenedPosition opened.handle) (events : List NativeExecutionEvent),
      last.reached = reached ∧
      last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins request => request.pinsAfter pins) [] ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      last.current.history = events.flatMap NativeExecutionEvent.writes ∧
      last.current.submissions = events.flatMap NativeExecutionEvent.submissions ∧
      last.current.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session ∧
      opened.start.current.LedgerSuffix events last.current ∧
      last.current.history.length ≤ (calls.map NativeReturnedCall.requestedRows).sum ∧
      (∀ {first through}, writes.WalWindowEffects storage first through →
        opened.start.WalWindowAt storage first through → last.WalWindowAt storage first through) := by
  have atRoot := (congrArg DiskDirectory.path resolved) ▸ writes.cache.atRoot
  obtain ⟨cache, directory, active, pending, first⟩ :=
    opened.writeStorageEntry used view resolved writes.cache.references atRoot census cacheAt settled
  have physical : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) opened.start := by
    exact ⟨first.census, by rw [← directory, ← active, ← pending]; exact first.cacheAt,
      first.physical, first.keeper, fun literal named => first.root literal (directory ▸ named)⟩
  obtain ⟨last, events, heap, pins, stored, length, records, ledger, budget, names⟩ :=
    executed.refinesReadyFramed covered view inodes runs storage inode buffered effects opened.start rfl
      (by rw [opened.emptyPins]; rfl) physical
  obtain ⟨history, submissions, reads, replay⟩ := opened.refinesLedger ledger
  refine ⟨opened.opened, last, events, heap, pins, stored, length, records, history, submissions, reads, replay,
    ledger, ?_, names⟩
  simpa only [opened.emptyHistory, List.length_nil, Nat.zero_add] using budget

/-- The fresh ready-call ledger is independent of any WAL name window
needed by a later pending operation. -/
theorem refinesReadyCalls {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (resolved : opened.handle.directory = directory)
    (writes : NativeReadyWriteCalls opened.handle) (issuer : opened.handle.LatestIssuer)
    {image : Type} (view : OpenCloseHeapView heap image)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached writes.cache.directory writes.cache.active writes.cache.pending =
      opened.start.current.ready.state.cache)
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state (storage opened.start.reached) ∧
      ∀ inode, (storage opened.start.reached).files.names
        (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
        (inodes opened.start.reached).visible inode = state.writer.wal.active.bytes)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    {calls : List (NativeReturnedCall opened.handle)} {reached : heap}
    (executed : NativeReturnedCalls writes issuer opened.start.reached [] calls reached)
    (covered : NativeReturnedCalls.ReadyFrom writes issuer opened.start.reached [] calls) :
    call entry = .ok opened.handle.table opened.start.reached ∧
    ∃ (last : NativeOpenedPosition opened.handle) (events : List NativeExecutionEvent),
      last.reached = reached ∧
      last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins request => request.pinsAfter pins) [] ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      last.current.history = events.flatMap NativeExecutionEvent.writes ∧
      last.current.submissions = events.flatMap NativeExecutionEvent.submissions ∧
      last.current.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session := by
  obtain ⟨atOpen, last, events, heap, pins, stored, length, records, history, submissions, reads, replay, _⟩ :=
    opened.refinesReadyCallsFramed used resolved writes issuer view inodes runs storage inode buffered
      census cacheAt settled effects executed covered
  exact ⟨atOpen, last, events, heap, pins, stored, length, records, history, submissions, reads, replay⟩

/-- Start the first observed write at the actual returned heap of the
fresh opener. Its local effects refer to the original cache references.
The returned writer can carry the finite WAL window of the next request. -/
theorem acknowledgesFirstWrite {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    {image : Type} (view : OpenCloseHeapView heap image)
    {directoryRef : IO.Ref (Option IO.FS.Handle)}
    {activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))}
    (resolved : opened.handle.directory = directory)
    (references : opened.handle.files.UsesCacheReferences activeRef pendingRef directoryRef)
    (atDirectory : opened.handle.files.AtDirectory directory.path)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached directoryRef activeRef pendingRef = opened.start.current.ready.state.cache)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state (observe opened.start.reached) ∧
      ∀ inode, (observe opened.start.reached).files.names (state.session.directory.file
        (.walSegment state.writer.wal.active.first)) = some inode →
        (inodes opened.start.reached).visible inode = state.writer.wal.active.bytes)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (seen : ∀ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path),
      cache.directory = directoryRef → cache.active = activeRef → cache.pending = pendingRef →
      opened.start.ObservesPublishedWrite appender stager syncer view cache inodes runs observe
        inode buffered request lookup rename sequence reached) :
    let handle := opened.handle
    let start := opened.start
    let dir := start.current.ready.state.session.directory
    call entry = .ok handle.table start.reached ∧ handle.table.UsesOpenWriteSchedules dir handle.files handle.phase ∧
    ∃ (cache : OpenSyncCacheRefs handle.files dir.path) (batch : List WAL.Write) (table : PackedTable)
      (next : NativeOpenedPosition handle) (sameDirectory : next.current.ready.state.session.directory = dir),
      cache.directory = directoryRef ∧ cache.active = activeRef ∧ cache.pending = pendingRef ∧
      request.runOnRawOpenPhase dir lookup (appender.run cache.active) (stager.run cache.pending)
        (syncer.group dir.path cache.directory cache.active cache.pending)
        rename handle.phase handle.get handle.set start.reached = .ok sequence reached ∧
      sequence = table.committed ∧ prepareBatch start.current.ready.state.writer.installed.table request.rows =
        some (batch, table) ∧ next.reached = reached ∧ next.pins = [] ∧
      start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      next.current.history = batch ∧ next.current.submissions = [.acknowledgedBatch batch] ∧
      next.current.ready.reads = [] ∧
      next.WriteStorageEntry view
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
        (observe next.reached) (inodes next.reached).visible ∧
      ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow dir 0 through (observe start.reached) →
        start.WalNameEffects appender stager syncer cache request lookup rename observe 0 through →
        (∀ {settled value}, handle.set handle.phase (.ready value) settled = .ok () reached →
          WalNamePresenceFrame dir 0 through (observe settled) (observe reached)) →
        next.current.ready.state.writer.wal.SettledNamespaceWindow
          next.current.ready.state.session.directory 0 through (observe next.reached) := by
  obtain ⟨cache, sameDir, sameActive, samePending, writeEntry⟩ :=
    opened.writeStorageEntry used view resolved references atDirectory census cacheAt settled
  obtain ⟨schedule, returned, batch, table, next, sameDirectory, prepared, number, atReturn, pins, _, ledger, physical, keepsNames⟩ :=
    opened.start.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty writeEntry (seen cache sameDir sameActive samePending)
  obtain ⟨history, submissions, reads, _⟩ := opened.refinesLedger ledger
  refine ⟨opened.opened, schedule, cache, batch, table, next, sameDirectory, sameDir, sameActive, samePending, returned,
    number, prepared, atReturn, pins.trans opened.emptyPins, ledger, ?_, ?_, ?_, physical, ?_⟩
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using history
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.submissions] using submissions
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.reads] using reads
  · intro through initial names restore
    exact (keepsNames (fun offset _ => Nat.zero_le offset) initial names restore).2

/-- End at the checkpoint issued on the heap of the preceding returned
call. Both the prior replay and the stop use the same opened position. -/
def stopsAfterWrites {last : NativeOpenedPosition opened.handle} {requests : List WriteRequest}
    (trace : NativeOpenedTrace opened.start (requests.map NativeOpenedInstruction.write) events last)
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stop : NativeCheckpointSourceStop last primitives fsync stage reason reached)
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop last.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.handle.contents after.2 opened.handle.phase = opened.handle.contents before.2 opened.handle.phase)
    (stoppedKeeps : opened.handle.contents reached.2 opened.handle.phase =
      opened.handle.contents stop.atIssue.2 opened.handle.phase) :
    NativeReachedExecutionPrefix opened.start.current (requests.map NativeExecutionInstruction.write) .checkpoint :=
  stop.terminalPrefix returnedKeeps stoppedKeeps (trace.writeInstructions rfl) trace.common

end FreshBootstrapOpenHeap.Returned
end Alvoki.Storage.DiskSession
