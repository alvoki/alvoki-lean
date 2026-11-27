import Alvoki.Storage.Disk.Proofs.Native.Open.NativeFreshTableOpen
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenReadyTrace
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenReadyStorage
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeEarlyCheckpointTerminal
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyCallRefinement
import Alvoki.Storage.Disk.Proofs.Write.NativeRawWriteReboot
import Alvoki.Storage.Disk.Proofs.Write.NativeRawWriteRootStop
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeAlignedReadyCalls
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDurability
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationWalReplay
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRawRotationLiveReopen
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRawRotationReboot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WalSegmentRepair (FileImage)
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

private theorem firstBatchLedger (ledger : opened.start.current.LedgerSuffix [.acknowledged request batch] last) :
    last.submissions = [.acknowledgedBatch batch] ∧ last.ready.reads = [] := by
  obtain ⟨_, log, reads, _⟩ := opened.refinesLedger ledger
  simpa only [List.flatMap_cons, List.flatMap_nil, NativeExecutionEvent.submissions, NativeExecutionEvent.reads,
    List.append_nil] using And.intro log reads

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

private theorem freshManifestAbsent {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after) :
    opened.start.current.ready.state.writer.target.pair.manifest = none := by
  obtain ⟨bootstrap, _, image, _⟩ := used
  have ready := opened.start.current.ready.readPrefix.refines.1.retained.resumed.ready
  rw [← ready.selected]
  exact (congrArg (fun image : DirectoryPublication.Image => image.active.manifest) image).trans bootstrap.manifestAbsent

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
    (createdKeeps : ∀ start ≤ through, start ≠ 0 → seen.keeper.namespaceView.child report.captured.root (renderWalSegmentName start) =
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
      rw [createdKeeps start upper zero, missing]
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
  have manifest := opened.freshManifestAbsent used
  obtain ⟨_, census, _, _, _, owner, directorySlot, _⟩ := used
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

/-- The fixed public write dispatcher uses the initialized references
at the actual fresh return heap. -/
theorem readyCallStorage {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (resolved : opened.handle.directory = directory)
    (writes : NativeReadyWriteCalls opened.handle)
    {image : Type} (view : OpenCloseHeapView heap image)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached writes.cache.directory writes.cache.active writes.cache.pending =
      opened.start.current.ready.state.cache)
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state (storage opened.start.reached) ∧
      ∀ inode, (storage opened.start.reached).files.names
        (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
        visible opened.start.reached inode = state.writer.wal.active.bytes) :
    writes.StorageAt view storage visible opened.start := by
  have atRoot := (congrArg DiskDirectory.path resolved) ▸ writes.cache.atRoot
  obtain ⟨cache, directory, active, pending, first⟩ :=
    opened.writeStorageEntry used view resolved writes.cache.references atRoot census cacheAt settled
  exact ⟨first.census, by rw [← directory, ← active, ← pending]; exact first.cacheAt,
    first.physical, first.keeper, fun literal named => first.root literal (directory ▸ named)⟩

/-- Start the first observed write at the actual returned heap of the
fresh opener. Its local effects refer to the original cache references.
The acknowledged batch is the entire history of the checkpoint-free
writer, which can carry the same finite WAL window forward. -/
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
      next.current.ready.state.ObservesLiveWalMarker (observe next.reached) (inodes next.reached).visible ∧
      (let writer := next.current.ready.state.writer
       writer.target.pair.manifest = none ∧ writer.wal.sealed = [] ∧ writer.history = batch ∧
       writer.target.range.through = request.rows.length) ∧
      ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow dir 0 through (observe start.reached) →
        start.WalNameEffects appender stager syncer cache request lookup rename observe 0 through →
        (∀ {settled value}, handle.set handle.phase (.ready value) settled = .ok () reached →
          WalNamePresenceFrame dir 0 through (observe settled) (observe reached)) →
        next.current.ready.state.writer.wal.SettledNamespaceWindow
          next.current.ready.state.session.directory 0 through (observe next.reached) := by
  obtain ⟨cache, sameDir, sameActive, samePending, writeEntry⟩ :=
    opened.writeStorageEntry used view resolved references atDirectory census cacheAt settled
  obtain ⟨schedule, returned, batch, table, next, sameDirectory, prepared, number, atReturn, pins, _, ledger, physical,
    liveMarker, preserved, keepsNames⟩ :=
    opened.start.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty writeEntry (seen cache sameDir sameActive samePending)
  obtain ⟨history, submissions, reads, _⟩ := opened.refinesLedger ledger
  have exactHistory : next.current.history = batch := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using history
  obtain ⟨beforeReady, beforeHistory, _⟩ := opened.start.current.ready.readPrefix.refines
  have seals := (freshEmptyWAL beforeReady (beforeHistory.trans opened.emptyHistory)).2.2
  obtain ⟨afterReady, afterHistory, _⟩ := next.current.ready.readPrefix.refines
  have batchHistory := afterHistory.trans exactHistory
  have cutoff := afterReady.retained.resumed.through.trans
    ((congrArg List.length batchHistory).trans (prepareBatch_spec prepared).1)
  refine ⟨opened.opened, schedule, cache, batch, table, next, sameDirectory, sameDir, sameActive, samePending, returned,
    number, prepared, atReturn, pins.trans opened.emptyPins, ledger, exactHistory, ?_, ?_, physical, liveMarker,
    ⟨preserved.1.trans (opened.freshManifestAbsent used), preserved.2.trans seals, batchHistory, cutoff⟩, ?_⟩
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.submissions] using submissions
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.reads] using reads
  · intro through initial names restore
    exact (keepsNames (fun offset _ => Nat.zero_le offset) initial names restore).2

section BootstrapWriteEntry

variable {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory}
    {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {admitted : heap}
    {seed : OpenSyncCacheAllocations report.captured.opened view init admitted} {calls : FreshBootstrapCacheCalls heap}
    {raw : FreshBootstrapCacheChronology seed calls} (seen : FreshBootstrapOpenHeap report raw)
    (resolved : opened.handle.directory = directory)
    {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (runs : heap → RunUnlinkImage)
    (files : ∀ h, RunDirectoryInodeView opened.handle.directory (seen.keeperPhysical.inodes h) (runs h))
    (through : Nat)
    (createdKeeps : ∀ name ∈ ["LOCK", "MANIFEST"],
      seen.keeper.namespaceView.child report.captured.root name = report.captured.view.child report.captured.root name)
    (createdWal : ∀ start ≤ through, start ≠ 0 → seen.keeper.namespaceView.child report.captured.root (renderWalSegmentName start) =
      report.captured.view.child report.captured.root (renderWalSegmentName start))
    (rootNames : let issued := (files raw.afterRename).storageObservation
      issued.files.names directory.path = some (report.captured.view.modelObject report.captured.root) ∧
      ∀ names ∈ issued.crashNames, names directory.path = issued.files.names directory.path)
    (liveChildren : ∀ name, checkpointFreeWalChild through name →
      (files raw.afterRename).visible ⟨directory.path.toString ++ "/" ++ name⟩ =
        (report.marker.renamedView.child report.captured.root name).map report.marker.renamedView.modelObject)
    (directoryEffect :
      (view.handle raw.afterRename seed.handle).1.inode (view.handle raw.afterRename seed.handle).2.1.description =
        report.marker.renamedView.modelObject report.captured.root →
      calls.fsync seed.handle raw.afterRename = .ok () raw.markerDirectory.reached →
      CheckpointRunsDirectoryEffect directory.path
        (fun path => ∃ name, checkpointFreeWalChild through name ∧ path = ⟨directory.path.toString ++ "/" ++ name⟩)
        (files raw.afterRename).storageObservation (files raw.markerDirectory.reached).storageObservation)
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : WalSegmentRepair.Reopened).installed raw.markerDirectory.reached)
    (returnedAt : (opened.handle.phase, opened.handle.token, opened.start.reached) =
      (allocation.phase, allocation.token, allocation.afterToken))
    (phaseFrame : let scope := fun path => opened.start.current.ready.state.crashPath path ∨
        ∃ start ≤ through, path = directory.file (.walSegment start)
      (files raw.markerDirectory.reached).storageObservation.Frames scope (files allocation.afterPhase).storageObservation)
    (tokenFrame : let scope := fun path => opened.start.current.ready.state.crashPath path ∨
        ∃ start ≤ through, path = directory.file (.walSegment start)
      (files allocation.afterPhase).storageObservation.Frames scope (files allocation.afterToken).storageObservation)
    (phaseInodes : seen.keeperPhysical.inodes allocation.afterPhase =
      seen.keeperPhysical.inodes raw.markerDirectory.reached)
    (tokenInodes : seen.keeperPhysical.inodes allocation.afterToken = seen.keeperPhysical.inodes allocation.afterPhase)

include resolved used createdKeeps createdWal rootNames liveChildren directoryEffect returnedAt phaseFrame tokenFrame phaseInodes tokenInodes

/-- The final bootstrap directory sync settles the protected children
and every canonical WAL name in the prospective write's window. The
directory itself was settled in its parent before this call. -/
theorem readyStorageAndWindow :
    let storage := fun h => (files h).storageObservation
    let state := opened.start.current.ready.state
    (NativeReadyStorage state (storage opened.start.reached) ∧
      ∀ inode, (storage opened.start.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
        some inode → (seen.keeperPhysical.inodes opened.start.reached).visible inode = state.writer.wal.active.bytes) ∧
      opened.start.WalWindowAt storage 0 through := by
  intro storage state
  have actual := raw.markerDirectory.selectsRoot
  have rootObject : (view.handle raw.afterRename seed.handle).1.inode
      (view.handle raw.afterRename seed.handle).2.1.description =
        report.marker.renamedView.modelObject report.captured.root := by
    rw [raw.markerDirectory.rawHandle, report.handoff.renameObjects]
    exact actual.2.2.symm
  have barrier := directoryEffect rootObject raw.markerDirectory.synced
  have root : (storage raw.markerDirectory.reached).files.names directory.path =
      some (report.captured.view.modelObject report.captured.root) ∧
      ∀ names ∈ (storage raw.markerDirectory.reached).crashNames,
        names directory.path = (storage raw.markerDirectory.reached).files.names directory.path := by
    refine ⟨(congrFun barrier.visible _).trans rootNames.1, ?_⟩
    intro names survives
    obtain ⟨prior, priorAllowed, same, _⟩ := barrier.survivors names survives
    exact same.trans ((rootNames.2 prior priorAllowed).trans (congrFun barrier.visible _).symm)
  have children (name : String) (inScope : checkpointFreeWalChild through name) :
      let path : FilePath := ⟨directory.path.toString ++ "/" ++ name⟩
      let object := report.marker.renamedView.modelObject
      (storage raw.markerDirectory.reached).files.names path =
        (report.marker.renamedView.child report.captured.root name).map object ∧
      ∀ names ∈ (storage raw.markerDirectory.reached).crashNames,
        names path ∈ (report.handoff.afterMarkerNames name).map (Option.map object) := by
    refine ⟨(congrFun barrier.visible _).trans (liveChildren name inScope), ?_⟩
    intro names survives
    obtain ⟨_, _, _, settled⟩ := barrier.survivors names survives
    have actual := (settled _ ⟨name, inScope, rfl⟩).trans (liveChildren name inScope)
    simpa only [report.handoff.markerSettlement, List.map_singleton, List.mem_singleton] using actual
  refine ⟨opened.readyStorage seen resolved used storage createdKeeps root ?_ rfl allocation returnedAt
    (phaseFrame.weaken fun _ selected => Or.inl selected) (tokenFrame.weaken fun _ selected => Or.inl selected)
    phaseInodes tokenInodes, opened.walNamespace seen resolved storage through createdWal ?_ allocation returnedAt
    (WalNamePresenceFrame.ofStorageFrame phaseFrame fun start _ bound => Or.inr ⟨start, bound, rfl⟩)
    (WalNamePresenceFrame.ofStorageFrame tokenFrame fun start _ bound => Or.inr ⟨start, bound, rfl⟩)⟩
  · intro name member
    apply children name
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .inl (by simp)
    · exact .inl (by simp)
    · exact .inr ⟨0, Nat.zero_le _, rfl⟩
    · exact .inl (by simp)
  · intro start bound
    rw [directory.walSegment_path]
    exact children (renderWalSegmentName start) (.inr ⟨start, bound, rfl⟩)

/-- The table and cache returned by fresh bootstrap start the actual
public prefix ending in an uncertain write. Its ledger starts empty. -/
theorem refinesReadyBeforeCommitUnknown
    {image : Type} (observeImage : heap → image)
    (writes : NativeReadyWriteCalls opened.handle) (issuer : opened.handle.LatestIssuer)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached writes.cache.directory writes.cache.active writes.cache.pending =
      opened.start.current.ready.state.cache)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects (view.withFileProjection (fun h => ⟨observeImage h, (view.files h).owners⟩))
      seen.keeperPhysical.inodes runs (fun h => (files h).storageObservation) inode buffered)
    {failed : heap} {prefixCalls : List (NativeReturnedCall opened.handle)}
    {request : WriteRequest} {cause : IO.Error}
    (executed : NativeReturnedCalls writes issuer opened.start.reached []
      (prefixCalls ++ [.write request (.error (.commitUnknown cause))]) failed)
    (names : writes.WalWindowEffects (fun h => (files h).storageObservation) 0
      (opened.start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (budget : opened.start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum +
      request.rows.length ≤ through) :
    call entry = .ok opened.handle.table opened.start.reached ∧
    ∃ (current : NativeOpenedPosition opened.handle) (events : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer opened.start.reached [] prefixCalls current.reached ∧
      events.length = prefixCalls.length ∧ (∀ pair ∈ prefixCalls.zip events, pair.1.Records pair.2) ∧
      opened.start.current.LedgerSuffix events current.current ∧
      writes.ReachedUncertainWrite issuer current files 0 request cause failed := by
  let clientView := view.withFileProjection (fun h => ⟨observeImage h, (view.files h).owners⟩)
  obtain ⟨settled, window⟩ := opened.readyStorageAndWindow seen resolved used runs files through
    createdKeeps createdWal rootNames liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
  have initial := opened.readyCallStorage used resolved writes clientView
    (fun h => (files h).storageObservation) (fun h => (seen.keeperPhysical.inodes h).visible) census cacheAt settled
  have actual : NativeReturnedCalls writes issuer opened.start.reached (opened.start.pins.map NativeOpenedPin.raw)
      (prefixCalls ++ [.write request (.error (.commitUnknown cause))]) failed := by
    simpa only [opened.emptyPins, List.map_nil] using executed
  obtain ⟨current, events, ran, length, records, ledger, uncertain⟩ :=
    actual.refinesReadyBeforeCommitUnknown opened.start (.empty _) clientView
      seen.keeperPhysical.inodes runs files inode buffered effects initial names (window.restrictUpper budget)
  refine ⟨opened.opened, current, events, ?_, length, records, ledger, uncertain⟩
  simpa only [opened.emptyPins, List.map_nil] using ran

variable (modeledFiles : heap → FileImage)

local notation "clientView" => OpenCloseHeapView.withFileProjection view
  (fun h => LockedFileState.mk (modeledFiles h) (LockedFileState.owners (OpenCloseHeapView.files view h)))
local notation "storage" => fun h => RunDirectoryInodeView.storageObservation (files h)
local notation "visible" => fun h =>
  WalInodeImage.visible (FreshBootstrapKeeperPhysical.inodes (FreshBootstrapOpenHeap.keeperPhysical seen) h)
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))

section FirstAcknowledgement

variable
    (references : opened.handle.files.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef)
    (atDirectory : opened.handle.files.AtDirectory directory.path)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached seed.directoryRef seed.activeRef seed.pendingRef =
      opened.start.current.ready.state.cache)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (covered : request.rows.length ≤ through)

set_option quotPrecheck false in
local notation "observedFirstWrite" =>
  ∀ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path),
    OpenSyncCacheRefs.directory cache = OpenSyncCacheAllocations.directoryRef seed →
    OpenSyncCacheRefs.active cache = OpenSyncCacheAllocations.activeRef seed →
    OpenSyncCacheRefs.pending cache = OpenSyncCacheAllocations.pendingRef seed →
    NativeOpenedPosition.ObservesPublishedWrite (FreshBootstrapOpenHeap.Returned.start opened)
      appender stager syncer clientView cache
      (FreshBootstrapKeeperPhysical.inodes (FreshBootstrapOpenHeap.keeperPhysical seen)) runs storage
      inode buffered request lookup rename sequence reached

include references atDirectory census cacheAt nonempty

/-- The first acknowledgement leaves the same table and cache ready to
accept another write. The bootstrap window can cover both requests. -/
theorem acknowledgesFirstWriteWithWindow (wrote : observedFirstWrite) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (batch : List WAL.Write) (preparedTable : PackedTable) (next : NativeOpenedPosition opened.handle)
      (sameDirectory : next.current.ready.state.session.directory = opened.start.current.ready.state.session.directory),
      let state := next.current.ready.state
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (batch, preparedTable) ∧
      sequence = preparedTable.committed ∧ sequence.toNat = batch.length ∧
      cache.directory = seed.directoryRef ∧ cache.active = seed.activeRef ∧ cache.pending = seed.pendingRef ∧
      next.reached = reached ∧ next.pins = [] ∧ next.current.history = batch ∧
      opened.start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      next.WriteStorageEntry clientView
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
        (storage next.reached) (visible next.reached) ∧
      state.ObservesLiveWalMarker (storage next.reached) (visible next.reached) ∧
      (state.writer.target.pair.manifest = none ∧ state.writer.wal.sealed = [] ∧ state.writer.history = batch ∧
        state.writer.target.range.through = request.rows.length) ∧
      ∀ horizon ≤ through,
        opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 horizon →
        (∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 horizon
            (storage preReady) (storage reached)) →
        next.WalWindowAt storage 0 horizon := by
  obtain ⟨settled, freshWindow⟩ := opened.readyStorageAndWindow seen resolved used runs files through
    createdKeeps createdWal rootNames liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame
    phaseInodes tokenInodes
  obtain ⟨initial, _, cache, batch, preparedTable, next, sameDirectory, dirRef, activeRef, pendingRef, write, number,
    prepared, exactHeap, emptyPins, ledger, batchHistory, _, _, physical, liveMarker, shape, carries⟩ :=
    opened.acknowledgesFirstWrite used clientView resolved references atDirectory census cacheAt
      seen.keeperPhysical.inodes runs storage settled appender stager syncer inode buffered request lookup rename nonempty wrote
  rw [dirRef, activeRef, pendingRef, opened.start.directory.trans resolved] at write
  obtain ⟨ready, initialHistory, _⟩ := opened.start.current.ready.readPrefix.refines
  obtain ⟨_, refined, represented⟩ := ready.retained.resumed.canonical
  have initialCount : opened.start.current.ready.state.writer.installed.table.committed.toNat = 0 := by
    rw [refined.committed, represented.committed_count, initialHistory, opened.emptyHistory]
    rfl
  have count : sequence.toNat = batch.length := by
    rw [number, replay_committed_count batch (prepareBatch_spec prepared).2.1, initialCount, Nat.zero_add]
  refine ⟨cache, batch, preparedTable, next, sameDirectory, initial, write, prepared, number, count,
    dirRef, activeRef, pendingRef, exactHeap, emptyPins, batchHistory, ledger, physical, liveMarker, shape, ?_⟩
  intro horizon covered nameEffects restore
  exact ⟨fun offset _ => Nat.zero_le offset,
    carries horizon (freshWindow.restrictUpper covered).2 nameEffects restore⟩

include covered in
/-- A sampled restart after the first acknowledged write uses the
same returned writer and cache as a subsequent write would. -/
theorem replaysFirstAcknowledgedWrite {stream : Type} (wrote : observedFirstWrite)
    (source : RawMarkedOpenInterpreter heap stream) (namespaceView : DirectoryReadNamespace) (root : DeviceInode) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (batch : List WAL.Write) (preparedTable : PackedTable) (next : NativeOpenedPosition opened.handle),
      let state := next.current.ready.state
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (batch, preparedTable) ∧
      sequence = preparedTable.committed ∧ sequence.toNat = batch.length ∧
      cache.directory = seed.directoryRef ∧ cache.active = seed.activeRef ∧ cache.pending = seed.pendingRef ∧
      next.reached = reached ∧ state.writer.history = batch ∧
      opened.start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      ∀ {rebooted : heap} (sample : RawWriteRebootEntry state clientView storage names visible reached rebooted),
        sample.DurableReset →
        opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 request.rows.length →
        (∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 request.rows.length
            (storage preReady) (storage reached)) →
        source.ReplaysWalBeforeCheckpointAtOpen clientView (state).session.directory (state).writer.wal.active.first
          storage visible rebooted namespaceView root batch := by
  obtain ⟨cache, batch, preparedTable, next, _, initial, write, prepared, number, count, dirRef, activeRef, pendingRef,
    exactHeap, _, _, ledger, physical, _, ⟨noManifest, _, history, cutoff⟩, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, batch, preparedTable, next, initial, write, prepared, number, count, dirRef, activeRef, pendingRef,
    exactHeap, history, ledger, ?_⟩
  intro _ sampled reset nameEffects restore
  have finalWindow := (carries request.rows.length covered nameEffects restore).2
  rw [← cutoff, exactHeap] at finalWindow
  have readyPhysical := physical.physical
  rw [exactHeap] at readyPhysical
  rw [← history]
  exact @RawWriteRebootEntry.replaysWalBeforeCheckpointAtOpen _ _ _ _ source _ _ _ _ namespaceView root
    sampled next.current.ready.readPrefix.refines.1 readyPhysical reset finalWindow noManifest

include covered in
/-- The first acknowledged WAL batch survives creation of the successor,
one sampled power loss, and a lookup on the table returned by the next open. -/
theorem readsAfterCreatedRotation {stream : Type} (wrote : observedFirstWrite)
    (source : RawMarkedOpenInterpreter heap stream) (namespaceView : DirectoryReadNamespace) (root : DeviceInode) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (batch : List WAL.Write) (preparedTable : PackedTable) (next : NativeOpenedPosition opened.handle),
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (batch, preparedTable) ∧
      sequence = preparedTable.committed ∧ sequence.toNat = batch.length ∧ next.reached = reached ∧
      ∀ (_firstNames : opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 request.rows.length)
        (_restore : ∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 request.rows.length
            (storage preReady) (storage reached))
        (report : NativeReadyCreatedRotation next.current.ready.state)
        (rotation : OpenRotationObservation.Created next report),
        ∃ rotated, rotation.Reached report.lookup rotated ∧
          rotation.active = seed.activeRef ∧ rotation.pending = seed.pendingRef ∧ rotation.directory = seed.directoryRef ∧
          opened.start.current.LedgerSuffix [.acknowledged request batch, .rotatedWal] rotated.current ∧
          let old := next.current.ready.state
          let state := rotated.current.ready.state
          let reopenView := rotation.view.withFileProjection (fun h => ⟨modeledFiles h, (rotation.view.files h).owners⟩)
          ∀ (_keeps : rotation.LocalFrames (fun a b => (storage a).Frames old.crashPath (storage b)))
            (_child : (rotation.view.files rotated.reached).image.ObservesWalChild report.parent.root
              state.session.directory state.writer.wal.active.first (storage rotated.reached) (visible rotated.reached))
            (_otherNames : rotation.LocalFrames (fun a b => RotationWalNameFrame old.session.directory 0
              request.rows.length old.writer.wal.active.last (storage a) (storage b)))
            {rebooted : heap} (sample : RawWriteRebootEntry state reopenView storage names visible rotated.reached rebooted),
            sample.DurableReset →
            source.ReadsClientHistoryAtOpen reopenView (state).session.directory storage visible rebooted
              namespaceView root [.acknowledgedBatch batch] [] batch := by
  obtain ⟨cache, batch, preparedTable, next, _, atOpen, write, prepared, number, count, _, _, _,
    exactHeap, _, batchHistory, firstLedger, physical, _, ⟨noManifest, _, _, _⟩, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, batch, preparedTable, next, atOpen, write, prepared, number, count, exactHeap, ?_⟩
  intro firstNames restore report rotation
  obtain ⟨rotated, returned, step, continues⟩ :=
    NativeOpenedPosition.rotatesCreatedWithWal (current := next) report rotation storage visible
  have ledger := firstLedger.append step.ledgerSuffix
  refine ⟨rotated, returned, rotation.references.1.symm.trans references.1,
    rotation.references.2.1.symm.trans references.2.1, rotation.references.2.2.symm.trans references.2.2, ledger, ?_⟩
  intro old state reopenView keeps child otherNames rebooted sample reset
  have window := carries request.rows.length covered firstNames restore
  have gaps (start : Nat) (bound : start ≤ request.rows.length) (_apart : start ≠ old.writer.wal.active.last) :
      old.writer.wal.SettledNamespaceWindow old.session.directory start start (storage next.reached) :=
    ⟨window.2.1.restrict (Nat.zero_le _) bound,
      fun surviving chosen => (window.2.2 surviving chosen).restrict (Nat.zero_le _) bound⟩
  have post := continues physical.physical keeps child
  obtain ⟨_, readsAfterOpen⟩ := post.2 request.rows.length gaps otherNames
  obtain ⟨valid, writerHistory, _⟩ := rotated.current.ready.readPrefix.refines
  have history : rotated.current.history = batch := by
    simpa only [NativeExecutionEvent.writes, List.append_nil, batchHistory] using step.ledgers.1
  have cutoff : state.writer.target.range.through ≤ request.rows.length := by
    change rotated.current.ready.state.writer.target.range.through ≤ request.rows.length
    rw [valid.retained.resumed.through, writerHistory, history, (prepareBatch_spec prepared).1]
    exact Nat.le_refl _
  obtain ⟨submitted, noReads⟩ := opened.firstBatchLedger firstLedger
  change source.ReadsClientHistoryAtOpen reopenView (state).session.directory
    storage visible rebooted namespaceView root
    [.acknowledgedBatch batch] [] batch
  rw [← submitted, ← noReads, ← batchHistory]
  exact @readsAfterOpen stream source modeledFiles rebooted namespaceView root sample reset cutoff noManifest

include covered in
/-- A returned rotation error after the first acknowledgement leaves the
same batch available to a live open after the explicit close. -/
theorem readsAfterFailedRotation {stream : Type} (wrote : observedFirstWrite)
    (source : RawMarkedOpenInterpreter heap stream) (rotation : OpenRotationCallbacks heap)
    (closeView : OpenCloseHeapView heap RotationCreateFiles)
    (unlock : IO.FS.Handle → EStateM IO.Error heap Unit)
    (setCell : {α : Type} → IO.Ref α → α → EStateM IO.Error heap Unit) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (batch : List WAL.Write) (preparedTable : PackedTable) (next : NativeOpenedPosition opened.handle),
      let state := next.current.ready.state
      let dir := state.session.directory
      let usedCache : OpenSyncCacheRefs opened.handle.files opened.handle.directory.path :=
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          congrArg DiskDirectory.path opened.start.directory ▸ cache.atRoot⟩
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (batch, preparedTable) ∧
      sequence = preparedTable.committed ∧ sequence.toNat = batch.length ∧ next.reached = reached ∧
      opened.start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      ∀ (_firstNames : opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 request.rows.length)
        (_restore : ∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 request.rows.length
            (storage preReady) (storage reached))
        {cause : IO.Error} {poisoned synced issued failed afterUnlock : heap} {root : IO.FS.Handle}
        (directoryObject : DeviceInode)
        (guard : BatchActiveGuard opened.handle.directory state.writer.installed)
        (_poisonedAt : opened.handle.set opened.handle.phase .poisoned next.reached = .ok () poisoned)
        (filePrefix : rotation.SuccessorFilePrefix opened.handle.directory state.writer.rotationInstalled.activeFirst poisoned synced)
        (file : filePrefix.ExclusiveSync stager syncer usedCache)
        (_rootRoute : rotation.sync opened.handle.directory.path synced =
          syncer.group opened.handle.directory.path usedCache.directory usedCache.active usedCache.pending
            #[opened.handle.directory.path] synced)
        (_loaded : syncer.readDirectory usedCache.directory synced = .ok (some root) issued)
        (_rootFailed : syncer.fsync root issued = .error cause failed)
        (_rotationEffects : NativeRotationCloseEffects next usedCache closeView file directoryObject
          (fun name => checkpointFreeWalChild state.writer.history.length name ∧
            name ≠ renderWalSegmentName state.writer.rotationInstalled.activeFirst) issued failed)
        (drops : CloseCacheField → List LockReferenceDrop)
        (_unlocked : unlock opened.handle.lock failed = .ok () afterUnlock)
        (_unlockEffect : (closeView.files failed).owners.Owns dir state.session.descriptor →
          (closeView.handle failed opened.handle.lock).2.1 ∈ (closeView.descriptors failed).slots →
          (closeView.handle failed opened.handle.lock).2.1.description = state.session.descriptor →
          unlock opened.handle.lock failed = .ok () afterUnlock →
          closeView.phase afterUnlock opened.handle.phase = some .poisoned ∧
          closeView.files afterUnlock = ⟨(closeView.files failed).image, (closeView.files failed).owners.set (dir.file .lock) none⟩ ∧
          closeView.descriptors afterUnlock = closeView.descriptors failed)
        (clears : OpenCloseClears drops closeView ⟨opened.handle.get, unlock, setCell⟩
          opened.handle.phase usedCache.active usedCache.pending usedCache.directory afterUnlock),
        let released := clears.afterPhase
        let observed := (closeView.files released).image
        let live := fun h => (closeView.files h).image.inodes.visible
        let openView := closeView.withFileProjection (fun h => ⟨modeledFiles h, (closeView.files h).owners⟩)
        let successor := state.writer.rotationInstalled.activeFirst
        ∀ (_atEntry : ∀ name, checkpointFreeWalChild state.writer.history.length name →
            names next.reached ⟨dir.path.toString ++ "/" ++ name⟩ =
              ((closeView.files next.reached).image.view.child directoryObject name).map
                (closeView.files next.reached).image.view.modelObject)
          (_atClose : ∀ name, checkpointFreeWalChild state.writer.history.length name →
            names released ⟨dir.path.toString ++ "/" ++ name⟩ =
              (observed.view.child directoryObject name).map observed.view.modelObject)
          (_entryBytes : ∀ path, path = dir.file (.walSegment state.writer.wal.active.first) ∨ path = dir.file .walBoundary →
            ∀ inode, names next.reached path = some inode → live next.reached inode = visible next.reached inode),
          rotation.run opened.handle guard.lookup usedCache.active next.reached =
            .error (IO.userError s!"sync failed for '{opened.handle.directory.path}': {cause}") failed ∧
          opened.handle.table.close = closeSchedule opened.handle.phase.get (fun _ => opened.handle.lock.unlock)
            (usedCache.active.set none) (usedCache.pending.set []) (usedCache.directory.set none)
            (opened.handle.phase.set .closed) ∧
          closeSchedule (opened.handle.get opened.handle.phase) (fun _ => unlock opened.handle.lock)
            (setCell usedCache.active none) (setCell usedCache.pending []) (setCell usedCache.directory none)
            (setCell opened.handle.phase .closed) failed = .ok () released ∧
          source.ReadsClientHistoryAtOpen (openView.withObservedWalFiles dir successor names live) dir storage live released observed.view directoryObject
            [.acknowledgedBatch batch] [] batch := by
  obtain ⟨cache, batch, preparedTable, next, _, initial, write, prepared, number, count, _, _, _, exactHeap,
    _, batchHistory, ledger, physical, liveMarker, ⟨noManifest, noSeals, history, _⟩, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, batch, preparedTable, next, initial, write, prepared, number, count, exactHeap, ledger, ?_⟩
  intro firstNames restore cause poisoned synced issued failed afterUnlock root directoryObject guard poisonedAt
    filePrefix file rootRoute loaded rootFailed rotationEffects drops unlocked unlockEffect clears
  intro released observed live openView successor atEntry atClose entryBytes
  have positive : 0 < next.current.ready.state.writer.history.length := by
    rw [history, (prepareBatch_spec prepared).1]
    exact List.length_pos_iff.mpr nonempty
  have nonemptyWal := next.current.ready.readPrefix.refines.1.retained.activeBeforeCutoffOfFirstBatch noManifest noSeals positive
  obtain ⟨returned, phase, owner, held, liveLock, kept, child, created, _, empty⟩ := next.rotationErrorCloseProjection
    rotation stager syncer _ closeView guard nonemptyWal poisonedAt filePrefix file rootRoute loaded rootFailed rotationEffects
  obtain ⟨close, rawClose, closed⟩ := next.closesAfterRotationDirectoryError rotation _ closeView unlock setCell
    guard returned phase owner held liveLock drops unlocked unlockEffect clears
  have catalog := (carries request.rows.length covered firstNames restore).2.1
  rw [← (prepareBatch_spec prepared).1, ← history] at catalog
  let markerPath := next.current.ready.state.session.directory.file .walBoundary
  have markerBytes : (names next.reached markerPath).map (visible next.reached) =
      next.current.ready.state.writer.target.pair.walBoundary := liveMarker
  have markerAtEntry : next.current.ready.state.ObservesLiveWalMarker (storage next.reached) (live next.reached) := by
    change (names next.reached markerPath).map (live next.reached) = _
    rw [← markerBytes]
    exact Option.map_congr (entryBytes markerPath (.inr rfl))
  obtain ⟨_, readsAfterOpen⟩ := closed.readsAfterRotationDirectoryError («storage» := storage) _ nonemptyWal
    directoryObject child created empty kept physical.physical
    (fun inode bound => (entryBytes _ (.inl rfl) inode bound).trans (physical.keeper inode bound))
    markerAtEntry (by simp [noSeals]) catalog atEntry atClose modeledFiles noManifest source
  simp only [returned, Option.some.injEq, Prod.mk.injEq, true_and] at rawClose
  obtain ⟨submitted, noReads⟩ := opened.firstBatchLedger ledger
  refine ⟨returned, close, rawClose, ?_⟩
  rw [← submitted, ← noReads, ← batchHistory]
  exact @readsAfterOpen

/-- A failed rotation and one reboot preserve the first batch for reads.
The sampled map has no WAL segment between the committed cutoff and
the requested horizon, with the cutoff itself excluded.
A durable reset and scoped retry frames also support calls on the reopened writer. -/
theorem readsAfterFailedRotationReboot {stream : Type} (wrote : observedFirstWrite)
    (source : RawMarkedOpenInterpreter heap stream) (rotation : OpenRotationCallbacks heap) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (batch : List WAL.Write) (preparedTable : PackedTable) (next : NativeOpenedPosition opened.handle),
      let state := next.current.ready.state
      let dir := state.session.directory
      let usedCache : OpenSyncCacheRefs opened.handle.files opened.handle.directory.path :=
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          congrArg DiskDirectory.path opened.start.directory ▸ cache.atRoot⟩
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (batch, preparedTable) ∧
      sequence = preparedTable.committed ∧ sequence.toNat = batch.length ∧ next.reached = reached ∧
      opened.start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      ∀ {poisoned afterFileSync : heap}
        (guard : BatchActiveGuard opened.handle.directory state.writer.installed)
        (_poisonedAt : opened.handle.set opened.handle.phase .poisoned next.reached = .ok () poisoned)
        (filePrefix : rotation.SuccessorFilePrefix opened.handle.directory state.writer.rotationInstalled.activeFirst
          poisoned afterFileSync)
        (barrier : rotation.FailedRootBarrier syncer usedCache afterFileSync),
        rotation.run opened.handle guard.lookup usedCache.active next.reached =
          .error (IO.userError s!"sync failed for '{opened.handle.directory.path}': {barrier.cause}") barrier.failed ∧
        ∀ (horizon : Nat) (_cutoffCovered : request.rows.length ≤ horizon) (_horizonCovered : horizon ≤ through)
          (_firstNames : opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 horizon)
          (_restore : ∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
            WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 horizon
              (storage preReady) (storage reached))
          {rebooted : heap} {effective : Bool}
          (file : filePrefix.ExclusiveSync stager syncer usedCache)
          (_fileEffects : file.SuccessorEffects clientView storage visible next.reached barrier.issued)
          (_rootEffects : filePrefix.RootErrorEffects barrier clientView storage effective next.reached)
          (_fileFrames : file.PreservesFiles clientView storage (state.rotationProtectedScope 0 horizon)
            next.reached barrier.issued),
          let valid := next.current.ready.readPrefix.refines.1
          let selected := state.withRotationSample valid (names rebooted)
          let path := dir.file (.walSegment state.writer.rotationInstalled.activeFirst)
          let inode := OpenCloseHeapView.capturedInode clientView file.opened file.handle
          ∀ (_chosen : names rebooted ∈ (storage barrier.failed).crashNames),
            (names rebooted path = none ∨ names rebooted path = some inode) ∧
            (effective = true → names rebooted path = some inode) ∧
            (∀ start, request.rows.length < start → start ≤ horizon →
              names rebooted (dir.file (.walSegment start)) = none) ∧
            ∀ (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
              (_sampled : ∀ path, checkpointSurvivorPath dir selected.writer selected.writer.target.pair.manifest path →
                ∀ object, names rebooted path = some object → visible rebooted object ∈ (storage barrier.failed).files.bytes object)
              {errors : List (FilePath × IO.Error)} {retryAt : heap}
              (attempts : source.FailedCalls rebooted errors retryAt)
              (_effects : attempts.PreserveWalFiles (directory := dir) horizon names visible),
              (∀ start, selected.writer.history.length < start → start ≤ horizon →
                names retryAt (dir.file (.walSegment start)) = none) ∧
              source.ReadsClientHistoryAtOpen
                ((clientView).withObservedWalFiles dir selected.writer.wal.active.first names visible)
                dir storage visible retryAt namespaceView root [.acknowledgedBatch batch] [] batch ∧
              ∀ (_restored : ∀ child, selected.writer.walOpenDurablePath dir child → child ≠ dir.path →
                  ∀ object, names rebooted child = some object →
                    (storage rebooted).files.bytes object = [visible rebooted object])
                (_rootSettled : ∀ possible ∈ (storage rebooted).crashNames, possible dir.path = names rebooted dir.path)
                (_kept : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
                  source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(input, cause)]) errors →
                  source.openTable input before = .error cause after →
                  (storage before).Frames (selected.writer.walOpenDurablePath dir) (storage after)),
                source.WritesAfterWalOpen clientView dir selected.writer retryAt namespaceView root
                  opened.start.current [.acknowledged request batch] seen.keeperPhysical.inodes runs storage := by
  obtain ⟨cache, batch, preparedTable, next, _, initial, write, prepared, number, count, _, _, _, exactHeap,
    _, batchHistory, ledger, physical, _, ⟨noManifest, noSeals, history, cutoff⟩, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, batch, preparedTable, next, initial, write, prepared, number, count, exactHeap, ledger, ?_⟩
  intro poisoned afterFileSync guard poisonedAt filePrefix barrier
  have positive : 0 < next.current.ready.state.writer.history.length := by
    rw [history, (prepareBatch_spec prepared).1]
    exact List.length_pos_iff.mpr nonempty
  have nonemptyWal := next.current.ready.readPrefix.refines.1.retained.activeBeforeCutoffOfFirstBatch noManifest noSeals positive
  refine ⟨(next.rotationReturnsDirectoryError rotation syncer _ guard nonemptyWal poisonedAt filePrefix
    barrier.route barrier.loaded barrier.returned).2.2.1, ?_⟩
  intro horizon cutoffCovered horizonCovered firstNames restore rebooted effective file fileEffects rootEffects
    fileFrames valid selected path createdInode chosen
  have window := (carries horizon horizonCovered firstNames restore).2
  have withinHorizon : next.current.ready.state.writer.target.range.through ≤ horizon := by
    rw [cutoff]
    exact cutoffCovered
  obtain ⟨_, ready, sameHistory, pair, _, noLater, choice, settled, sampledFiles⟩ := next.samplesFailedRotationDirectory
    rotation syncer clientView _ storage visible filePrefix file barrier fileEffects rootEffects
    nonemptyWal physical fileFrames withinHorizon window chosen
  refine ⟨choice.imp id And.left, settled, fun start past bound => noLater start (cutoff.symm ▸ past) bound, ?_⟩
  intro namespaceView root sampled errors retryAt attempts effects
  have bootFiles := sampledFiles sampled noManifest
  have selectedLength := (congrArg List.length sameHistory).trans
    ((congrArg List.length history).trans (prepareBatch_spec prepared).1)
  have missing := (congrArg DirectoryPublication.Bindings.manifest pair).trans noManifest
  obtain ⟨carriesAbsence, openedRetry, startsWriter⟩ := attempts.reopensSampledWal (view := clientView)
    (namespaceView := namespaceView) (root := root) seen.keeperPhysical.inodes runs storage ready missing bootFiles
    (by simpa only [selectedLength] using cutoffCovered) effects
  refine ⟨carriesAbsence (fun start past bound => noLater start (cutoff.symm ▸ (selectedLength ▸ past)) bound), ?_, ?_⟩
  · have replay := @Eq.mp _ _ (congrArg (fun writes => source.ReplaysWalBeforeCheckpointAtOpen
      ((clientView).withObservedWalFiles next.current.ready.state.session.directory selected.writer.wal.active.first names visible)
      next.current.ready.state.session.directory selected.writer.wal.active.first storage visible retryAt namespaceView root writes)
      (sameHistory.trans history)) (@openedRetry)
    obtain ⟨submitted, noReads⟩ := opened.firstBatchLedger ledger
    have pending : PendingClientReplay [.acknowledgedBatch batch] [] batch := by
      rw [← submitted, ← noReads, ← batchHistory]
      exact next.current.ready.readPrefix.refines.2.2
    exact @RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen.recordsReads
      (opened := replay) (pending := pending)
  · intro restored rootSettled kept
    have durable := bootFiles.durabilityAfterRebootRetries (source := source)
      («storage» := storage) («visible» := visible) (rebooted := rebooted) (entry := retryAt)
      ready restored rootSettled attempts (fun prior inside returned => kept prior inside returned)
    exact @startsWriter _ _ _ (sameHistory.trans next.current.ready.readPrefix.refines.2.1) ledger durable

/-- The actual first acknowledgement starts the interrupted second
write. One reboot sample selects its replay and the subsequent lookup
runs on the table returned by that literal open. -/
theorem readsAfterInterruptedSecondBatch {stream : Type}
    (second : WriteRequest) (bothCovered : request.rows.length + second.rows.length ≤ through)
    (wrote : observedFirstWrite)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (source : RawMarkedOpenInterpreter heap stream) (namespaceView : DirectoryReadNamespace) (root : DeviceInode) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (firstBatch : List WAL.Write) (firstTable : PackedTable) (next : NativeOpenedPosition opened.handle)
      (sameDirectory : next.current.ready.state.session.directory = opened.start.current.ready.state.session.directory),
      let dir := next.current.ready.state.session.directory
      let nextCache : OpenSyncCacheRefs opened.handle.files dir.path :=
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
      let observed := fun h => next.directory.symm ▸ files h
      let observedStorage := fun h => (observed h).storageObservation
      let horizon := request.rows.length + second.rows.length
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (firstBatch, firstTable) ∧
      sequence.toNat = firstBatch.length ∧ next.reached = reached ∧
      opened.start.current.LedgerSuffix [.acknowledged request firstBatch] next.current ∧
      ∀ (_firstNames : opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0 horizon)
        (_restore : ∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 horizon
            (storage preReady) (storage reached))
        (stop : next.RootFsyncStop syncer nextCache clientView appender stager seen.keeperPhysical.inodes runs observed
          inode buffered second lookup rename fsync),
        second.runUntilRootFsync dir nextCache lookup appender stager syncer rename fsync
          opened.handle.phase opened.handle.get opened.handle.set next.reached = .error stop.tag stop.reached ∧
        ∃ (secondBatch : List WAL.Write) (secondTable : PackedTable),
          prepareBatch next.current.ready.state.writer.installed.table second.rows = some (secondBatch, secondTable) ∧
          ∀ {rebooted : heap} (sample : RawWriteRebootEntry next.current.ready.state clientView observedStorage
            (fun h => (observedStorage h).files.names) visible stop.reached rebooted),
            sample.DurableReset →
            ∃ history retained : List WAL.Write,
              history = firstBatch ++ retained ∧ (retained = [] ∨ retained = secondBatch) ∧
              opened.start.current.InterruptedWriteLedger next.current [.acknowledged request firstBatch]
                second secondBatch retained history ∧
              source.ReadsClientHistoryAtOpen clientView next.current.ready.state.session.directory observedStorage visible rebooted
                namespaceView root [.acknowledgedBatch firstBatch, .uncertainBatch secondBatch] [] history := by
  obtain ⟨cache, firstBatch, firstTable, next, sameDirectory, atOpen, write, prepared, _, count, _, _, _,
    exactHeap, _, batchHistory, firstLedger, physical, _, ⟨noManifest, _, _, _⟩, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, firstBatch, firstTable, next, sameDirectory, atOpen, write, prepared, count, exactHeap, firstLedger, ?_⟩
  intro firstNames restore stop
  have castStorage {before after : DiskDirectory} {inodes : WalInodeImage} {runs : RunUnlinkImage}
      (same : before = after) (files : RunDirectoryInodeView before inodes runs) :
      (same ▸ files : RunDirectoryInodeView after inodes runs).storageObservation = files.storageObservation := by
    subst after
    rfl
  have sameStorage : (fun h => (next.directory.symm ▸ files h : RunDirectoryInodeView _ _ _).storageObservation) =
      storage := funext (fun h => castStorage next.directory.symm (files h))
  have firstWindow := carries _ bothCovered firstNames restore
  have rowCount := (prepareBatch_spec prepared).1
  have expectedHorizon : next.current.history.length + second.rows.length = request.rows.length + second.rows.length := by
    rw [batchHistory, rowCount]
  have old : NativeReadyStorage next.current.ready.state
      (next.directory.symm ▸ files next.reached : RunDirectoryInodeView _ _ _).storageObservation := by
    rw [castStorage]
    exact physical.physical
  have window : next.WalWindowAt
      (fun h => (next.directory.symm ▸ files h : RunDirectoryInodeView _ _ _).storageObservation)
      0 (next.current.history.length + second.rows.length) := by
    rw [sameStorage, expectedHorizon]
    exact firstWindow
  obtain ⟨_, stopped, secondBatch, secondTable, secondPrepared, _, selects⟩ := next.stopsAtRootFsync syncer _ clientView appender stager seen.keeperPhysical.inodes
    runs (fun h => next.directory.symm ▸ files h) inode buffered second lookup rename fsync stop old
  refine ⟨stopped, secondBatch, secondTable, secondPrepared, ?_⟩
  intro rebooted sample reset
  obtain ⟨_, plan, retained, _, _, ledger, opens⟩ := selects sample reset window
  have interruption := ledger firstLedger
  have retainedHistory : plan.history = firstBatch ++ retained := by
    simpa only [opened.emptyHistory, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, NativeExecutionEvent.writes] using interruption.history_eq
  have pending : PendingClientReplay [.acknowledgedBatch firstBatch, .uncertainBatch secondBatch] [] plan.history := by
    simpa only [opened.emptySubmissions, opened.emptyReads, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons_append, NativeExecutionEvent.submissions, NativeExecutionEvent.reads] using interruption.pending
  exact ⟨plan.history, retained, retainedHistory, interruption.whole, interruption,
    (@opens stream source namespaceView root noManifest).recordsReads pending⟩

include covered in
/-- Use the cache and WAL window of the first acknowledged write to
recover a stopped second append. The same fresh ledger continues at the
exact table returned after the reported reboot and failed opens. -/
theorem recoversInterruptedSecondAppend (wrote : observedFirstWrite) :
    ∃ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path)
      (firstBatch : List WAL.Write) (firstTable : PackedTable) (next : NativeOpenedPosition opened.handle)
      (sameDirectory : next.current.ready.state.session.directory = opened.start.current.ready.state.session.directory),
      let nextCache : OpenSyncCacheRefs opened.handle.files next.current.ready.state.session.directory.path :=
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
      call entry = .ok opened.handle.table opened.start.reached ∧
      request.runOnRawOpenPhase directory lookup (appender.run seed.activeRef) (stager.run seed.pendingRef)
        (syncer.group directory.path seed.directoryRef seed.activeRef seed.pendingRef)
        rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
      prepareBatch opened.start.current.ready.state.writer.installed.table request.rows = some (firstBatch, firstTable) ∧
      cache.directory = seed.directoryRef ∧ cache.active = seed.activeRef ∧ cache.pending = seed.pendingRef ∧
      next.reached = reached ∧ next.current.history = firstBatch ∧
      opened.start.current.LedgerSuffix [.acknowledged request firstBatch] next.current ∧
      ∀ (_firstNames : opened.start.WalNameEffects appender stager syncer cache request lookup rename storage 0
          next.current.history.length)
        (_restore : ∀ {preReady installed}, opened.handle.set opened.handle.phase (.ready installed) preReady = .ok () reached →
          WalNamePresenceFrame opened.start.current.ready.state.session.directory 0 next.current.history.length
            (storage preReady) (storage reached)),
        next.ContinuesAfterInterruptedAppend clientView
          (FreshBootstrapKeeperPhysical.inodes (FreshBootstrapOpenHeap.keeperPhysical seen)) runs storage nextCache
          opened.start.current [.acknowledged request firstBatch] 0 := by
  obtain ⟨cache, firstBatch, firstTable, next, sameDirectory, atOpen, write, prepared, _, _, directoryRef, activeRef,
    pendingRef, exactHeap, _, history, prior, physical, _, _, carries⟩ :=
    opened.acknowledgesFirstWriteWithWindow seen resolved used runs files through createdKeeps createdWal rootNames
      liveChildren directoryEffect allocation returnedAt phaseFrame tokenFrame phaseInodes tokenInodes
      modeledFiles references atDirectory census cacheAt appender stager syncer inode buffered request lookup rename nonempty wrote
  refine ⟨cache, firstBatch, firstTable, next, sameDirectory, atOpen, write, prepared, directoryRef, activeRef,
    pendingRef, exactHeap, history, prior, ?_⟩
  intro firstNames restore
  have budget : next.current.history.length ≤ through := by
    simpa only [history, (prepareBatch_spec prepared).1] using covered
  exact @NativeOpenedPosition.opensReadyAfterInterruptedAppend heap opened.handle next clientView
    seen.keeperPhysical.inodes runs storage _ physical.physical 0 (carries _ budget firstNames restore)
    opened.start.current [.acknowledged request firstBatch] prior

end FirstAcknowledgement

end BootstrapWriteEntry

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
    (covered : NativeReturnedCalls.ReadyResponses calls) :
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
  have physical := opened.readyCallStorage used resolved writes view storage (fun atHeap => (inodes atHeap).visible)
    census cacheAt settled
  obtain ⟨last, events, heap, pins, stored, length, records, ledger, budget, _, names⟩ :=
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
    (covered : NativeReturnedCalls.ReadyResponses calls) :
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
