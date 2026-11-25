import Alvoki.Storage.Disk.NativeFreshTableOpen
import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeEarlyCheckpointTerminal

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

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

/-- The common execution consumes the empty ledgers derived by the
fresh installer. This applies to both same-handle and later sessions. -/
theorem refinesTrace (trace : NativeExecutionTrace opened.start.current events last) :
    last.history = events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
    InstalledClientReplay last.submissions last.ready.reads last.history
      last.ready.state.writer.installed last.ready.state.session := by
  simpa only [opened.emptyHistory, opened.emptySubmissions, opened.emptyReads, List.nil_append]
    using trace.keyValueRefinement

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

/-- The fresh public open starts with settled physical storage on its
returned heap. The keeper create frames the listed lock and absent
manifest. The final directory barrier supplies the child bindings, and
installing the phase and token keeps the same recovery footprint. -/
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
    (allocated : (observe raw.markerDirectory.reached).Frames opened.start.current.ready.state.crashPath
      (observe opened.start.reached)) :
    NativeReadyStorage opened.start.current.ready.state (observe opened.start.reached) := by
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
  obtain ⟨_, _, keeperBinding, keeperObject, _⟩ := report.handoff.preservesKeeper
  obtain ⟨_, _, _, _, _, _, markerBinding, _⟩ := report.marker.settledInode
  have markerObject : report.marker.renamedView.modelObject report.marker.stageChild.child = report.marker.inodeState.active := by
    rw [report.handoff.renameObjects, ← report.handoff.stageObjects]
    exact report.marker.stageInode.symm
  obtain ⟨_, _, _, _, _, _, _, _, keeperBytes, markerBytes, _⟩ := seen.markerPhysical.settles
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
  apply NativeReadyStorage.frame _ allocated
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

/-- End at the checkpoint issued on the heap of the preceding returned
call. Both the prior replay and the stop use the same opened position. -/
def stopsAfterWrites {last : NativeOpenedPosition opened.handle} {requests : List WriteRequest}
    (trace : NativeOpenedTrace opened.start (requests.map NativeOpenedInstruction.write) events last)
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stop : NativeCheckpointSourceStop last primitives fsync stage reason reached)
    {storage : heap → CheckpointStorageObservation}
    (early : stage = .syncRunsDirectory ∨ ∃ index, stage = .syncRun index)
    (stable : NativeReadyStorage last.current.ready.state (storage reached.2))
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop last.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.handle.contents after.2 opened.handle.phase = opened.handle.contents before.2 opened.handle.phase)
    (stoppedKeeps : opened.handle.contents reached.2 opened.handle.phase =
      opened.handle.contents stop.atIssue.2 opened.handle.phase) :
    NativeReachedExecutionPrefix opened.start.current (requests.map NativeExecutionInstruction.write) .checkpoint :=
  stop.terminalPrefix early stable returnedKeeps stoppedKeeps (trace.writeInstructions rfl) trace.common

end FreshBootstrapOpenHeap.Returned
end Alvoki.Storage.DiskSession
