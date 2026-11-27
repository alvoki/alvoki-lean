import Alvoki.Storage.Disk.NativePublishedWriteSnapshot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair WalSegmentCommit
open WAL.Boundary (WalInodeImage)

variable {heap image : Type} {opened : NativeOpenedHandle heap}

abbrev NativeReadyWriteCalls.cacheAtPosition (writes : NativeReadyWriteCalls opened)
    (position : NativeOpenedPosition opened) :
    OpenSyncCacheRefs opened.files position.current.ready.state.session.directory.path :=
  ⟨writes.cache.directory, writes.cache.active, writes.cache.pending, writes.cache.references,
    (congrArg DiskDirectory.path position.directory).symm ▸ writes.cache.atRoot⟩

abbrev NativeReadyWriteCalls.StorageAt (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (storage : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (position : NativeOpenedPosition opened) : Prop :=
  position.WriteStorageEntry view (writes.cacheAtPosition position)
    (storage position.reached) (visible position.reached)

/-- Dispatch the same observed write at the refined position's
directory and cache. The result retains its original outcome tag and
heap, including an ordinary commit-unknown return. -/
theorem NativeReadyWriteCalls.returnedWriteAt (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) {issuer : opened.LatestIssuer} {pins : List DiskSnapshotPin}
    {request : WriteRequest} {result : Except DiskWriteError UInt64} {reached : heap}
    (observed : (NativeReturnedCall.write request result).Reaches writes issuer pins start.reached reached) :
    let directory := start.current.ready.state.session.directory
    let cache := writes.cacheAtPosition start
    request.runOnRawOpenPhase directory writes.lookup (writes.appender.run cache.active)
      (writes.stager.run cache.pending) (writes.syncer.group directory.path cache.directory cache.active cache.pending)
      writes.rename opened.phase opened.get opened.set start.reached =
      match result with | .ok sequence => .ok sequence reached | .error cause => .error cause reached := by
  change request.runOnRawOpenPhase start.current.ready.state.session.directory writes.lookup
    (writes.appender.run writes.cache.active) (writes.stager.run writes.cache.pending)
    (writes.syncer.group start.current.ready.state.session.directory.path writes.cache.directory writes.cache.active
      writes.cache.pending) writes.rename opened.phase opened.get opened.set start.reached = _
  rw [start.directory]
  cases result <;> exact observed

/-- The name-only frames of the reached ready primitives. This contract
does not select a later write's result or add physical facts outside
the specified interval. -/
structure NativeReadyWriteCalls.WalWindowEffects (writes : NativeReadyWriteCalls opened)
    (storage : heap → CheckpointStorageObservation) (first through : Nat) : Prop where
  write : ∀ (start : NativeOpenedPosition opened) (request : WriteRequest) {issuer : opened.LatestIssuer}
      {pins : List DiskSnapshotPin} {sequence : UInt64} {reached : heap},
    request.rows ≠ [] →
    (NativeReturnedCall.write request (.ok sequence)).Reaches writes issuer pins start.reached reached →
    start.WalNameEffects writes.appender writes.stager writes.syncer (writes.cacheAtPosition start)
      request writes.lookup writes.rename storage first through ∧
    ∀ {settled value}, opened.set opened.phase (.ready value) settled = .ok () reached →
      WalNamePresenceFrame start.current.ready.state.session.directory first through (storage settled) (storage reached)
  acquire : ∀ (start : NativeOpenedPosition opened) {table : PackedTable} {reached : heap},
    opened.set opened.phase (.ready { start.current.ready.state.writer.installed with table })
      start.reached = .ok () reached →
    WalNamePresenceFrame start.current.ready.state.session.directory first through (storage start.reached) (storage reached)
  guardLookup : ∀ (start : NativeOpenedPosition opened) {cause : IO.Error} {reached : heap},
    reached ≠ start.reached →
    checkActiveSegmentWith opened.directory start.current.ready.state.writer.installed writes.lookup start.reached =
      .error cause reached →
    WalNamePresenceFrame start.current.ready.state.session.directory first through (storage start.reached) (storage reached)

/-- The frame changes only the namespace observation. Updating the
in-memory table leaves the writer's segment starts in place. -/
private theorem NativeOpenedPosition.keepsWalWindow {start next : NativeOpenedPosition opened}
    {storage : heap → CheckpointStorageObservation} {first through : Nat} {table : PackedTable}
    (updated : next.current.ready.state = start.current.ready.state.withTable table)
    (frame : WalNamePresenceFrame start.current.ready.state.session.directory first through
      (storage start.reached) (storage next.reached))
    (initial : start.WalWindowAt storage first through) :
    next.WalWindowAt storage first through := by
  unfold NativeOpenedPosition.WalWindowAt at *
  rw [updated]
  exact ⟨initial.1, frame.preservesNamespaceWindow initial.2⟩

/-- An in-memory table update or metadata lookup can advance the heap
while preserving the files and references used by the next write. -/
structure NativeReadyWriteCalls.StorageFrame (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (storage : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (start : NativeOpenedPosition opened) (reached : heap) : Prop where
  census : view.descriptors reached = view.descriptors start.reached
  cache : view.cacheAt reached writes.cache.directory writes.cache.active writes.cache.pending =
    view.cacheAt start.reached writes.cache.directory writes.cache.active writes.cache.pending
  files : (storage start.reached).Frames start.current.ready.state.crashPath (storage reached)
  keeper : ∀ inode, (storage start.reached).files.names
    (start.current.ready.state.session.directory.file (.walSegment start.current.ready.state.writer.wal.active.first)) =
      some inode → visible reached inode = visible start.reached inode

private theorem NativeReadyWriteCalls.keepsStorage (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (storage : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) {start next : NativeOpenedPosition opened} {table : PackedTable}
    (initial : writes.StorageAt view storage visible start)
    (updated : next.current.ready.state = start.current.ready.state.withTable table)
    (frame : writes.StorageFrame view storage visible start next.reached) :
    writes.StorageAt view storage visible next := by
  have retained := initial.physical.frame frame.files
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [updated]
    exact frame.census.trans initial.census
  · change view.cacheAt next.reached writes.cache.directory writes.cache.active writes.cache.pending = _
    rw [updated]
    exact frame.cache.trans initial.cacheAt
  · rw [updated]
    exact ⟨⟨retained.directoryBound, retained.lockBound, retained.manifest, retained.sealedFiles, retained.runs⟩,
      retained.marker, retained.keeper, retained.settled⟩
  · intro inode bound
    rw [updated] at bound ⊢
    have before := (frame.files.visible _ (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))).1.symm.trans bound
    exact (frame.keeper inode before).trans (initial.keeper inode before)
  · intro handle cached
    have directory := congrArg SyncHandleRouting.Cache.directory frame.cache
    change (view.directory next.reached writes.cache.directory).map (view.handle next.reached) =
      (view.directory start.reached writes.cache.directory).map (view.handle start.reached) at directory
    rw [cached, Option.map_some] at directory
    cases previous : view.directory start.reached writes.cache.directory with
    | none => simp [previous] at directory
    | some original =>
      rw [previous, Option.map_some] at directory
      have same := Option.some.inj directory
      rw [updated, same]
      exact (frame.files.visible _ (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr (.inl rfl))))).1.trans
        (initial.root original previous)

private theorem NativeReadyState.withInstalledTable {state : NativeReadyState}
    (valid : state.Valid) : state.withTable state.writer.installed.table = state := by
  cases state with
  | mk session writer census cache owner directorySlot =>
    cases writer
    cases session
    simp [NativeReadyState.withTable, SegmentedWriterState.withTable]
    exact valid.phase.symm

/-- The no-follow check uses exactly one observed metadata lookup.
Its pure decision uses that response, and both outcomes retain that
lookup's returned heap. -/
private theorem NativeReadyWriteCalls.rawGuardResult (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) :
    let installed := start.current.ready.state.writer.installed
    let lookup := nativeWriteLookupAt writes.lookup start.reached
    let reached := (lookup (opened.directory.file (.walSegment installed.activeFirst))).2
    checkActiveSegmentWith opened.directory installed writes.lookup start.reached =
      match (checkActiveSegmentWith opened.directory installed (fun path => (lookup path).1) :
        Except IO.Error Unit) with
      | .ok value => .ok value reached
      | .error cause => .error cause reached := by
  intro installed lookup reached
  rw [checkActiveSegmentWith_rawResult]
  cases observed : writes.lookup (opened.directory.file (.walSegment installed.activeFirst)) start.reached with
  | error cause heap =>
    simp [checkActiveSegmentWith, lookup, reached, nativeWriteLookupAt, observed, Bind.bind, Except.bind]
  | ok metadata heap =>
    simp [checkActiveSegmentWith, lookup, reached, nativeWriteLookupAt, observed, Bind.bind, Except.bind]
    split <;> simp_all

/-- An uncertain submission ends the ready epoch. The remaining
responses are classified at the actual step using its callback laws. -/
def NativeReturnedCall.ReadyResponse (call : NativeReturnedCall opened) : Prop :=
  match call with
  | .write _ (.error (.commitUnknown _)) => False
  | _ => True

/-- Restrict the ready fold by the observed response, independently of
the semantics admitting the raw sequence. -/
def NativeReturnedCalls.ReadyResponses (calls : List (NativeReturnedCall opened)) : Prop :=
  ∀ call ∈ calls, call.ReadyResponse

/-- Native file callbacks preserve the opened phase cell. These
projections are available independently of the whole write response. -/
structure NativeReadyWriteCalls.WritePhaseFrames (writes : NativeReadyWriteCalls opened) : Prop where
  lookup : ∀ {path before after metadata}, writes.lookup path before = .ok metadata after →
    opened.contents after opened.phase = opened.contents before opened.phase
  append : ∀ path bytes before, opened.contents
    (reachedState (writes.appender.run writes.cache.active path bytes before)) opened.phase =
      opened.contents before opened.phase
  stage : ∀ path bytes before, opened.contents
    (reachedState (writes.stager.run writes.cache.pending path bytes before)) opened.phase =
      opened.contents before opened.phase
  sync : ∀ paths before, opened.contents (reachedState (writes.syncer.group opened.directory.path
    writes.cache.directory writes.cache.active writes.cache.pending paths before)) opened.phase =
      opened.contents before opened.phase
  rename : ∀ source target before, opened.contents (reachedState (writes.rename source target before)) opened.phase =
    opened.contents before opened.phase

private theorem NativeReadyWriteCalls.poisonsAfterGuard (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) (frames : writes.WritePhaseFrames) {guarded : heap}
    (accepted : checkActiveSegmentWith opened.directory start.current.ready.state.writer.installed writes.lookup
      start.reached = .ok () guarded) :
    ∃ poisoned, opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned := by
  obtain ⟨_, lookedUp⟩ := BatchActiveGuard.ofRawChecked writes.lookup accepted
  exact opened.phaseEffects.writes guarded opened.phase _ .poisoned
    ((frames.lookup lookedUp).trans start.stored)

private theorem NativeReadyWriteCalls.keepsPhaseThroughPublication (writes : NativeReadyWriteCalls opened)
    (frames : writes.WritePhaseFrames) (first : Nat) (bytes : ByteArray) (count : Nat) (entry : heap) :
    let cache := writes.cache
    let root := opened.directory
    opened.contents (reachedState (commitBytesAt root first bytes count
      (writes.appender.run cache.active) (writes.stager.run cache.pending)
      (writes.syncer.group root.path cache.directory cache.active cache.pending) writes.rename entry)) opened.phase =
      opened.contents entry opened.phase :=
  commitBytesAt_frames (fun before after => opened.contents after opened.phase = opened.contents before opened.phase)
    (fun _ => rfl) (fun earlier later => later.trans earlier) opened.directory first bytes count
    (writes.appender.run writes.cache.active) (writes.stager.run writes.cache.pending)
    (writes.syncer.group opened.directory.path writes.cache.directory writes.cache.active writes.cache.pending)
    writes.rename entry (frames.append _ _ _) (frames.stage _ _) (frames.sync _) (frames.rename _ _) (frames.sync _)

/-- After successful pure preparation, an actual rejection comes from
the metadata guard. The live phase cell allows both setters to succeed
whenever the preceding file callbacks reach them. -/
private theorem NativeReadyWriteCalls.rejectedAtGuard (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) {issuer : opened.LatestIssuer} {pins : List DiskSnapshotPin}
    {request : WriteRequest} {cause : IO.Error} {reached : heap} {batch : List WAL.Write} {table : PackedTable}
    (observed : (NativeReturnedCall.write request (.error (.rejected cause))).Reaches
      writes issuer pins start.reached reached)
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch start.current.ready.state.writer.installed.table request.rows = some (batch, table))
    (fits : start.current.ready.state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (frames : writes.WritePhaseFrames) :
    checkActiveSegmentWith opened.directory start.current.ready.state.writer.installed writes.lookup start.reached =
      .error cause reached := by
  let installed := start.current.ready.state.writer.installed
  let root := opened.directory
  let count := installed.walBytes + WAL.frameSize * request.rows.length
  let next : Installed := { installed with table, walBytes := count }
  let append := writes.appender.run writes.cache.active
  let stage := writes.stager.run writes.cache.pending
  let sync := writes.syncer.group root.path writes.cache.directory writes.cache.active writes.cache.pending
  let publish := commitBytesAt root installed.activeFirst (WAL.encodeBatch batch) count append stage sync writes.rename
  have stored := start.stored.trans (congrArg some start.current.ready.readPrefix.refines.1.phase)
  have loaded := opened.phaseEffects.reads start.reached opened.phase (.ready installed) stored
  have returned : request.runOnRawOpenPhase root writes.lookup append stage sync writes.rename
      opened.phase opened.get opened.set start.reached = .error (.rejected cause) reached := observed
  rw [request.runOnRawOpenPhase_afterPreparation root writes.lookup append stage sync writes.rename
    opened.phase opened.get opened.set loaded nonempty prepared fits] at returned
  change (match checkActiveSegmentWith root installed writes.lookup start.reached with
    | .error diagnostic after => .error (.rejected diagnostic) after
    | .ok () guarded => match opened.set opened.phase .poisoned guarded with
      | .error diagnostic after => .error (.rejected diagnostic) after
      | .ok () poisoned => match publish poisoned with
        | .error diagnostic after => .error (.commitUnknown diagnostic) after
        | .ok () settled => match opened.set opened.phase (.ready next) settled with
          | .error diagnostic after => .error (.rejected diagnostic) after
          | .ok () after => .ok table.committed after : EStateM.Result DiskWriteError heap UInt64) =
    .error (.rejected cause) reached at returned
  cases guard : checkActiveSegmentWith root installed writes.lookup start.reached with
  | error diagnostic after =>
    simp only [guard, EStateM.Result.error.injEq, DiskWriteError.rejected.injEq] at returned
    obtain ⟨rfl, rfl⟩ := returned
    rfl
  | ok value guarded =>
    cases value
    obtain ⟨poisoned, excludes, poisonedPhase⟩ := writes.poisonsAfterGuard start frames guard
    cases publication : publish poisoned with
    | error => simp [guard, excludes, publication] at returned
    | ok value settled =>
      cases value
      have kept : opened.contents (reachedState (publish poisoned)) opened.phase =
          opened.contents poisoned opened.phase :=
        writes.keepsPhaseThroughPublication frames installed.activeFirst (WAL.encodeBatch batch) count poisoned
      have atReadySetter : opened.contents settled opened.phase = some .poisoned := by
        rw [publication, reachedState] at kept
        exact kept.trans poisonedPhase
      obtain ⟨_, restores, _⟩ := opened.phaseEffects.writes settled opened.phase .poisoned (.ready next) atReadySetter
      simp [guard, excludes, publication, restores] at returned

/-- An empty request on the ready phase returns before publication. -/
theorem NativeReadyWriteCalls.commitUnknownHasRows (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) {issuer : opened.LatestIssuer} {pins : List DiskSnapshotPin}
    {request : WriteRequest} {cause : IO.Error} {reached : heap}
    (observed : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
      writes issuer pins start.reached reached) :
    request.rows ≠ [] := by
  intro empty
  let state := start.current.ready.state
  let root := opened.directory
  let append := writes.appender.run writes.cache.active
  let stage := writes.stager.run writes.cache.pending
  let sync := writes.syncer.group root.path writes.cache.directory writes.cache.active writes.cache.pending
  have valid := start.current.ready.readPrefix.refines.1
  have stored := start.stored.trans (congrArg some valid.phase)
  have loaded := opened.phaseEffects.reads start.reached opened.phase (.ready state.writer.installed) stored
  let seen : NativeWritePreflightObservation state request :=
    ⟨fun path => (nativeWriteLookupAt writes.lookup start.reached path).1, .ok state.writer.installed.table.committed,
      .empty empty⟩
  obtain ⟨_, _, quiet⟩ := request.runOnRawOpenPhase_preflight root writes.lookup append stage sync writes.rename
    opened.phase opened.get opened.set valid seen loaded start.directory rfl
  have returned : request.runOnRawOpenPhase root writes.lookup append stage sync writes.rename
      opened.phase opened.get opened.set start.reached = .error (.commitUnknown cause) reached := observed
  cases quiet.symm.trans returned

/-- An uncertain public return keeps the phase poisoned. Its publication
prefix uses the same phase frame as a returned successful commit. -/
theorem NativeReadyWriteCalls.commitUnknownPoisons (writes : NativeReadyWriteCalls opened)
    (start : NativeOpenedPosition opened) {issuer : opened.LatestIssuer} {pins : List DiskSnapshotPin}
    {request : WriteRequest} {cause : IO.Error} {reached : heap}
    (observed : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
      writes issuer pins start.reached reached) (frames : writes.WritePhaseFrames) :
    opened.contents reached opened.phase = some .poisoned := by
  let installed := start.current.ready.state.writer.installed
  let root := opened.directory
  let append := writes.appender.run writes.cache.active
  let stage := writes.stager.run writes.cache.pending
  let sync := writes.syncer.group root.path writes.cache.directory writes.cache.active writes.cache.pending
  have stored := start.stored.trans (congrArg some start.current.ready.readPrefix.refines.1.phase)
  have loaded := opened.phaseEffects.reads start.reached opened.phase (.ready installed) stored
  have returned : request.runOnRawOpenPhase root writes.lookup append stage sync writes.rename
      opened.phase opened.get opened.set start.reached = .error (.commitUnknown cause) reached := observed
  have nonempty := writes.commitUnknownHasRows start observed
  obtain ⟨batch, table, prepared, fits⟩ := request.runOnRawOpenPhase_prepared root writes.lookup append stage sync
    writes.rename opened.phase opened.get opened.set loaded nonempty (by rw [returned]; trivial)
  obtain ⟨guarded, poisoned, accepted, excluded, failed, _⟩ := request.runOnRawOpenPhase_commitUnknown root
    writes.lookup append stage sync writes.rename opened.phase opened.get opened.set loaded nonempty prepared fits returned
  obtain ⟨written, assigned, poisonedPhase⟩ := writes.poisonsAfterGuard start frames accepted
  have same := (EStateM.Result.ok.inj (assigned.symm.trans excluded)).2
  let count := installed.walBytes + WAL.frameSize * request.rows.length
  have kept : opened.contents (reachedState (commitBytesAt root installed.activeFirst
      (WAL.encodeBatch batch) count append stage sync writes.rename poisoned)) opened.phase =
      opened.contents poisoned opened.phase :=
    writes.keepsPhaseThroughPublication frames installed.activeFirst (WAL.encodeBatch batch) count poisoned
  rw [failed] at kept
  exact kept.trans (same ▸ poisonedPhase)

/-- These laws concern the reached native primitives. The raw call
chronology supplies the actual request, response and endpoint. -/
structure NativeReadyWriteCalls.ReturnEffects (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray) : Prop where
  writePhase : writes.WritePhaseFrames
  write : ∀ (start : NativeOpenedPosition opened) (request : WriteRequest) {issuer : opened.LatestIssuer}
      {pins : List DiskSnapshotPin} {sequence : UInt64} {reached : heap},
    request.rows ≠ [] →
    (NativeReturnedCall.write request (.ok sequence)).Reaches writes issuer pins start.reached reached →
    ∃ files : ∀ atHeap, RunDirectoryInodeView start.current.ready.state.session.directory (inodes atHeap) (runs atHeap),
      (∀ atHeap, (files atHeap).storageObservation = storage atHeap) ∧
      (∀ {batch table}, prepareBatch start.current.ready.state.writer.installed.table request.rows = some (batch, table) →
        start.PublishedWriteEffects writes.appender writes.stager writes.syncer view (writes.cacheAtPosition start)
          inodes runs files inode buffered request writes.lookup writes.rename batch)
  acquire : ∀ (start : NativeOpenedPosition opened) {table : PackedTable} {reached : heap},
    opened.set opened.phase (.ready { start.current.ready.state.writer.installed with table })
      start.reached = .ok () reached →
    writes.StorageFrame view storage (fun atHeap => (inodes atHeap).visible) start reached
  guardLookup : ∀ (start : NativeOpenedPosition opened) {cause : IO.Error} {reached : heap},
    reached ≠ start.reached →
    checkActiveSegmentWith opened.directory start.current.ready.state.writer.installed writes.lookup start.reached =
      .error cause reached →
    opened.contents reached opened.phase = opened.contents start.reached opened.phase ∧
    writes.StorageFrame view storage (fun atHeap => (inodes atHeap).visible) start reached
  readToken : ∀ (start : NativeOpenedPosition opened),
    opened.ptrEq opened.token opened.token start.reached = .ok true start.reached

/-- The horizon for a future request can be chosen from the submitted
rows before any ready call's outcome is examined. -/
def NativeReturnedCall.requestedRows : NativeReturnedCall opened → Nat
  | .write request _ => request.rows.length
  | .acquire _ | .read _ _ _ => 0

/-- A derived abstract event records the same public operands and
response. Actual admission is the independent `Reaches` relation. -/
inductive NativeReturnedCall.Records : NativeReturnedCall opened → NativeExecutionEvent → Prop where
  | write (rows : batch.map (fun entry : WAL.Write => (entry.key, entry.value)) = request.rows)
      (sequence : batch.getLast?.map WAL.Write.sequence = some number) :
      Records (.write request (.ok number)) (.acknowledged request batch)
  | preflight {state : NativeReadyState} (seen : NativeWritePreflightObservation state request) :
      Records (.write request (seen.response.mapError DiskWriteError.rejected)) (.writePreflight request seen.response)
  | acquire (pin : NativeOpenedPin opened) :
      Records (.acquire (.ok pin.raw)) (.snapshotControl .acquire (.ok (session, pin.localPin)))
  | read (pin : NativeOpenedPin opened) :
      Records (.read pin request (.ok response))
        (.snapshotHandleRead session pin.localPin.handle request response recorded)

theorem NativeReturnedCall.Records.writesBound {call : NativeReturnedCall opened} {event : NativeExecutionEvent}
    (recorded : call.Records event) : event.writes.length ≤ call.requestedRows := by
  cases recorded with
  | write rows _ =>
    have length := congrArg List.length rows
    simp only [List.length_map] at length
    exact Nat.le_of_eq length
  | preflight => exact Nat.zero_le _
  | acquire => exact Nat.le_refl _
  | read => exact Nat.le_refl _

private theorem NativeReadyWriteCalls.refinesQuietWrite (writes : NativeReadyWriteCalls opened)
    (issuer : opened.LatestIssuer) (view : OpenCloseHeapView heap image)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) {request : WriteRequest} {result : Except DiskWriteError UInt64}
    (seen : NativeWritePreflightObservation start.current.ready.state request)
    (coherent : seen.lookup = fun path => (nativeWriteLookupAt writes.lookup start.reached path).1)
    {known : List DiskSnapshotPin} {reached : heap}
    (observed : (NativeReturnedCall.write request result).Reaches writes issuer known start.reached reached)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (next : NativeOpenedPosition opened) (event : NativeExecutionEvent),
      next.reached = reached ∧ next.pins.map NativeOpenedPin.raw = start.pins.map NativeOpenedPin.raw ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) next ∧
      (NativeReturnedCall.write (opened := opened) request result).Records event ∧ start.current.LedgerSuffix [event] next.current ∧
      (next.current.ready.state.writer.target.pair.manifest = start.current.ready.state.writer.target.pair.manifest ∧
        next.current.ready.state.writer.wal.sealed = start.current.ready.state.writer.wal.sealed) ∧
      (∀ {first through}, writes.WalWindowEffects storage first through →
        start.WalWindowAt storage first through → next.WalWindowAt storage first through) := by
  let state := start.current.ready.state
  have valid := start.current.ready.readPrefix.refines.1
  have load := opened.phaseEffects.reads start.reached opened.phase state.session.phase start.stored
  rw [valid.phase] at load
  obtain ⟨quietHeap, _, preflight⟩ := request.runOnRawOpenPhase_preflight opened.directory writes.lookup
    (writes.appender.run writes.cache.active) (writes.stager.run writes.cache.pending)
    (writes.syncer.group opened.directory.path writes.cache.directory writes.cache.active writes.cache.pending)
    writes.rename opened.phase opened.get opened.set valid seen load start.directory coherent
  have exactResult : result = seen.response.mapError DiskWriteError.rejected := by
    let atReturn : Except DiskWriteError UInt64 → EStateM.Result DiskWriteError heap UInt64
      | .ok value => .ok value reached
      | .error cause => .error cause reached
    have same : seen.resultAt quietHeap = atReturn result := preflight.symm.trans (by
      cases result <;> exact observed)
    cases result <;> cases response : seen.response <;>
      simp [atReturn, NativeWritePreflightObservation.resultAt, response, Except.mapError] at same ⊢
    all_goals exact same.1.symm
  subst result
  let lookedUp := (nativeWriteLookupAt writes.lookup start.reached
    (opened.directory.file (.walSegment state.writer.installed.activeFirst))).2
  have failedGuard (different : reached ≠ start.reached) (path : seen.ReturnHeap start.reached lookedUp reached) :
      ∃ cause, checkActiveSegmentWith opened.directory state.writer.installed writes.lookup start.reached =
        .error cause reached := by
    rcases path with unchanged | ⟨cause, _, rejected, exactHeap⟩
    · exact False.elim (different unchanged)
    · rw [start.directory, coherent] at rejected
      refine ⟨cause, ?_⟩
      rw [writes.rawGuardResult start, rejected, exactHeap]
  have lookupFrame (different : reached ≠ start.reached) (path : seen.ReturnHeap start.reached lookedUp reached) :
      opened.contents reached opened.phase = opened.contents start.reached opened.phase ∧
      writes.StorageFrame view storage (fun atHeap => (inodes atHeap).visible) start reached := by
    obtain ⟨_, actual⟩ := failedGuard different path
    exact effects.guardLookup start different actual
  obtain ⟨next, nextHeap, current, pins, ledger, path⟩ :=
    start.preflightsReturnedWrite writes issuer known seen coherent observed
      (fun different path => (lookupFrame different path).1)
  have frame : writes.StorageFrame view storage (fun atHeap => (inodes atHeap).visible) start next.reached := by
    rw [nextHeap]
    by_cases same : reached = start.reached
    · rw [same]
      exact ⟨rfl, rfl, .refl _ _, fun _ _ => rfl⟩
    · exact (lookupFrame same path).2
  have updated : next.current.ready.state = state.withTable state.writer.installed.table :=
    (congrArg (fun position : NativeExecutionPosition => position.ready.state) current).trans
      (NativeReadyState.withInstalledTable valid).symm
  refine ⟨next, .writePreflight request seen.response, nextHeap, congrArg (List.map NativeOpenedPin.raw) pins,
    writes.keepsStorage view storage _ initial updated frame, .preflight seen, ledger, ?_, ?_⟩
  · rw [updated]
    exact ⟨rfl, rfl⟩
  · intro first through names window
    apply NativeOpenedPosition.keepsWalWindow updated _ window
    rw [nextHeap]
    by_cases same : reached = start.reached
    · rw [same]
      exact .refl _
    · obtain ⟨_, actual⟩ := failedGuard same path
      exact names.guardLookup start same actual

private theorem NativeReturnedCall.refinesReady
    (call : NativeReturnedCall opened) (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) {known : List DiskSnapshotPin} {reached : heap}
    (observed : call.Reaches writes issuer known start.reached reached) (covered : call.ReadyResponse)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (next : NativeOpenedPosition opened) (event : NativeExecutionEvent),
      next.reached = reached ∧
      next.pins.map NativeOpenedPin.raw = call.pinsAfter (start.pins.map NativeOpenedPin.raw) ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) next ∧
      call.Records event ∧ start.current.LedgerSuffix [event] next.current ∧
      (next.current.ready.state.writer.target.pair.manifest = start.current.ready.state.writer.target.pair.manifest ∧
        next.current.ready.state.writer.wal.sealed = start.current.ready.state.writer.wal.sealed) ∧
      (∀ {first through}, writes.WalWindowEffects storage first through →
        start.WalWindowAt storage first through → next.WalWindowAt storage first through) := by
  cases call with
  | write request result =>
    let state := start.current.ready.state
    let lookup := fun path => (nativeWriteLookupAt writes.lookup start.reached path).1
    cases result with
    | error failure =>
      cases failure with
      | commitUnknown => exact False.elim covered
      | rejected cause =>
        have quiet : ∃ seen : NativeWritePreflightObservation state request, seen.lookup = lookup := by
          by_cases empty : request.rows = []
          · exact ⟨⟨lookup, .ok state.writer.installed.table.committed, .empty empty⟩, rfl⟩
          by_cases fits : state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size
          · cases prepared : prepareBatch state.writer.installed.table request.rows with
            | none => exact ⟨⟨lookup, _, .rejected (.sequence empty fits prepared)⟩, rfl⟩
            | some ready =>
              obtain ⟨batch, table⟩ := ready
              have actual := writes.rejectedAtGuard start observed empty prepared fits effects.writePhase
              rw [writes.rawGuardResult start] at actual
              have pureGuard : (checkActiveSegmentWith state.session.directory state.writer.installed lookup :
                  Except IO.Error Unit) = .error cause := by
                rw [start.directory]
                let decision := (checkActiveSegmentWith opened.directory state.writer.installed lookup :
                  Except IO.Error Unit)
                change decision = .error cause
                change (match decision with
                  | .ok value => .ok value _
                  | .error diagnostic => .error diagnostic _) =
                  EStateM.Result.error cause reached at actual
                cases outcome : decision with
                | ok value => rw [outcome] at actual; cases actual
                | error diagnostic =>
                  rw [outcome] at actual
                  exact congrArg Except.error (EStateM.Result.error.inj actual).1
              exact ⟨⟨lookup, .error cause, .rejected (.active empty fits prepared pureGuard)⟩, rfl⟩
          · exact ⟨⟨lookup, _, .rejected (.byteCount empty (Nat.le_of_not_gt fits))⟩, rfl⟩
        obtain ⟨seen, coherence⟩ := quiet
        exact writes.refinesQuietWrite issuer view inodes runs storage inode buffered effects start
          seen coherence observed initial
    | ok sequence =>
      by_cases empty : request.rows = []
      · let seen : NativeWritePreflightObservation state request :=
          ⟨lookup, .ok state.writer.installed.table.committed, .empty empty⟩
        exact writes.refinesQuietWrite issuer view inodes runs storage inode buffered effects start
          seen rfl observed initial
      · have nonempty : request.rows ≠ [] := empty
        obtain ⟨files, sameStorage, callbacks⟩ := effects.write start request nonempty observed
        let cache := writes.cacheAtPosition start
        have raw := writes.returnedWriteAt start observed
        have seen : start.ObservesPublishedWrite writes.appender writes.stager writes.syncer view cache inodes runs
            storage inode buffered request writes.lookup writes.rename sequence reached :=
          ⟨files, sameStorage, raw, callbacks⟩
        obtain ⟨_, _, batch, table, next, _, prepared, committed, atHeap, pins, _, ledger, ready, _,
          retainedCheckpoint, keepsNames⟩ :=
          start.acknowledgesObservedWrite writes.appender writes.stager writes.syncer view cache inodes runs
            storage inode buffered request writes.lookup writes.rename nonempty initial seen
        obtain ⟨length, replayed, rows, numbered⟩ := prepareBatch_spec prepared
        have lastSequence : batch.getLast?.map WAL.Write.sequence = some sequence := by
          rcases List.eq_nil_or_concat batch with empty | ⟨earlier, last, appended⟩
          · exfalso
            apply nonempty
            apply List.length_eq_zero_iff.mp
            simpa only [empty, List.length_nil] using length.symm
          · subst batch
            rw [List.concat_eq_append] at numbered replayed ⊢
            obtain ⟨ordinal, _⟩ : last.sequence.toNat =
                start.current.ready.state.writer.installed.table.committed.toNat + 1 + earlier.length ∧ True :=
              ((ordinals_append_iff _ earlier [last]).mp numbered).2
            have count := replay_committed_count _ replayed
            simp only [List.length_append, List.length_cons, List.length_nil] at count
            have number : last.sequence = sequence := UInt64.toNat_inj.mp (by
              rw [committed]
              omega)
            simp [number]
        refine ⟨next, .acknowledged request batch, atHeap, congrArg (List.map NativeOpenedPin.raw) pins, ready,
          .write rows lastSequence, ledger, retainedCheckpoint, ?_⟩
        intro first through names window
        obtain ⟨phaseNames, restore⟩ := names.write start request nonempty observed
        exact keepsNames window.1 window.2 phaseNames restore
  | acquire result =>
    cases result with
    | error cause =>
      have raw : opened.acquireLatestRaw issuer.val start.reached = .error cause reached := observed
      obtain ⟨_, _, impossible, _⟩ := start.refinesAcquireLatest issuer raw
      cases impossible
    | ok returned =>
      have raw : opened.acquireLatestRaw issuer.val start.reached = .ok returned reached := observed
      obtain ⟨next, pin, actual, pins, acquired⟩ := start.refinesAcquireLatest issuer raw
      obtain ⟨samePin, sameHeap⟩ := EStateM.Result.ok.inj actual
      subst returned
      obtain ⟨_, _, table, _, _, _, _, setter, _, updated, _⟩ := acquired.returned
      rw [updated] at setter
      have framed := effects.acquire start (table := table) setter
      have ready := writes.keepsStorage view storage (fun atHeap => (inodes atHeap).visible) initial updated framed
      refine ⟨next, .snapshotControl .acquire (.ok (start.current.ready.state.session.sessionRef, pin.localPin)),
        sameHeap.symm, ?_, ready, .acquire pin, acquired.common.ledgerSuffix, ?_, ?_⟩
      · simp only [pins, List.map_append, List.map_cons, List.map_nil, pinsAfter]
      · rw [updated]
        exact ⟨rfl, rfl⟩
      · intro first through names window
        exact NativeOpenedPosition.keepsWalWindow updated (names.acquire start setter) window
  | read pin request result =>
    obtain ⟨_, value, recorded, readPosition, read, returned, _⟩ :=
      start.current.ready.readsOpenPin opened.table start.uses pin.issued
        (fun phase => opened.phaseEffects.reads start.reached opened.phase phase)
        start.stored opened.ptrEq (effects.readToken start) request
    cases result with
    | error cause =>
      have actual : opened.readPinRaw pin request start.reached = .error cause reached := observed.2
      cases returned.symm.trans actual
    | ok response =>
      have actual : opened.readPinRaw pin request start.reached = .ok response reached := observed.2
      have ⟨responseEq, heapEq⟩ := EStateM.Result.ok.inj (returned.symm.trans actual)
      subst response
      let next : NativeOpenedPosition opened :=
        ⟨⟨start.current.history, start.current.submissions, readPosition⟩, start.reached,
          read.state.symm ▸ start.directory, read.state.symm ▸ start.stored, start.pins⟩
      let event := NativeExecutionEvent.snapshotHandleRead start.current.ready.state.session.sessionRef
        pin.localPin.handle request value recorded
      have continued : NativeExecutionStep start.current event next.current :=
        .snapshotHandleRead start.current ⟨pin.localPin.handle, start.current.ready.state.session.sessionRef, true, by simp⟩
          request value recorded readPosition read
      have ready : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) next := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        all_goals
          simp only [next, read.state]
        · exact initial.census
        · exact initial.cacheAt
        · exact initial.physical
        · exact initial.keeper
        · exact initial.root
      refine ⟨next, event, heapEq, rfl, ready, .read pin, continued.ledgerSuffix, ?_, ?_⟩
      · simp only [next, read.state, and_self]
      · intro first through _ window
        simpa only [NativeOpenedPosition.WalWindowAt, next, read.state] using window

/-- Refine any finite supported ready sequence on the fixed public
dispatcher. The next transition uses the preceding returned heap,
actual pins, and physical write entry derived by that transition.
The final witness keeps the initial manifest and exact sealed segment list. -/
theorem NativeReturnedCalls.refinesReadyFramed
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (covered : NativeReturnedCalls.ReadyResponses calls)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) (sameEntry : start.reached = entry)
    (samePins : start.pins.map NativeOpenedPin.raw = known)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      last.reached = reached ∧
      last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins call => call.pinsAfter pins) known ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      start.current.LedgerSuffix events last.current ∧
      last.current.history.length ≤ start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum ∧
      (last.current.ready.state.writer.target.pair.manifest = start.current.ready.state.writer.target.pair.manifest ∧
        last.current.ready.state.writer.wal.sealed = start.current.ready.state.writer.wal.sealed) ∧
      (∀ {first through}, writes.WalWindowEffects storage first through →
        start.WalWindowAt storage first through → last.WalWindowAt storage first through) := by
  induction executed generalizing start with
  | empty =>
    exact ⟨start, [], sameEntry, samePins, initial, rfl, by simp, .empty _, by simp,
      ⟨rfl, rfl⟩, fun _ window => window⟩
  | @cons middle rest last before known call observed _ ih =>
    have atStart : call.Reaches writes issuer known start.reached middle := sameEntry ▸ observed
    have first := covered call List.mem_cons_self
    obtain ⟨next, event, nextHeap, pins, ready, recorded, firstLedger, firstCheckpoint, firstFrame⟩ :=
      call.refinesReady writes issuer view inodes runs storage inode buffered effects start atStart first initial
    have tail : NativeReturnedCalls.ReadyResponses rest :=
      fun call member => covered call (List.mem_cons_of_mem _ member)
    obtain ⟨finish, events, done, finalPins, physical, length, records, ledger, lengthBound, finalCheckpoint, finalFrame⟩ :=
      ih tail next nextHeap
        (pins.trans (congrArg call.pinsAfter samePins)) ready
    refine ⟨finish, event :: events, done, finalPins, physical, by simp [length], ?_, firstLedger.append ledger, ?_,
      ⟨finalCheckpoint.1.trans firstCheckpoint.1, finalCheckpoint.2.trans firstCheckpoint.2⟩,
      fun names window => finalFrame names (firstFrame names window)⟩
    · intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact recorded
      · exact records pair member
    · have appended := congrArg List.length firstLedger.history
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append] at appended
      have requested := recorded.writesBound
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The client sequence that can follow a newly installed writer. Its observations
start at the returned heap with fresh pins and extend the incoming ledger. -/
abbrev NativeOpenedPosition.ContinuesReadyCalls (start : NativeOpenedPosition opened)
    (refs : OpenSyncCacheRefs opened.files start.current.ready.state.session.directory.path)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation) (origin : NativeExecutionPosition)
    (earlier : List NativeExecutionEvent) (lower : Nat) : Prop :=
    ∀ (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
      (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
      (rename : FilePath → FilePath → EStateM IO.Error heap Unit),
      let writes := start.readyWriteCalls refs appender stager syncer lookup rename
      ∀ (issuer : opened.LatestIssuer) (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
        (_reported : writes.ReturnEffects view inodes runs observe inode buffered)
        {calls : List (NativeReturnedCall opened)} {reached : heap},
        NativeReturnedCalls writes issuer start.reached [] calls reached →
        NativeReturnedCalls.ReadyResponses calls →
        ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
          last.reached = reached ∧
          last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins call => call.pinsAfter pins) [] ∧
          writes.StorageAt view observe (fun atHeap => (inodes atHeap).visible) last ∧
          events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
          origin.LedgerSuffix (earlier ++ events) last.current ∧
          InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
            last.current.ready.state.writer.installed last.current.ready.state.session ∧
          ∀ extra, (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, lower ≤ offset) →
            writes.WalWindowEffects observe lower
              (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + extra) →
            last.WalWindowAt observe lower (last.current.history.length + extra)

/-- Any installer that supplies the fresh pins, storage entry and settled
namespace can use the same ready dispatcher for subsequent calls. -/
theorem NativeOpenedPosition.continuesReadyCalls (start : NativeOpenedPosition opened)
    (refs : OpenSyncCacheRefs opened.files start.current.ready.state.session.directory.path)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation) (origin : NativeExecutionPosition)
    (earlier : List NativeExecutionEvent) (lower : Nat) (emptyPins : start.pins = [])
    (across : origin.LedgerSuffix earlier start.current)
    (entry : start.WriteStorageEntry view refs (observe start.reached) (inodes start.reached).visible)
    (settled : ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
      start.current.ready.state.session.directory lower through (observe start.reached)) :
    start.ContinuesReadyCalls refs view inodes runs observe origin earlier lower := by
  intro appender stager syncer lookup rename writes issuer inode buffered reported calls reached executed covered
  have initial : writes.StorageAt view observe (fun atHeap => (inodes atHeap).visible) start := entry
  obtain ⟨last, events, atHeap, pins, physical, length, records, ledger, budget, _, frames⟩ :=
    executed.refinesReadyFramed covered view inodes runs observe inode buffered reported start rfl
      (by rw [emptyPins]; rfl) initial
  refine ⟨last, events, atHeap, pins, physical, length, records, across.append ledger,
    last.current.ready.readPrefix.guardedReplay, ?_⟩
  intro extra covers names
  exact (frames names ⟨covers, settled _⟩).restrictUpper (Nat.add_le_add_right budget extra)

/-- The ready proof alone does not need namespace observations. -/
theorem NativeReturnedCalls.refinesReady
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (covered : NativeReturnedCalls.ReadyResponses calls)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) (sameEntry : start.reached = entry)
    (samePins : start.pins.map NativeOpenedPin.raw = known)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      last.reached = reached ∧
      last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins call => call.pinsAfter pins) known ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      start.current.LedgerSuffix events last.current := by
  obtain ⟨last, events, reached, pins, physical, length, records, ledger, _⟩ :=
    executed.refinesReadyFramed covered view inodes runs storage inode buffered effects start sameEntry samePins initial
  exact ⟨last, events, reached, pins, physical, length, records, ledger⟩

/-- Locate the first uncertain return using only public responses. -/
private theorem readyOrFirstUnknown {heap : Type} {opened : NativeOpenedHandle heap}
    (calls : List (NativeReturnedCall opened)) :
    NativeReturnedCalls.ReadyResponses calls ∨
      ∃ prior request cause later, calls = prior ++ .write request (.error (.commitUnknown cause)) :: later ∧
        NativeReturnedCalls.ReadyResponses prior := by
  induction calls with
  | nil => exact .inl (by simp [NativeReturnedCalls.ReadyResponses])
  | cons call rest ih =>
    by_cases first : call.ReadyResponse
    · rcases ih with tail | ⟨prior, request, cause, later, rfl, prefixReady⟩
      · exact .inl (by simpa [NativeReturnedCalls.ReadyResponses] using And.intro first tail)
      · exact .inr ⟨call :: prior, request, cause, later, rfl,
          by simpa [NativeReturnedCalls.ReadyResponses] using And.intro first prefixReady⟩
    · cases call with
      | acquire result => exact (first trivial).elim
      | read pin request result => exact (first trivial).elim
      | write request result =>
        cases result with
        | ok => exact (first trivial).elim
        | error failure =>
          cases failure with
          | rejected => exact (first trivial).elim
          | commitUnknown cause =>
            exact .inr ⟨[], request, cause, rest, rfl, by simp [NativeReturnedCalls.ReadyResponses]⟩

/-- A returned sequence that ends outside the poisoned phase contains
no earlier commit-unknown response on that same handle. -/
theorem NativeReturnedCalls.readyResponsesOfNotPoisoned
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) (sameEntry : start.reached = entry)
    (samePins : start.pins.map NativeOpenedPin.raw = known)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start)
    (notPoisoned : opened.contents reached opened.phase ≠ some .poisoned) :
    NativeReturnedCalls.ReadyResponses calls := by
  obtain covered | ⟨prior, request, cause, later, rfl, prefixReady⟩ := readyOrFirstUnknown calls
  · exact covered
  obtain ⟨middle, ran, remaining⟩ := executed.splitAppend
  obtain ⟨position, _, atMiddle, _, _, _⟩ := ran.refinesReady prefixReady view inodes runs
    storage inode buffered effects start sameEntry samePins initial
  cases remaining with
  | cons unknown suffix =>
    have poisoned := writes.commitUnknownPoisons position (atMiddle.symm ▸ unknown) effects.writePhase
    exact (notPoisoned (suffix.fromPoisoned poisoned).2).elim

/-- The next write shares the prefix's handle, pins and actual heap.
A confirmed or uncertain return proves the prefix ran in one ready
epoch. A rejected return needs separate prefix coverage because the
poisoned-phase guard can reject it. -/
theorem NativeReturnedCalls.refinesReadyBeforeWrite
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {prefixCalls : List (NativeReturnedCall opened)}
    {request : WriteRequest} {response : Except DiskWriteError UInt64}
    (executed : NativeReturnedCalls writes issuer entry known
      (prefixCalls ++ [.write request response]) reached)
    (coveredIfRejected : ∀ cause, response = .error (.rejected cause) → NativeReturnedCalls.ReadyResponses prefixCalls)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) (sameEntry : start.reached = entry)
    (samePins : start.pins.map NativeOpenedPin.raw = known)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start)
    {first : Nat}
    (names : writes.WalWindowEffects storage first
      (start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (window : start.WalWindowAt storage first
      (start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum + request.rows.length)) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer entry known prefixCalls last.reached ∧
      last.pins.map NativeOpenedPin.raw = prefixCalls.foldl (fun pins call => call.pinsAfter pins) known ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = prefixCalls.length ∧ (∀ pair ∈ prefixCalls.zip events, pair.1.Records pair.2) ∧
      start.current.LedgerSuffix events last.current ∧
      last.WalWindowAt storage first (last.current.history.length + request.rows.length) ∧
      (NativeReturnedCall.write request response).Reaches
        writes issuer (last.pins.map NativeOpenedPin.raw) last.reached reached := by
  obtain ⟨middle, ran, pending⟩ := executed.splitAppend
  cases pending with
  | cons returned tail =>
    cases tail
    have covered : NativeReturnedCalls.ReadyResponses prefixCalls := by
      by_cases rejected : ∃ cause, response = .error (.rejected cause)
      · obtain ⟨cause, declared⟩ := rejected
        exact coveredIfRejected cause declared
      · exact ran.readyResponsesOfNotPoisoned view inodes runs storage inode buffered
          effects start sameEntry samePins initial (returned.writeNotPoisoned (fun cause declared => rejected ⟨cause, declared⟩))
    obtain ⟨last, events, atMiddle, pins, physical, length, records, ledger, budget, _, frames⟩ :=
      ran.refinesReadyFramed covered view inodes runs storage inode buffered effects start sameEntry samePins initial
    refine ⟨last, events, atMiddle.symm ▸ ran, pins, physical, length, records, ledger,
      (frames names window).restrictUpper (Nat.add_le_add_right budget _), ?_⟩
    rw [atMiddle, pins]
    exact returned

/-- The final write reached by a ready prefix. Its physical entry and
bounded WAL namespace refer to the same ready heap as the public call. -/
structure NativeReadyWriteCalls.ReachedUncertainWrite (writes : NativeReadyWriteCalls opened)
    (issuer : opened.LatestIssuer) (current : NativeOpenedPosition opened)
    {inodes : heap → WalInodeImage} {runs : heap → RunUnlinkImage}
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    (first : Nat) (request : WriteRequest) (cause : IO.Error) (failed : heap) : Prop where
  observed : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
    writes issuer (current.pins.map NativeOpenedPin.raw) current.reached failed
  nonempty : request.rows ≠ []
  returned :
    let directory := current.current.ready.state.session.directory
    let cache := writes.cacheAtPosition current
    request.runOnRawOpenPhase directory writes.lookup (writes.appender.run cache.active)
      (writes.stager.run cache.pending) (writes.syncer.group directory.path cache.directory cache.active cache.pending)
      writes.rename opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) failed
  physical : NativeReadyStorage current.current.ready.state
    ((current.directory.symm ▸ observe current.reached : RunDirectoryInodeView _ _ _).storageObservation)
  window : current.WalWindowAt
    (fun atHeap => (current.directory.symm ▸ observe atHeap : RunDirectoryInodeView _ _ _).storageObservation) first
    (current.current.history.length + request.rows.length)

/-- Reindexing a run view along directory equality preserves the observed files. -/
theorem _root_.Alvoki.Storage.CheckpointPublication.RunDirectoryInodeView.storageObservation_cast
    {first last : DiskDirectory} {inodes : WalInodeImage} {runs : RunUnlinkImage}
    (same : first = last) (files : RunDirectoryInodeView first inodes runs) :
    (same ▸ files : RunDirectoryInodeView last inodes runs).storageObservation = files.storageObservation := by
  subst last
  rfl

/-- Refine the actual ready calls before an uncertain write and attach
their ledger to the incoming client's history. The final observed call
also supplies the raw write equality used by both retry branches. -/
theorem NativeReturnedCalls.refinesReadyBeforeCommitUnknown
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {failed : heap} {prefixCalls : List (NativeReturnedCall opened)}
    {request : WriteRequest} {cause : IO.Error}
    (start : NativeOpenedPosition opened)
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw)
      (prefixCalls ++ [.write request (.error (.commitUnknown cause))]) failed)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix earlier start.current)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs (fun atHeap => (observe atHeap).storageObservation) inode buffered)
    (initial : writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
      (fun atHeap => (inodes atHeap).visible) start)
    {first : Nat}
    (names : writes.WalWindowEffects (fun atHeap => (observe atHeap).storageObservation) first
      (start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (window : start.WalWindowAt (fun atHeap => (observe atHeap).storageObservation) first
      (start.current.history.length + (prefixCalls.map NativeReturnedCall.requestedRows).sum + request.rows.length)) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) prefixCalls last.reached ∧
      events.length = prefixCalls.length ∧ (∀ pair ∈ prefixCalls.zip events, pair.1.Records pair.2) ∧
      origin.LedgerSuffix (earlier ++ events) last.current ∧
      writes.ReachedUncertainWrite issuer last observe first request cause failed := by
  obtain ⟨last, events, ran, _, physical, length, records, suffix, bounded, observed⟩ :=
    executed.refinesReadyBeforeWrite (fun _ declared => by cases declared) view inodes runs
      (fun atHeap => (observe atHeap).storageObservation) inode buffered effects start rfl rfl initial names window
  have sameStorage :
      (fun atHeap => (last.directory.symm ▸ observe atHeap : RunDirectoryInodeView _ _ _).storageObservation) =
        fun atHeap => (observe atHeap).storageObservation := by
    funext atHeap
    exact RunDirectoryInodeView.storageObservation_cast last.directory.symm (observe atHeap)
  refine ⟨last, events, ran, length, records, prior.append suffix,
    ⟨observed, writes.commitUnknownHasRows last observed, writes.returnedWriteAt last observed, ?_, ?_⟩⟩
  · exact (congrFun sameStorage last.reached).symm ▸ physical.physical
  · exact sameStorage.symm ▸ bounded

end Alvoki.Storage.DiskSession
