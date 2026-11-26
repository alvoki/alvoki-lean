import Alvoki.Storage.Disk.NativePublishedWriteSnapshot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
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

/-- Successful writes and local snapshot calls continue the ready proof.
For a rejected write whose nonempty preparation fits and succeeds, the
literal guard must itself reject at the call's reached heap. A setter
failure with the same error tag cannot meet that condition. Admission
remains the independent raw call relation. -/
def NativeReturnedCall.ReadyContinuation (call : NativeReturnedCall opened)
    (writes : NativeReadyWriteCalls opened) (entry reached : heap) : Prop :=
  match call with
  | .write _ (.ok _) | .acquire (.ok _) | .read _ _ (.ok _) => True
  | .write request (.error (.rejected cause)) =>
    ∀ {installed : Installed}, opened.contents entry opened.phase = some (.ready installed) →
      request.rows ≠ [] →
      installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size →
      ∀ {batch table}, prepareBatch installed.table request.rows = some (batch, table) →
        checkActiveSegmentWith opened.directory installed writes.lookup entry = .error cause reached
  | _ => False

/-- Authorize only occurrences following a literal prefix of this same
sequence. Two instances of the same request and diagnostic can reach
different guards or setters. -/
def NativeReturnedCalls.ReadyFrom (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (entry : heap) (known : List DiskSnapshotPin) (calls : List (NativeReturnedCall opened)) : Prop :=
  ∀ {prior : List (NativeReturnedCall opened)} {call : NativeReturnedCall opened}
    {later : List (NativeReturnedCall opened)} {before after : heap},
    calls = prior ++ call :: later →
    NativeReturnedCalls writes issuer entry known prior before →
    call.Reaches writes issuer (prior.foldl (fun pins call => call.pinsAfter pins) known) before after →
    call.ReadyContinuation writes before after

/-- These laws concern the reached native primitives. The raw call
chronology supplies the actual request, response and endpoint. -/
structure NativeReadyWriteCalls.ReturnEffects (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray) : Prop where
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
  read : ∀ (start : NativeOpenedPosition opened) {α : Type} (pin : NativeOpenedPin opened)
      (request : SnapshotReadRequest α) {response reached},
    opened.readPinRaw pin request start.reached = .ok response reached →
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
    writes.keepsStorage view storage _ initial updated frame, .preflight seen, ledger, ?_⟩
  intro first through names window
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
    (observed : call.Reaches writes issuer known start.reached reached) (covered : call.ReadyContinuation writes start.reached reached)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (next : NativeOpenedPosition opened) (event : NativeExecutionEvent),
      next.reached = reached ∧
      next.pins.map NativeOpenedPin.raw = call.pinsAfter (start.pins.map NativeOpenedPin.raw) ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) next ∧
      call.Records event ∧ start.current.LedgerSuffix [event] next.current ∧
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
              have stored : opened.contents start.reached opened.phase = some (.ready state.writer.installed) :=
                start.stored.trans (congrArg some start.current.ready.readPrefix.refines.1.phase)
              have actual := covered stored empty fits prepared
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
        obtain ⟨_, _, batch, table, next, _, prepared, committed, atHeap, pins, _, ledger, ready, keepsNames⟩ :=
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
          .write rows lastSequence, ledger, ?_⟩
        intro first through names window
        obtain ⟨phaseNames, restore⟩ := names.write start request nonempty observed
        exact keepsNames window.1 window.2 phaseNames restore
  | acquire result =>
    cases result with
    | error => exact False.elim covered
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
        sameHeap.symm, ?_, ready, .acquire pin, acquired.common.ledgerSuffix, ?_⟩
      · simp only [pins, List.map_append, List.map_cons, List.map_nil, pinsAfter]
      · intro first through names window
        exact NativeOpenedPosition.keepsWalWindow updated (names.acquire start setter) window
  | read pin request result =>
    cases result with
    | error => exact False.elim covered
    | ok response =>
      have actual : opened.readPinRaw pin request start.reached = .ok response reached := observed.2
      have compare := effects.read start pin request actual
      obtain ⟨_, value, recorded, readPosition, read, returned, _⟩ :=
        start.current.ready.readsOpenPin opened.table start.uses pin.issued
          (fun phase => opened.phaseEffects.reads start.reached opened.phase phase)
          start.stored opened.ptrEq compare request
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
      refine ⟨next, event, heapEq, rfl, ready, .read pin, continued.ledgerSuffix, ?_⟩
      intro first through _ window
      simpa only [NativeOpenedPosition.WalWindowAt, next, read.state] using window

/-- Refine any finite supported ready sequence on the fixed public
dispatcher. The next transition uses the preceding returned heap,
actual pins, and physical write entry derived by that transition. -/
theorem NativeReturnedCalls.refinesReadyFramed
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (covered : NativeReturnedCalls.ReadyFrom writes issuer entry known calls)
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
      (∀ {first through}, writes.WalWindowEffects storage first through →
        start.WalWindowAt storage first through → last.WalWindowAt storage first through) := by
  induction executed generalizing start with
  | empty => exact ⟨start, [], sameEntry, samePins, initial, rfl, by simp, .empty _, by simp, fun _ window => window⟩
  | @cons middle rest last before known call observed _ ih =>
    have atStart : call.Reaches writes issuer known start.reached middle := sameEntry ▸ observed
    have first : call.ReadyContinuation writes start.reached middle :=
      sameEntry ▸ covered (prior := []) (later := rest) rfl .empty observed
    obtain ⟨next, event, nextHeap, pins, ready, recorded, firstLedger, firstFrame⟩ :=
      call.refinesReady writes issuer view inodes runs storage inode buffered effects start atStart first initial
    have tail : NativeReturnedCalls.ReadyFrom writes issuer middle (call.pinsAfter known) rest := by
      intro prior subsequent later before after order ran returned
      exact covered (prior := call :: prior) (by rw [order]; rfl) (.cons observed ran) returned
    obtain ⟨finish, events, done, finalPins, physical, length, records, ledger, lengthBound, finalFrame⟩ :=
      ih tail next nextHeap
        (pins.trans (congrArg call.pinsAfter samePins)) ready
    refine ⟨finish, event :: events, done, finalPins, physical, by simp [length], ?_, firstLedger.append ledger, ?_,
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

/-- The ready proof alone does not need namespace observations. -/
theorem NativeReturnedCalls.refinesReady
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (covered : NativeReturnedCalls.ReadyFrom writes issuer entry known calls)
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

end Alvoki.Storage.DiskSession
