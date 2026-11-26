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

/-- The phase-cell update that registers a snapshot keeps these physical
observations. The installed table and its pin registry may change. -/
structure NativeReadyWriteCalls.SnapshotFrame (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (storage : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (start : NativeOpenedPosition opened) (reached : heap) : Prop where
  census : view.descriptors reached = view.descriptors start.reached
  cache : view.cacheAt reached writes.cache.directory writes.cache.active writes.cache.pending =
    view.cacheAt start.reached writes.cache.directory writes.cache.active writes.cache.pending
  files : (storage start.reached).Frames start.current.ready.state.crashPath (storage reached)
  keeper : ∀ inode, (storage start.reached).files.names
    (start.current.ready.state.session.directory.file (.walSegment start.current.ready.state.writer.wal.active.first)) =
      some inode → visible reached inode = visible start.reached inode

private theorem NativeReadyWriteCalls.keepsStorageOnSnapshot (writes : NativeReadyWriteCalls opened)
    (view : OpenCloseHeapView heap image) (storage : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) {start next : NativeOpenedPosition opened} {table : PackedTable}
    (initial : writes.StorageAt view storage visible start)
    (updated : next.current.ready.state = start.current.ready.state.withTable table)
    (frame : writes.SnapshotFrame view storage visible start next.reached) :
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

/-- The ready continuation currently covers acknowledged nonempty
writes, successful latest acquisitions and local reads. Admission still
retains empty writes and ordinary errors for later refinements. -/
def NativeReturnedCall.ReadyContinuation (call : NativeReturnedCall opened) : Prop :=
  match call with
  | .write request (.ok _) => request.rows ≠ []
  | .acquire (.ok _) | .read _ _ (.ok _) => True
  | _ => False

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
    writes.SnapshotFrame view storage (fun atHeap => (inodes atHeap).visible) start reached
  read : ∀ (start : NativeOpenedPosition opened) {α : Type} (pin : NativeOpenedPin opened)
      (request : SnapshotReadRequest α) {response reached},
    opened.readPinRaw pin request start.reached = .ok response reached →
    opened.ptrEq opened.token opened.token start.reached = .ok true start.reached

/-- A derived abstract event records the same public operands and
response. Actual admission is the independent `Reaches` relation. -/
inductive NativeReturnedCall.Records : NativeReturnedCall opened → NativeExecutionEvent → Prop where
  | write (rows : batch.map (fun entry : WAL.Write => (entry.key, entry.value)) = request.rows)
      (sequence : batch.getLast?.map WAL.Write.sequence = some number) :
      Records (.write request (.ok number)) (.acknowledged request batch)
  | acquire (pin : NativeOpenedPin opened) :
      Records (.acquire (.ok pin.raw)) (.snapshotControl .acquire (.ok (session, pin.localPin)))
  | read (pin : NativeOpenedPin opened) :
      Records (.read pin request (.ok response))
        (.snapshotHandleRead session pin.localPin.handle request response recorded)

private theorem NativeReturnedCall.refinesReady
    (call : NativeReturnedCall opened) (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) {known : List DiskSnapshotPin} {reached : heap}
    (observed : call.Reaches writes issuer known start.reached reached) (covered : call.ReadyContinuation)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start) :
    ∃ (next : NativeOpenedPosition opened) (event : NativeExecutionEvent),
      next.reached = reached ∧
      next.pins.map NativeOpenedPin.raw = call.pinsAfter (start.pins.map NativeOpenedPin.raw) ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) next ∧
      call.Records event ∧ start.current.LedgerSuffix [event] next.current := by
  cases call with
  | write request result =>
    cases result with
    | error => exact False.elim covered
    | ok sequence =>
      obtain ⟨files, sameStorage, callbacks⟩ := effects.write start request covered observed
      let cache := writes.cacheAtPosition start
      let dir := start.current.ready.state.session.directory
      have raw : request.runOnRawOpenPhase dir writes.lookup (writes.appender.run cache.active)
          (writes.stager.run cache.pending) (writes.syncer.group dir.path cache.directory cache.active cache.pending)
          writes.rename opened.phase opened.get opened.set start.reached = .ok sequence reached := by
        change request.runOnRawOpenPhase start.current.ready.state.session.directory writes.lookup
          (writes.appender.run writes.cache.active) (writes.stager.run writes.cache.pending)
          (writes.syncer.group start.current.ready.state.session.directory.path writes.cache.directory writes.cache.active
            writes.cache.pending) writes.rename opened.phase opened.get opened.set start.reached = .ok sequence reached
        rw [start.directory]
        exact observed
      have seen : start.ObservesPublishedWrite writes.appender writes.stager writes.syncer view cache inodes runs
          storage inode buffered request writes.lookup writes.rename sequence reached :=
        ⟨files, sameStorage, raw, callbacks⟩
      obtain ⟨_, _, batch, table, next, _, prepared, committed, atHeap, pins, _, ledger, ready, _⟩ :=
        start.acknowledgesObservedWrite writes.appender writes.stager writes.syncer view cache inodes runs
          storage inode buffered request writes.lookup writes.rename covered initial seen
      obtain ⟨length, replayed, rows, numbered⟩ := prepareBatch_spec prepared
      have lastSequence : batch.getLast?.map WAL.Write.sequence = some sequence := by
        rcases List.eq_nil_or_concat batch with empty | ⟨earlier, last, appended⟩
        · exfalso
          apply covered
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
      exact ⟨next, .acknowledged request batch, atHeap, congrArg (List.map NativeOpenedPin.raw) pins, ready,
        .write rows lastSequence, ledger⟩
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
      have ready := writes.keepsStorageOnSnapshot view storage (fun atHeap => (inodes atHeap).visible) initial updated framed
      refine ⟨next, .snapshotControl .acquire (.ok (start.current.ready.state.session.sessionRef, pin.localPin)),
        sameHeap.symm, ?_, ready, .acquire pin, acquired.common.ledgerSuffix⟩
      simp only [pins, List.map_append, List.map_cons, List.map_nil, pinsAfter]
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
      exact ⟨next, event, heapEq, rfl, ready, .read pin, continued.ledgerSuffix⟩

/-- Refine any finite supported ready sequence on the fixed public
dispatcher. The next transition uses the preceding returned heap,
actual pins, and physical write entry derived by that transition. -/
theorem NativeReturnedCalls.refinesReady
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls reached)
    (covered : ∀ call ∈ calls, call.ReadyContinuation)
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
  induction executed generalizing start with
  | empty => exact ⟨start, [], sameEntry, samePins, initial, rfl, by simp, .empty _⟩
  | @cons middle rest last before known call observed _ ih =>
    have atStart : call.Reaches writes issuer known start.reached middle := sameEntry ▸ observed
    obtain ⟨next, event, nextHeap, pins, ready, recorded, firstLedger⟩ :=
      call.refinesReady writes issuer view inodes runs storage inode buffered effects start atStart
        (covered call (.head rest)) initial
    obtain ⟨finish, events, done, finalPins, physical, length, records, ledger⟩ :=
      ih (fun each member => covered each (.tail call member)) next nextHeap
        (pins.trans (congrArg call.pinsAfter samePins)) ready
    refine ⟨finish, event :: events, done, finalPins, physical, by simp [length], ?_, firstLedger.append ledger⟩
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact recorded
    · exact records pair member

end Alvoki.Storage.DiskSession
