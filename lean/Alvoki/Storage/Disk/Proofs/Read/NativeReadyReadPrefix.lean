import Alvoki.Storage.Disk.Proofs.Keeper.CapturedLongKeeperInstallation
import Alvoki.Storage.Disk.Proofs.Read.ClientSnapshotTransitions
import Alvoki.Storage.Disk.ClientRunMaintenance
import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterReopen
import Alvoki.Storage.Disk.Proofs.Read.SnapshotReadHistoryBounds

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)
open Sequential (SnapshotPin SnapshotTable)

/-- The session, file image and live descriptions reached by one native
open. A subsequent snapshot operation only changes the session's table. -/
structure NativeReadyState where
  session : SegmentedSession
  writer : SegmentedWriterState
  census : DescriptorInventory
  cache : CensusDirectoryCache
  owner : DescriptorSlot
  directorySlot : DescriptorSlot

namespace NativeReadyState

def files (state : NativeReadyState) : LockedFileState FileImage :=
  ⟨state.writer.files, state.writer.owners⟩

structure Valid (state : NativeReadyState) : Prop where
  phase : state.session.phase = .ready state.writer.installed
  owner : state.owner.description = state.session.descriptor
  ownerLive : state.owner ∈ state.census.slots
  directoryLive : state.directorySlot ∈ state.census.slots
  captured : ∃ atOpen, state.cache.directory = some (atOpen, state.directorySlot, 0)
  retained : state.writer.RetainedReady state.session.directory state.session.descriptor

def withTable (state : NativeReadyState) (table : PackedTable) : NativeReadyState :=
  { state with
    session := { state.session with phase := .ready { state.writer.installed with table } }
    writer := state.writer.withTable table }

private theorem Valid.tablePreserves {state : NativeReadyState} (valid : state.Valid) {table : PackedTable}
    (step : SegmentedTableStep state.writer.installed.table table) : (state.withTable table).Valid :=
  ⟨rfl, valid.owner, valid.ownerLive, valid.directoryLive, valid.captured, step.preservesRetained valid.retained⟩

theorem Valid.acquirePreserves {state : NativeReadyState} (valid : state.Valid)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table)) :
    (state.withTable table).Valid :=
  valid.tablePreserves (.acquireAt acquired)

theorem Valid.acquireReturns {state : NativeReadyState} (valid : state.Valid)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table)) :
    state.session.runAcquireAt snapshot = .ok (some (state.session.sessionRef, pin)) (state.withTable table).session :=
  SegmentedSession.runAcquireAt_ready valid.phase acquired

private theorem readReturns (state : NativeReadyState) {table : PackedTable} {pin : SnapshotPin}
    (request : SnapshotReadRequest α) {response : α}
    (read : request.read pin.handle table = some response) :
    (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
      .ok (some response) (state.withTable table).session := by
  simp [SegmentedSession.runSnapshotRead, withTable, readSnapshotWith, withLocalHandle, Phase.installed, read,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

end NativeReadyState

/-- The first ready session is the exact result of the selected restart.
Local snapshot operations and in-memory rewrites keep its files and
descriptor inventory. Reads use a handle at the reached table. -/
inductive NativeReadyReadPrefix
    (opened : EStateM.Result IO.Error CensusOpenState SegmentedSession)
    (initial : NativeReadyState) (history : List WAL.Write) (log : List DatabaseSubmissions) :
    List RecordedSnapshotRead → NativeReadyState → Prop where
  | installed {reads} (returned : opened = .ok initial.session (initial.census, initial.files))
      (valid : initial.Valid) (sameHistory : initial.writer.history = history)
      (replay : PendingClientReplay log reads history)
      (bounded : ∀ read ∈ reads, read.BoundedBy history.length) :
      NativeReadyReadPrefix opened initial history log reads initial
  | acquireRead {reads : List RecordedSnapshotRead} {state : NativeReadyState} {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
      {α : Type} {request : SnapshotReadRequest α} {response : α}
      (prior : NativeReadyReadPrefix opened initial history log reads state)
      (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table))
      (returned : state.session.runAcquireAt snapshot =
        .ok (some (state.session.sessionRef, pin)) (state.withTable table).session)
      (read : (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
        .ok (some response) (state.withTable table).session) :
      NativeReadyReadPrefix opened initial history log (reads ++ [request.record snapshot response]) (state.withTable table)
  | snapshotUpdate {reads : List RecordedSnapshotRead} {state : NativeReadyState} {table : PackedTable}
      {α : Type} (update : SnapshotUpdate α) {result : α}
      (prior : NativeReadyReadPrefix opened initial history log reads state)
      (returned : update.run state.session = .ok result (state.withTable table).session)
      (step : SegmentedTableStep state.writer.installed.table table) :
      NativeReadyReadPrefix opened initial history log reads (state.withTable table)
  | rewriteRun {reads : List RecordedSnapshotRead} {state : NativeReadyState} {table : PackedTable}
      (request : RunMaintenance)
      (prior : NativeReadyReadPrefix opened initial history log reads state)
      (returned : request.run state.session = .ok true (state.withTable table).session)
      (rewritten : request.update state.writer.installed.table = some table) :
      NativeReadyReadPrefix opened initial history log reads (state.withTable table)
  | readHandle {reads : List RecordedSnapshotRead} {state : NativeReadyState}
      {α : Type} {request : SnapshotReadRequest α} {handle : Sequential.SnapshotHandle}
      {reader : ObservedSnapshotReader state.session.directory state.session.descriptor state.writer}
      {response : Option α} {recorded : RecordedSnapshotRead}
      (prior : NativeReadyReadPrefix opened initial history log reads state)
      (atSession : reader.session = state.session)
      (returned : request.HandleReturn reader handle response recorded) :
      NativeReadyReadPrefix opened initial history log (reads ++ [recorded]) state

private theorem readReplay (request : SnapshotReadRequest α) (reference : SnapshotTable UInt64)
    (snapshot : UInt64) : (request.record snapshot (request.replay reference snapshot)).agrees reference := by
  cases request <;> rfl

private theorem acquiredAtBounds {before after : PackedTable} {snapshot : UInt64} {pin : SnapshotPin}
    (acquired : before.acquireAt snapshot = some (pin, after)) :
    before.pins.floor ≤ snapshot ∧ snapshot ≤ before.committed := by
  obtain ⟨⟨_, _⟩, pinned, _⟩ := Option.map_eq_some_iff.mp acquired
  have bounds := Sequential.SnapshotPins.acquire_spec pinned
  exact ⟨bounds.1, bounds.2.1⟩

private theorem NativeReadyState.Valid.exactRead {state : NativeReadyState} (valid : state.Valid)
    {reference : SnapshotTable UInt64} (replayed : SnapshotWalReplay .empty state.writer.history reference)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table))
    (request : SnapshotReadRequest α) :
    (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
      .ok (some (request.replay reference snapshot)) (state.withTable table).session := by
  obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
  have within := acquiredAtBounds acquired
  obtain ⟨expectedPin, expectedTable, expected, lookup, range⟩ :=
    represented.acquireReads refined valid.retained.resumed.bounds replayed within.1 within.2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (expected.symm.trans acquired))
  apply state.readReturns request
  cases request with
  | lookup key => exact lookup key
  | range lo hi => exact range lo hi

/-- The returned files, cache and census remain the ones from the same
restart, and the local token stays with this session throughout. -/
theorem NativeReadyReadPrefix.frames
    (observed : NativeReadyReadPrefix opened initial history log reads state) :
    opened = .ok initial.session (initial.census, initial.files) ∧
    state.files = initial.files ∧ state.census = initial.census ∧ state.cache = initial.cache ∧
    state.session.sessionRef = initial.session.sessionRef ∧ state.session.phaseRef = initial.session.phaseRef ∧
    state.owner = initial.owner ∧ state.directorySlot = initial.directorySlot := by
  induction observed with
  | installed returned _ _ _ _ => exact ⟨returned, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | acquireRead _ _ _ _ ih => exact ih
  | snapshotUpdate _ _ _ _ ih => exact ih
  | rewriteRun _ _ _ _ ih => exact ih
  | readHandle _ _ _ ih => exact ih

/-- The ledger and exact native read results are preserved by induction
over an arbitrary supported read prefix. -/
theorem NativeReadyReadPrefix.refines
    (observed : NativeReadyReadPrefix opened initial history log reads state) :
    state.Valid ∧ state.writer.history = history ∧ PendingClientReplay log reads history := by
  induction observed with
  | installed _ valid history replay _ => exact ⟨valid, history, replay⟩
  | @acquireRead reads state snapshot pin table α request response _ acquired _ read ih =>
    obtain ⟨valid, history, reference, replayed, retained, acknowledged, submitted, responses⟩ := ih
    have expected := valid.exactRead (history.symm ▸ replayed) acquired request
    have equal := Option.some.inj (EStateM.Result.ok.inj (read.symm.trans expected)).1
    refine ⟨valid.acquirePreserves acquired, history, reference, replayed, retained, acknowledged, submitted, ?_⟩
    intro response member
    rcases List.mem_append.mp member with old | new
    · exact responses _ old
    · obtain rfl := List.mem_singleton.mp new
      exact equal.symm ▸ readReplay request reference snapshot
  | snapshotUpdate _ _ _ step ih =>
    exact ⟨ih.1.tablePreserves step, ih.2⟩
  | rewriteRun request _ _ rewritten ih =>
    exact ⟨ih.1.tablePreserves (request.update_spec rewritten).1, ih.2⟩
  | readHandle _ _ returned ih =>
    obtain ⟨valid, history, reference, replayed, retained, acknowledged, submitted, responses⟩ := ih
    refine ⟨valid, history, reference, replayed, retained, acknowledged, submitted, ?_⟩
    intro response member
    rcases List.mem_append.mp member with old | newest
    · exact responses _ old
    · obtain rfl := List.mem_singleton.mp newest
      exact returned.observed.agreesForReplay valid.retained
        (by simpa only [List.append_nil, history] using replayed :
          SnapshotWalReplay .empty (_ ++ []) reference)

/-- Each successful response records a sequence within the history
that supported its acquired or previously registered pin. -/
theorem NativeReadyReadPrefix.readsBounded
    (observed : NativeReadyReadPrefix opened initial history log reads state) :
    ∀ read ∈ reads, read.BoundedBy history.length := by
  induction observed with
  | installed _ _ _ _ bounded => exact bounded
  | @acquireRead reads state snapshot pin table α request response prior acquired _ _ ih =>
    intro read member
    rcases List.mem_append.mp member with earlier | latest
    · exact ih read earlier
    · obtain rfl := List.mem_singleton.mp latest
      obtain ⟨valid, sameHistory, _⟩ := prior.refines
      obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
      have committedCount : state.writer.installed.table.committed.toNat = history.length :=
        (congrArg UInt64.toNat refined.committed).trans
          (represented.committed_count.trans (congrArg List.length sameHistory))
      have committed := committedCount ▸ UInt64.le_iff_toNat_le.mp (acquiredAtBounds acquired).2
      cases request <;> exact committed
  | snapshotUpdate _ _ _ _ ih => exact ih
  | rewriteRun _ _ _ _ ih => exact ih
  | readHandle prior _ returned ih =>
    intro read member
    rcases List.mem_append.mp member with earlier | latest
    · exact ih read earlier
    · obtain rfl := List.mem_singleton.mp latest
      obtain ⟨valid, sameHistory, _⟩ := prior.refines
      exact sameHistory ▸ returned.observed.boundedBy valid.retained

/-- The same replay already observed by the prefix still explains every
supported local snapshot in the reached ready session. -/
theorem NativeReadyReadPrefix.guardedReplay
    (observed : NativeReadyReadPrefix opened initial history log reads state) :
    InstalledClientReplay log reads history state.writer.installed state.session := by
  obtain ⟨valid, history, reference, replayed, retained, acknowledged, submitted, prior⟩ := observed.refines
  obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
  have guarded := state.session.guardedAcquireReads valid.phase fun _ floor committed =>
    represented.acquireReads refined valid.retained.resumed.bounds (history.symm ▸ replayed) floor committed
  exact ⟨reference, replayed, retained, acknowledged, submitted, prior, guarded⟩

/-- The next read is issued at the previously returned session. The
acquisition and the local point or range read supply the next prefix
at the exact reached state, still under the same owner and directory. -/
theorem NativeReadyReadPrefix.readAt
    (observed : NativeReadyReadPrefix opened initial history log reads state) (snapshot : UInt64)
    (floor : state.writer.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ state.writer.installed.table.committed)
    (request : SnapshotReadRequest α) :
    ∃ (reference : SnapshotTable UInt64) (pin : SnapshotPin) (table : PackedTable),
      SnapshotWalReplay .empty history reference ∧
      state.session.runAcquireAt snapshot = .ok (some (state.session.sessionRef, pin)) (state.withTable table).session ∧
      (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
        .ok (some (request.replay reference snapshot)) (state.withTable table).session ∧
      NativeReadyReadPrefix opened initial history log (reads ++ [request.record snapshot (request.replay reference snapshot)])
        (state.withTable table) ∧ (state.withTable table).files = state.files ∧
      (state.withTable table).census = state.census ∧ (state.withTable table).cache = state.cache := by
  obtain ⟨valid, history, reference, replayed, _, _, _, _⟩ := observed.refines
  obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
  have current := history.symm ▸ replayed
  obtain ⟨pin, table, acquired, _, _⟩ := represented.acquireReads refined valid.retained.resumed.bounds current floor committed
  have returned := valid.acquireReturns acquired
  have read := valid.exactRead current acquired request
  exact ⟨reference, pin, table, replayed, returned, read, .acquireRead observed acquired returned read, rfl, rfl, rfl⟩

end Alvoki.Storage.DiskSession
