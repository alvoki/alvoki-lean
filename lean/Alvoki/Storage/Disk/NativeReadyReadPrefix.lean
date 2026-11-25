import Alvoki.Storage.Disk.CapturedLongKeeperInstallation
import Alvoki.Storage.Disk.ClientSnapshotTransitions
import Alvoki.Storage.Disk.RetainedWriterReopen
import Alvoki.Storage.Disk.PendingClientReplay

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

theorem Valid.acquirePreserves {state : NativeReadyState} (valid : state.Valid)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table)) :
    (state.withTable table).Valid := by
  have step : SegmentedBatchDatabaseTrace state.session.directory state.session.descriptor state.writer
      false [] state.session.descriptor (state.writer.withTable table) := .table .start (.acquireAt acquired)
  exact ⟨rfl, valid.owner, valid.ownerLive, valid.directoryLive, valid.captured, (step.preservesRetained valid.retained).1⟩

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
Each next edge acquires a local pin and records the read at that reached
session. Neither operation changes the files or descriptor inventory. -/
inductive NativeReadyReadPrefix
    (opened : EStateM.Result IO.Error CensusOpenState SegmentedSession)
    (history : List WAL.Write) (log : List DatabaseSubmissions) :
    List RecordedSnapshotRead → NativeReadyState → Prop where
  | installed {reads state} (returned : opened = .ok state.session (state.census, state.files))
      (valid : state.Valid) (sameHistory : state.writer.history = history)
      (replay : PendingClientReplay log reads history) : NativeReadyReadPrefix opened history log reads state
  | acquireRead {reads : List RecordedSnapshotRead} {state : NativeReadyState} {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
      {α : Type} {request : SnapshotReadRequest α} {response : α}
      (prior : NativeReadyReadPrefix opened history log reads state)
      (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table))
      (returned : state.session.runAcquireAt snapshot =
        .ok (some (state.session.sessionRef, pin)) (state.withTable table).session)
      (read : (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
        .ok (some response) (state.withTable table).session) :
      NativeReadyReadPrefix opened history log (reads ++ [request.record snapshot response]) (state.withTable table)

private theorem readReplay (request : SnapshotReadRequest α) (reference : SnapshotTable UInt64)
    (snapshot : UInt64) : (request.record snapshot (request.replay reference snapshot)).agrees reference := by
  cases request <;> rfl

private theorem NativeReadyState.Valid.exactRead {state : NativeReadyState} (valid : state.Valid)
    {reference : SnapshotTable UInt64} (replayed : SnapshotWalReplay .empty state.writer.history reference)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : state.writer.installed.table.acquireAt snapshot = some (pin, table))
    (request : SnapshotReadRequest α) :
    (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
      .ok (some (request.replay reference snapshot)) (state.withTable table).session := by
  obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
  obtain ⟨⟨_, _⟩, pinned, _⟩ := Option.map_eq_some_iff.mp acquired
  have within := Sequential.SnapshotPins.acquire_spec pinned
  obtain ⟨expectedPin, expectedTable, expected, lookup, range⟩ :=
    represented.acquireReads refined valid.retained.resumed.bounds replayed within.1 within.2.1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (expected.symm.trans acquired))
  apply state.readReturns request
  cases request with
  | lookup key => exact lookup key
  | range lo hi => exact range lo hi

/-- The returned files, cache and census remain the ones from the same
restart, and the local token stays with this session throughout. -/
theorem NativeReadyReadPrefix.frames
    (observed : NativeReadyReadPrefix opened history log reads state) :
    ∃ initial : NativeReadyState, opened = .ok initial.session (initial.census, initial.files) ∧
      state.files = initial.files ∧ state.census = initial.census ∧ state.cache = initial.cache ∧
      state.session.sessionRef = initial.session.sessionRef ∧ state.session.phaseRef = initial.session.phaseRef ∧
      state.owner = initial.owner ∧ state.directorySlot = initial.directorySlot := by
  induction observed with
  | installed returned _ _ _ => exact ⟨_, returned, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | acquireRead _ _ _ _ ih => exact ih

/-- The ledger and exact native read results are preserved by induction
over an arbitrary supported read prefix. -/
theorem NativeReadyReadPrefix.refines
    (observed : NativeReadyReadPrefix opened history log reads state) :
    state.Valid ∧ state.writer.history = history ∧ PendingClientReplay log reads history := by
  induction observed with
  | installed _ valid history replay => exact ⟨valid, history, replay⟩
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

/-- The same replay already observed by the prefix still explains every
supported local snapshot in the reached ready session. -/
theorem NativeReadyReadPrefix.guardedReplay
    (observed : NativeReadyReadPrefix opened history log reads state) :
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
    (observed : NativeReadyReadPrefix opened history log reads state) (snapshot : UInt64)
    (floor : state.writer.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ state.writer.installed.table.committed)
    (request : SnapshotReadRequest α) :
    ∃ (reference : SnapshotTable UInt64) (pin : SnapshotPin) (table : PackedTable),
      SnapshotWalReplay .empty history reference ∧
      state.session.runAcquireAt snapshot = .ok (some (state.session.sessionRef, pin)) (state.withTable table).session ∧
      (state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
        .ok (some (request.replay reference snapshot)) (state.withTable table).session ∧
      NativeReadyReadPrefix opened history log (reads ++ [request.record snapshot (request.replay reference snapshot)])
        (state.withTable table) ∧ (state.withTable table).files = state.files ∧
      (state.withTable table).census = state.census ∧ (state.withTable table).cache = state.cache := by
  obtain ⟨valid, history, reference, replayed, _, _, _, _⟩ := observed.refines
  obtain ⟨_, refined, represented⟩ := valid.retained.resumed.canonical
  have current := history.symm ▸ replayed
  obtain ⟨pin, table, acquired, _, _⟩ := represented.acquireReads refined valid.retained.resumed.bounds current floor committed
  have returned := valid.acquireReturns acquired
  have read := valid.exactRead current acquired request
  exact ⟨reference, pin, table, replayed, returned, read, .acquireRead observed acquired returned read, rfl, rfl, rfl⟩

/-- Seed the prefix from a chronological marked reopen with a long
keeper. The primitive reports supply the reached reads and replacement;
the actual returned session is derived before the first read step. -/
theorem CapturedLongKeeperFinish.startsNativeReadPrefix
    {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
    {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
    {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
    {published : CheckpointPublication.Image} {calls : CapturedAlignedCallbacks admission}
    {report : CapturedMarkedReadReports admission layout published}
    {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
    {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
    (finish : CapturedLongKeeperFinish calls report vacant selected)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    (markerRead : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (markerRead.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    {released : FilePath → List LockReferenceDrop} {required : List (Nat × IO.FS.Metadata)}
    (seals : CapturedSealReadChain report released required report.listing.afterClose finish.reader.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ finish.reader.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    (pending : PendingClientReplay log reads history) :
    ∃ state, NativeReadyReadPrefix (finish.runFromCensus metadataRelease runs.released released) history log reads state ∧
      state.cache = admission.cache ∧ state.census = finish.census ∧ state.files = finish.settled ∧
      state.writer.published.durable = published.durable ∧ state.writer.checkpoint = checkpoint := by
  obtain ⟨session, returned, _, ownerLive, directoryLive, installed⟩ := finish.installsFromCensus manifest runs markerRead
    chronology seals offsets retained marker prepared.keeperPrefix prepared.newer following accepted ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ordered
  obtain ⟨sameSession, sameFinal, writer, indexed, path, description, phase, files, owners, _, target,
    history, _, durable, ready⟩ := appendReady.writerRetained walLayout walValid spans active keeper kept
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  let state : NativeReadyState := ⟨session, writer, finish.census, admission.cache, admission.owner, admission.cached⟩
  have exactFiles : state.files = finish.settled := by
    change (⟨writer.files, writer.owners⟩ : LockedFileState FileImage) = finish.settled
    rw [files, owners]
  have correct : state.Valid :=
    ⟨phase, description.symm, ownerLive, directoryLive, ⟨admission.reached, rfl⟩, path.symm ▸ description.symm ▸ ready⟩
  have chosen := ready.resumed.selected
  rw [target, durable] at chosen
  exact ⟨state, .installed (exactFiles.symm ▸ returned) correct history pending, rfl, rfl, exactFiles, durable,
    chosen.uniqueResult selected⟩

end Alvoki.Storage.DiskSession
