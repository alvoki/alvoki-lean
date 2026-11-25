import Alvoki.Storage.Disk.NativeOpenAcquire
import Alvoki.Storage.Disk.NativeExecutionPendingWrite
import Alvoki.Storage.Disk.NativeWritePreflight
import Alvoki.Storage.Disk.NativeWriteClassification

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

abbrev OpenWriteFiles := CensusDirectoryCache × WriteFiles

variable {heap : Type}

private def heapEffect {α : Type} (classify : IO.Error → DiskWriteError) (action : EStateM IO.Error heap α) :
    EStateM DiskWriteError (heap × OpenWriteFiles) α :=
  fun (heap, files) => match action heap with
    | .ok result after => .ok result (after, files)
    | .error cause after => .error (classify cause) (after, files)

private def fileEffect {α : Type} (classify : IO.Error → DiskWriteError) (action : EStateM IO.Error OpenWriteFiles α) :
    EStateM DiskWriteError (heap × OpenWriteFiles) α :=
  fun (heap, files) => match action files with
    | .ok result after => .ok result (heap, after)
    | .error cause after => .error (classify cause) (heap, after)

private def requireWritePreparation {s α : Type} : Option α → EStateM DiskWriteError s α
  | some result => pure result
  | none => throw (.rejected (IO.userError "write sequence space exhausted"))

/-- On either production dispatcher, the reached ready-cell read and
successful nonempty preflight issue the same encoded publication tail.
The single-write route keeps its own order of preflight checks. -/
private theorem preparedWrite_reachesPublication {s : Type}
    (request : WriteRequest) {rows : List (UInt64 × Option UInt64)}
    (submitted : request.rows = rows) (nonempty : rows ≠ [])
    {installed : Installed} {events : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch installed.table rows = some (events, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    (load : EStateM DiskWriteError s Installed) (guard : Installed → EStateM DiskWriteError s Unit)
    (setPhase : Phase Installed → EStateM DiskWriteError s Unit)
    (commit : Installed → ByteArray → Nat → EStateM DiskWriteError s Unit)
    {entry : s} (loaded : load entry = .ok installed entry) (checked : guard installed entry = .ok () entry) :
    let count := installed.walBytes + WAL.frameSize * rows.length
    let publish := publishPreparedWrite { installed with table, walBytes := count } table.committed
      setPhase (commit installed (WAL.encodeBatch events) count)
    (match request with
      | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
          (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
            event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
      | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
          (fun state batch count => commit state (WAL.encodeBatch batch) count)) entry =
      publish entry := by
  cases request with
  | single key value =>
    change [(key, value)] = rows at submitted
    subst rows
    rw [prepareBatch_singleton] at prepared
    cases written : installed.table.write key value with
    | none => simp [prepareWrite, written] at prepared
    | some next =>
      simp only [prepareWrite, written, Option.map_some, Option.some.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      have count : installed.walBytes + WAL.frameSize < UInt64.size := by simpa using fits
      simp only [withPreparedSingleWrite, Bind.bind, EStateM.bind, loaded, prepareWrite, written, Option.map_some,
        requireWritePreparation, Pure.pure, EStateM.pure, count, ↓reduceIte,
        checked, List.length_singleton, Nat.mul_one, WAL.encodeBatch_singleton]
  | batch group =>
    change group = rows at submitted
    subst rows
    have present : group.isEmpty = false := by cases group <;> simp_all
    simp only [writeBatchSchedule, Bind.bind, EStateM.bind, loaded, present, Bool.false_eq_true, ↓reduceIte,
      fits, prepared, requireWritePreparation, Pure.pure, EStateM.pure, checked]

private theorem BatchActiveGuard.checkedForWrite {directory installed} (seen : BatchActiveGuard directory installed) :
    (checkActiveSegmentWith directory installed seen.lookup : Except IO.Error Unit) = .ok () := by
  have kind : (IO.FS.FileType.file == .file) = true := rfl
  simp [checkActiveSegmentWith, checkPrivateRegularWith, seen.reached, seen.regular, seen.privateFile,
    seen.extent, kind, Except.bind, Bind.bind, Except.pure, Pure.pure]

/-- Exact production write interpreted with the phase cell and the
reported cache and file callbacks at entry. -/
def NativeReadyWriteReport.ReturnsOnOpenPhase {before : NativeReadyState}
    {prepared : NativeReadyWritePreparation before} (seen : NativeReadyWriteReport prepared)
    (request : WriteRequest) (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (entry reached : heap) : Prop :=
  let directory := before.session.directory
  let load : EStateM DiskWriteError (heap × OpenWriteFiles) Installed := do
    let state ← heapEffect .rejected (get phase)
    liftExcept ((state.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
  let guard := fun state => liftExcept ((checkActiveSegmentWith directory state seen.calls.lookup :
    Except IO.Error Unit).mapError DiskWriteError.rejected)
  let setPhase := fun state => heapEffect .rejected (set phase state)
  let commit := fun (state : Installed) bytes count =>
    fileEffect .commitUnknown (commitBytesAt directory state.activeFirst bytes count
      seen.calls.append seen.calls.stage seen.calls.sync seen.calls.rename)
  (match request with
    | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
        (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
          event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
    | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
        (fun state batch count => commit state (WAL.encodeBatch batch) count))
    (entry, before.cache, prepared.initial) = .ok prepared.table.committed (reached, seen.appendCache, prepared.settled)

/-- The reported cell and file actions follow the production dispatcher
from this exact installed state. Keep the heap and file result together
through each phase assignment and the reached WAL call. -/
theorem NativeReadPosition.acknowledgesViaOpenReferences {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeReadyWriteReport prepared)
    (request : WriteRequest) (rows : request.rows = prepared.rows) :
    db.UsesOpenWriteSchedules current.state.session.directory files phase ∧
    ∃ (poisoned reached : heap) (target : Target)
      (next : NativeReadPosition (history ++ prepared.batch) (log ++ [.acknowledgedBatch prepared.batch])),
      get phase entry = .ok current.state.session.phase entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some .poisoned ∧
      set phase (.ready seen.publication.nextInstalled) poisoned = .ok () reached ∧
      contents reached phase = some next.state.session.phase ∧
      seen.ReturnsOnOpenPhase request phase get set entry reached ∧
      let normalized := seen.next target
      seen.calls.run request current.state.session.directory current.state.writer =
        .ok prepared.table.committed (normalized.session.phase, ⟨(normalized.cache, prepared.settled), normalized.files.owners⟩) ∧
      next.state = normalized ∧ next.initial = normalized ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.reads = current.reads ∧
      db.UsesOpenReferences next.state.session.directory lock files phase token ∧
      InstalledClientReplay (log ++ [.acknowledgedBatch prepared.batch]) current.reads
        (history ++ prepared.batch) next.state.writer.installed next.state.session := by
  let before := current.state
  obtain ⟨target, next, normalized, nextState, initial, reads, opened, _, _, replay⟩ :=
    current.acknowledgesWrite seen request rows
  have ready := current.readPrefix.refines.1.phase
  have got := effects.reads entry phase before.session.phase stored
  obtain ⟨poisoned, exclude, poisonedPhase⟩ := effects.writes entry phase before.session.phase .poisoned stored
  obtain ⟨reached, publish, readyPhase⟩ := effects.writes poisoned phase .poisoned
    (.ready seen.publication.nextInstalled) poisonedPhase
  refine ⟨uses.writeSchedules, poisoned, reached, target, next, got, exclude, poisonedPhase, publish, ?_, ?_,
    normalized, nextState, initial, nextState.symm ▸ opened, reads, ?_, replay⟩
  · rw [nextState]
    exact readyPhase
  · unfold NativeReadyWriteReport.ReturnsOnOpenPhase
    intro directory load guard setPhase commit
    have loaded : load (entry, before.cache, prepared.initial) = .ok before.writer.installed (entry, before.cache, prepared.initial) := by
      simp [load, heapEffect, before, got, ready, Phase.installed, Bind.bind, EStateM.bind, liftExcept, Pure.pure,
        EStateM.pure, Except.pure, Except.mapError]
    have guarded : guard before.writer.installed (entry, before.cache, prepared.initial) =
        .ok () (entry, before.cache, prepared.initial) := by
      have checked : (checkActiveSegmentWith directory before.writer.installed seen.calls.lookup : Except IO.Error Unit) =
          .ok () := seen.activeGuard.checkedForWrite
      simp only [guard, checked, Except.mapError, liftExcept, Pure.pure, EStateM.pure]
    have entered := preparedWrite_reachesPublication request rows prepared.nonempty prepared.prepared prepared.fits
      load guard setPhase commit loaded guarded
    have committed : commit before.writer.installed (WAL.encodeBatch prepared.batch) prepared.count
        (poisoned, before.cache, prepared.initial) = .ok () (poisoned, seen.appendCache, prepared.settled) := by
      simp only [commit, fileEffect, directory, before, seen.publishes]
    rw [entered]
    change publishPreparedWrite seen.publication.nextInstalled prepared.table.committed setPhase
      (commit before.writer.installed (WAL.encodeBatch prepared.batch) prepared.count)
      (entry, before.cache, prepared.initial) = _
    simp only [publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind, setPhase, heapEffect, exclude,
      committed, publish, Pure.pure, EStateM.pure]
  · rw [nextState]
    exact uses

/-- A reported publication error returns on the same opened phase cell
while it is poisoned. The exact error and reached cache and file cut are
those of the existing pending write, with no ready-cell assignment. -/
theorem NativePendingWrite.returnsViaOpenReferences {history log}
    {current : NativeReadPosition history log} (pending : NativePendingWrite current) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase) :
    let before := current.state
    let directory := before.session.directory
    let seen := pending.write
    let failure := seen.failure
    let calls := WriteRequest.Calls.ofFailure seen.observed
    let initial := WriteFiles.initial before.writer.history (before.writer.files.directory.staged .walBoundary)
    let load : EStateM DiskWriteError (heap × OpenWriteFiles) Installed := do
      let state ← heapEffect .rejected (get phase)
      liftExcept ((state.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
    let guard := fun state => liftExcept ((checkActiveSegmentWith directory state calls.lookup :
      Except IO.Error Unit).mapError DiskWriteError.rejected)
    let setPhase := fun state => heapEffect .rejected (set phase state)
    let commit := fun (state : Installed) bytes count =>
      fileEffect .commitUnknown (commitBytesAt directory state.activeFirst bytes count
        calls.append calls.stage calls.sync calls.rename)
    db.UsesOpenWriteSchedules directory files phase ∧
    ∃ poisoned : heap,
      get phase entry = .ok before.session.phase entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some pending.session.phase ∧
      (match seen.request with
        | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
            (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
              event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
        | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
            (fun state batch count => commit state (WAL.encodeBatch batch) count))
        (entry, before.cache, initial) = .error (.commitUnknown failure.cause) (poisoned, pending.cache, failure.failed) ∧
      db.UsesOpenReferences pending.session.directory lock files phase token := by
  intro before directory seen failure calls initial load guard setPhase commit
  have valid := current.readPrefix.refines.1
  have got := effects.reads entry phase before.session.phase stored
  have loaded : load (entry, before.cache, initial) = .ok before.writer.installed (entry, before.cache, initial) := by
    simp [load, heapEffect, before, got, valid.phase, Phase.installed, Bind.bind, EStateM.bind, liftExcept,
      Pure.pure, EStateM.pure, Except.pure, Except.mapError]
  have guarded : guard before.writer.installed (entry, before.cache, initial) =
      .ok () (entry, before.cache, initial) := by
    have checked : (checkActiveSegmentWith directory before.writer.installed calls.lookup : Except IO.Error Unit) =
        .ok () := seen.observed.guard.checkedForWrite
    simp only [guard, checked, Except.mapError, liftExcept, Pure.pure, EStateM.pure]
  obtain ⟨poisoned, exclude, poisonedPhase⟩ := effects.writes entry phase before.session.phase .poisoned stored
  have entered := preparedWrite_reachesPublication seen.request seen.rows failure.nonempty failure.prepared
    failure.fits load guard setPhase commit loaded guarded
  obtain ⟨cacheAfter, failed⟩ := seen.observed.cachedCommitError
  let atWal := WriteFiles.initial before.writer.history (before.writer.wal.directory.staged .walBoundary)
  have projected := runBatchWrite_commitUnknown (before := ⟨(seen.observed.cache, atWal), before.writer.owners⟩)
    seen.observed.guard failure.nonempty failure.prepared failure.fits failed
  have returned : calls.run seen.request directory before.writer =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(pending.cache, failure.failed), before.writer.owners⟩) := by
    have reported := pending.returned
    change seen.returnedAt pending.cache at reported
    unfold NativeReadyWriteFailure.returnedAt at reported
    rw [← seen.cache] at reported
    exact reported
  unfold WriteRequest.Calls.run at returned
  rw [seen.request.runReported_eq_batch valid.retained, seen.rows, valid.retained.directoryFiles] at returned
  change runBatchWrite directory failure.rows seen.observed.guard.lookup seen.observed.append
    seen.observed.stage seen.observed.sync seen.observed.rename
    (.ready before.writer.installed, ⟨(seen.observed.cache, atWal), before.writer.owners⟩) = _ at returned
  rw [projected] at returned
  have sameCache : cacheAfter = pending.cache := by simpa [failure] using returned
  subst cacheAfter
  have committed : commit before.writer.installed (WAL.encodeBatch failure.batch) failure.proposed.walBytes
      (poisoned, before.cache, initial) = .error (.commitUnknown failure.cause) (poisoned, pending.cache, failure.failed) := by
    have initialAtWal : initial = atWal := by
      change WriteFiles.initial before.writer.history (before.writer.files.directory.staged .walBoundary) = atWal
      rw [valid.retained.directoryFiles]
    have entryCache : before.cache = seen.observed.cache := seen.cache.symm
    have failedHere : commitBytesAt directory before.writer.installed.activeFirst (WAL.encodeBatch failure.batch)
        failure.proposed.walBytes calls.append calls.stage calls.sync calls.rename (before.cache, initial) =
        .error failure.cause (pending.cache, failure.failed) := by
      rw [entryCache, initialAtWal]
      exact failed
    simp only [commit, fileEffect, failedHere]
  refine ⟨uses.writeSchedules, poisoned, got, exclude, poisonedPhase, ?_, uses⟩
  rw [entered]
  change publishPreparedWrite failure.proposed failure.table.committed setPhase
    (commit before.writer.installed (WAL.encodeBatch failure.batch) failure.proposed.walBytes)
    (entry, before.cache, initial) = _
  simp only [publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind, setPhase, heapEffect, exclude, committed]

/-- A checked rejection or an empty batch reads this table's phase
cell and leaves the reached heap and file projection unchanged.
The first phase setter and the publication callbacks are arbitrary
because neither branch reaches them. -/
theorem NativeReadPosition.preflightsViaOpenReferences {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)} {entry : heap}
    (read : get phase entry = .ok current.state.session.phase entry)
    {request : WriteRequest} (seen : NativeWritePreflightObservation current.state request)
    (atEntry : OpenWriteFiles)
    (setPhase : Phase Installed → EStateM DiskWriteError (heap × OpenWriteFiles) Unit)
    (commit : Installed → ByteArray → Nat → EStateM DiskWriteError (heap × OpenWriteFiles) Unit) :
    let directory := current.state.session.directory
    let load : EStateM DiskWriteError (heap × OpenWriteFiles) Installed := do
      let state ← heapEffect .rejected (get phase)
      liftExcept ((state.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
    let guard := fun state => liftExcept ((checkActiveSegmentWith directory state seen.lookup :
      Except IO.Error Unit).mapError DiskWriteError.rejected)
    db.UsesOpenWriteSchedules directory files phase ∧
    NativeWritePreflightStep current seen current ∧
    (match request with
      | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
          (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
            event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
      | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
          (fun state batch count => commit state (WAL.encodeBatch batch) count))
      (entry, atEntry) = seen.resultAt (entry, atEntry) := by
  intro directory load guard
  refine ⟨uses.writeSchedules, current.preflightsWrite seen, ?_⟩
  have valid := current.readPrefix.refines.1
  have loaded : load (entry, atEntry) = .ok current.state.writer.installed (entry, atEntry) := by
    simp [load, heapEffect, read, valid.phase, Phase.installed, Bind.bind, EStateM.bind, liftExcept, Pure.pure,
      EStateM.pure, Except.pure, Except.mapError]
  obtain ⟨lookup, response, reported⟩ := seen
  cases request with
  | single key value =>
    obtain ⟨next, prepared⟩ := valid.retained.preparesSingleWrite key value
    cases reported with
    | empty rows => simp [WriteRequest.rows] at rows
    | rejected rejected =>
      cases rejected with
      | byteCount _ overflow =>
        have tooLarge : ¬ current.state.writer.installed.walBytes + WAL.frameSize < UInt64.size := by
          simpa [WriteRequest.rows] using Nat.not_lt.mpr overflow
        simp [withPreparedSingleWrite, loaded, prepared, requireWritePreparation, tooLarge, Bind.bind, EStateM.bind,
          Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          NativeWritePreflightObservation.resultAt]
      | sequence _ _ exhausted =>
        simp [WriteRequest.rows, prepareBatch_singleton, prepared] at exhausted
      | active _ room _ checked =>
        have fits : current.state.writer.installed.walBytes + WAL.frameSize < UInt64.size := by
          simpa [WriteRequest.rows] using room
        simp [withPreparedSingleWrite, loaded, prepared, requireWritePreparation, fits, guard, directory, checked,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Except.mapError, liftExcept,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw, NativeWritePreflightObservation.resultAt]
  | batch rows =>
    cases reported with
    | empty nil =>
      change rows = [] at nil
      subst rows
      simp [writeBatchSchedule, loaded, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        NativeWritePreflightObservation.resultAt]
    | rejected rejected =>
      have nonempty (present : (WriteRequest.batch rows).rows ≠ []) : rows.isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr present
      cases rejected with
      | byteCount present overflow =>
        simp only [WriteRequest.rows] at overflow
        simp [writeBatchSchedule, loaded, nonempty present, Nat.not_lt.mpr overflow, Bind.bind, EStateM.bind,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          NativeWritePreflightObservation.resultAt]
      | sequence present room exhausted =>
        simp only [WriteRequest.rows] at room exhausted
        simp [writeBatchSchedule, loaded, nonempty present, room, exhausted, requireWritePreparation,
          Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          NativeWritePreflightObservation.resultAt]
      | active present room prepared checked =>
        simp only [WriteRequest.rows] at room prepared
        simp [writeBatchSchedule, loaded, nonempty present, room, prepared, requireWritePreparation, guard, directory,
          checked, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Except.mapError, liftExcept,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw, NativeWritePreflightObservation.resultAt]

/-- Interpret the original single or batch schedule on the reached phase
cell and a fixed set of projected native file callbacks. -/
def WriteRequest.runOnOpenPhase (request : WriteRequest) (directory : DiskDirectory)
    (calls : Calls (DescriptorInventory × DescriptorSlot × Nat)) (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) :
    EStateM DiskWriteError (heap × OpenWriteFiles) UInt64 :=
  let load : EStateM DiskWriteError (heap × OpenWriteFiles) Installed := do
    let current ← heapEffect .rejected (get phase)
    liftExcept ((current.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
  let guard := fun current => liftExcept ((checkActiveSegmentWith directory current calls.lookup :
    Except IO.Error Unit).mapError DiskWriteError.rejected)
  let setPhase := fun current => heapEffect .rejected (set phase current)
  let commit := fun (current : Installed) bytes count =>
    fileEffect .commitUnknown (commitBytesAt directory current.activeFirst bytes count
      calls.append calls.stage calls.sync calls.rename)
  match request with
  | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
      (fun current event next bytes => publishPreparedWrite { current with table := next, walBytes := bytes }
        event.sequence setPhase (commit current (WAL.encodeFrame event) bytes))
  | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
      (fun current batch count => commit current (WAL.encodeBatch batch) count)

/-- Read the reached phase from the same cell and retain the original
result, reached file/cache projection and held owner. -/
def projectOpenWriteResult (contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (phase : IO.Ref (Phase Installed)) (owners : LockOwners) :
    EStateM.Result DiskWriteError (heap × OpenWriteFiles) UInt64 →
      Option (EStateM.Result DiskWriteError (WriteCallState (DescriptorInventory × DescriptorSlot × Nat)) UInt64)
  | .ok result (after, files) => (contents after phase).map fun current => .ok result (current, ⟨files, owners⟩)
  | .error cause (after, files) => (contents after phase).map fun current => .error cause (current, ⟨files, owners⟩)

/-- Invert the actual returned single or batch schedule on this opened
cell. Every reached branch projects to the same committed value or
classified diagnostic and file/cache and phase state. The primitive
live-cell contract supplies successful get/set effects. File callbacks
are interpreted in their existing projected image. -/
theorem NativeReadPosition.classifiesWriteOnOpenPhase {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase)
    (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (cache : calls.cache = current.state.cache) :
    let state := current.state
    let initial := WriteFiles.initial state.writer.history (state.files.image.directory.staged .walBoundary)
    let actual := request.runOnOpenPhase state.session.directory calls phase get set (entry, state.cache, initial)
    db.UsesOpenWriteSchedules state.session.directory files phase ∧
      projectOpenWriteResult contents phase state.writer.owners actual =
        some (calls.run request state.session.directory state.writer) := by
  intro state initial actual
  have valid := current.readPrefix.refines.1
  have phaseReady := valid.phase
  have loaded := effects.reads entry phase current.state.session.phase stored
  have initialized : (entry, state.cache, initial) = (entry, (WriteRequest.readyCall state.writer calls.cache).2.image) := by
    rw [cache]
    rfl
  refine ⟨uses.writeSchedules, ?_⟩
  have classified := request.classifiesReadyReturn valid.retained (WriteRequest.readyCall state.writer calls.cache).2
    calls.lookup calls.append calls.stage calls.sync calls.rename
  change ReadyWriteReturn request state.session.directory state.writer.installed calls.lookup calls.append calls.stage
    calls.sync calls.rename (WriteRequest.readyCall state.writer calls.cache).2
      (calls.run request state.session.directory state.writer) at classified
  have enters (checked : CheckedWriteRequest request state.session.directory state.writer.installed calls.lookup) :
      actual = publishPreparedWrite checked.next checked.table.committed (fun current => heapEffect .rejected (set phase current))
        (fileEffect .commitUnknown (commitBytesAt state.session.directory state.writer.installed.activeFirst
          (WAL.encodeBatch checked.batch) checked.next.walBytes calls.append calls.stage calls.sync calls.rename))
        (entry, (WriteRequest.readyCall state.writer calls.cache).2.image) := by
    have active : (checkActiveSegmentWith state.session.directory state.writer.installed calls.lookup : Except IO.Error Unit) = .ok () :=
      checked.sameLookup ▸ checked.guard.checkedForWrite
    dsimp only [actual]
    rw [initialized]
    unfold WriteRequest.runOnOpenPhase
    refine preparedWrite_reachesPublication request rfl checked.nonempty checked.prepared checked.fits
      (do
        let current ← heapEffect .rejected (get phase)
        liftExcept ((current.installed : Except IO.Error Installed).mapError DiskWriteError.rejected))
      (fun current => liftExcept ((checkActiveSegmentWith state.session.directory current calls.lookup :
        Except IO.Error Unit).mapError DiskWriteError.rejected))
      (fun current => heapEffect .rejected (set phase current))
      (fun current bytes count => fileEffect .commitUnknown (commitBytesAt state.session.directory current.activeFirst bytes count
        calls.append calls.stage calls.sync calls.rename)) ?_ ?_
    · simp [heapEffect, loaded, phaseReady, Phase.installed, Bind.bind, EStateM.bind, liftExcept, Pure.pure,
        EStateM.pure, Except.pure, Except.mapError, state]
    · simp [active, liftExcept, Pure.pure, EStateM.pure, Except.mapError]
  have preflight (seen : NativeWritePreflightObservation current.state request) (sameLookup : seen.lookup = calls.lookup) :
      actual = seen.resultAt (entry, (WriteRequest.readyCall state.writer calls.cache).2.image) := by
    dsimp only [actual]
    rw [initialized]
    unfold WriteRequest.runOnOpenPhase
    obtain ⟨_, _, returned⟩ := current.preflightsViaOpenReferences db uses loaded seen
      (WriteRequest.readyCall state.writer calls.cache).2.image
      (fun current => heapEffect .rejected (set phase current))
      (fun current bytes count => fileEffect .commitUnknown (commitBytesAt state.session.directory current.activeFirst bytes count
        calls.append calls.stage calls.sync calls.rename))
    rw [sameLookup] at returned
    exact returned
  generalize calls.run request state.session.directory state.writer = result at classified ⊢
  cases classified with
  | empty rows =>
    let seen : NativeWritePreflightObservation current.state request :=
      ⟨calls.lookup, .ok state.writer.installed.table.committed, .empty rows⟩
    rw [preflight seen rfl]
    simp [projectOpenWriteResult, NativeWritePreflightObservation.resultAt, seen, stored, phaseReady, state]
  | @rejected cause rejected =>
    let seen : NativeWritePreflightObservation current.state request := ⟨calls.lookup, .error cause, .rejected rejected⟩
    rw [preflight seen rfl]
    simp [projectOpenWriteResult, NativeWritePreflightObservation.resultAt, seen, stored, phaseReady, state]
  | acknowledged checked committed =>
    obtain ⟨poisoned, setPoisoned, poison⟩ := effects.writes entry phase current.state.session.phase .poisoned stored
    obtain ⟨reached, setReady, ready⟩ := effects.writes poisoned phase .poisoned (.ready checked.next) poison
    rw [enters checked]
    simp only [publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind, heapEffect, setPoisoned, fileEffect,
      committed, setReady, Pure.pure, EStateM.pure, projectOpenWriteResult, ready, Option.map_some]
  | uncertain checked failed =>
    obtain ⟨poisoned, setPoisoned, poison⟩ := effects.writes entry phase current.state.session.phase .poisoned stored
    rw [enters checked]
    simp only [publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind, heapEffect, setPoisoned, fileEffect,
      failed, projectOpenWriteResult, poison, Option.map_some]

end Alvoki.Storage.DiskSession
