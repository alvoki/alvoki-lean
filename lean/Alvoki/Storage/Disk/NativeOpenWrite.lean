import Alvoki.Storage.Disk.NativeOpenAcquire

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
    let before := current.state
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
    db.UsesOpenWriteSchedules directory files phase ∧
    ∃ (poisoned reached : heap) (target : Target)
      (next : NativeReadPosition (history ++ prepared.batch) (log ++ [.acknowledgedBatch prepared.batch])),
      get phase entry = .ok current.state.session.phase entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some .poisoned ∧
      set phase (.ready seen.publication.nextInstalled) poisoned = .ok () reached ∧
      contents reached phase = some next.state.session.phase ∧
      (match request with
        | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requireWritePreparation guard
            (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
              event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
        | .batch group => writeBatchSchedule group load DiskWriteError.rejected requireWritePreparation guard setPhase
            (fun state batch count => commit state (WAL.encodeBatch batch) count))
        (entry, before.cache, prepared.initial) = .ok prepared.table.committed (reached, seen.appendCache, prepared.settled) ∧
      next.state = seen.next target ∧
      next.reads = current.reads ∧
      db.UsesOpenReferences next.state.session.directory lock files phase token ∧
      InstalledClientReplay (log ++ [.acknowledgedBatch prepared.batch]) current.reads
        (history ++ prepared.batch) next.state.writer.installed next.state.session := by
  intro before directory load guard setPhase commit
  obtain ⟨target, next, _, nextState, _, reads, _, _, _, replay⟩ := current.acknowledgesWrite seen request rows
  have ready := current.readPrefix.refines.1.phase
  have got := effects.reads entry phase before.session.phase stored
  have loaded : load (entry, before.cache, prepared.initial) = .ok before.writer.installed (entry, before.cache, prepared.initial) := by
    simp [load, heapEffect, before, got, ready, Phase.installed, Bind.bind, EStateM.bind, liftExcept, Pure.pure,
      EStateM.pure, Except.pure, Except.mapError]
  have guarded : guard before.writer.installed (entry, before.cache, prepared.initial) =
      .ok () (entry, before.cache, prepared.initial) := by
    have checked : (checkActiveSegmentWith directory before.writer.installed seen.calls.lookup : Except IO.Error Unit) =
        .ok () := seen.activeGuard.checkedForWrite
    simp only [guard, checked, Except.mapError, liftExcept, Pure.pure, EStateM.pure]
  obtain ⟨poisoned, exclude, poisonedPhase⟩ := effects.writes entry phase before.session.phase .poisoned stored
  obtain ⟨reached, publish, readyPhase⟩ := effects.writes poisoned phase .poisoned
    (.ready seen.publication.nextInstalled) poisonedPhase
  have entered := preparedWrite_reachesPublication request rows prepared.nonempty prepared.prepared prepared.fits
    load guard setPhase commit loaded guarded
  have committed : commit before.writer.installed (WAL.encodeBatch prepared.batch) prepared.count
      (poisoned, before.cache, prepared.initial) = .ok () (poisoned, seen.appendCache, prepared.settled) := by
    simp only [commit, fileEffect, directory, before, seen.publishes]
  refine ⟨uses.writeSchedules, poisoned, reached, target, next, got, exclude, poisonedPhase, publish, ?_, ?_,
    nextState, reads, ?_, replay⟩
  · rw [nextState]
    exact readyPhase
  · rw [entered]
    change publishPreparedWrite seen.publication.nextInstalled prepared.table.committed setPhase
      (commit before.writer.installed (WAL.encodeBatch prepared.batch) prepared.count)
      (entry, before.cache, prepared.initial) = _
    simp only [publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind, setPhase, heapEffect, exclude,
      committed, publish, Pure.pure, EStateM.pure]
  · rw [nextState]
    exact uses

end Alvoki.Storage.DiskSession
