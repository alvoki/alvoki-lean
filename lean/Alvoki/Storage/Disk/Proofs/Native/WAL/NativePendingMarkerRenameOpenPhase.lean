import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedPosition
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativePendingMarkerRename

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit SyncHandleRouting

variable {heap files stop : Type}

private abbrev InterruptedWrite (heap files stop : Type) :=
  ExceptT DiskWriteError (EStateM stop (heap × files))

private def phaseAction {α : Type} (action : EStateM IO.Error heap α) : InterruptedWrite heap files stop α :=
  fun (before, files) => match action before with
    | .ok value reached => .ok (.ok value) (reached, files)
    | .error cause reached => .ok (.error (.rejected cause)) (reached, files)

private def publishAction (publish : ExceptT IO.Error (EStateM stop files) Unit) :
    InterruptedWrite heap files stop Unit :=
  fun (heap, files) => match publish.run files with
    | .ok result reached => .ok (result.mapError .commitUnknown) (heap, reached)
    | .error issued reached => .error issued (heap, reached)

/-- Interpret either public write schedule with the original opened
phase getter and setter. A returned write error remains an `Except`
value. The outer stop records a call that has no return. -/
def WriteRequest.runWithInterruptionOnOpenPhase (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (publish : Installed → ByteArray → Nat → ExceptT IO.Error (EStateM stop files) Unit)
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) :
    EStateM stop (heap × files) (Except DiskWriteError UInt64) :=
  let load : InterruptedWrite heap files stop Installed := do
    let state ← phaseAction (get phase)
    liftExcept ((state.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
  let check : Installed → InterruptedWrite heap files stop Unit := fun installed => liftExcept
    ((checkActiveSegmentWith directory installed lookup : Except IO.Error Unit).mapError DiskWriteError.rejected)
  let requirePrepared : {α : Type} → Option α → InterruptedWrite heap files stop α :=
    fun {_} result => match result with
      | some prepared => pure prepared
      | none => throw (.rejected (IO.userError "write sequence space exhausted"))
  let setPhase := fun state => phaseAction (set phase state)
  let commit := fun installed bytes count => publishAction (publish installed bytes count)
  (match request with
    | .single key value => withPreparedSingleWrite key value load DiskWriteError.rejected requirePrepared check
        (fun state event next bytes => publishPreparedWrite { state with table := next, walBytes := bytes }
          event.sequence setPhase (commit state (WAL.encodeFrame event) bytes))
    | .batch rows => writeBatchSchedule rows load DiskWriteError.rejected requirePrepared check setPhase
        (fun state batch count => commit state (WAL.encodeBatch batch) count)).run

/-- Successful preparation and the original WAL guard reach the
publication in the poisoned phase. An outer stop exits that same
schedule before the final phase setter and acknowledgement. -/
theorem WriteRequest.stopsPublicationOnOpenPhase (request : WriteRequest) (directory : DiskDirectory)
    {rows : List (UInt64 × Option UInt64)} (submitted : request.rows = rows) (nonempty : rows ≠ [])
    {installed : Installed} {events : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch installed.table rows = some (events, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {lookup : FilePath → Except IO.Error IO.FS.Metadata}
    (checked : checkActiveSegmentWith directory installed lookup = .ok ())
    (publish : Installed → ByteArray → Nat → ExceptT IO.Error (EStateM stop files) Unit)
    {phase : IO.Ref (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {entry poisoned : heap} (loaded : get phase entry = .ok (.ready installed) entry)
    (excluded : set phase .poisoned entry = .ok () poisoned)
    {before reached : files} {issued : stop}
    (stopped : (publish installed (WAL.encodeBatch events) (installed.walBytes + WAL.frameSize * rows.length)).run before =
      .error issued reached) :
    request.runWithInterruptionOnOpenPhase directory lookup publish phase get set (entry, before) =
      .error issued (poisoned, reached) := by
  change publish installed (WAL.encodeBatch events) (installed.walBytes + WAL.frameSize * rows.length) before =
    .error issued reached at stopped
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
      simp only [List.length_singleton, Nat.mul_one, WAL.encodeBatch_singleton] at stopped
      simp [runWithInterruptionOnOpenPhase, withPreparedSingleWrite, prepareWrite, phaseAction, publishAction,
        publishPreparedWrite, publishPrepared, loaded, written, count, checked, excluded, stopped, Phase.installed,
        liftExcept, Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
        Pure.pure, ExceptT.pure, EStateM.pure]
  | batch group =>
    change group = rows at submitted
    subst rows
    have present : group.isEmpty = false := by cases group <;> simp_all
    simp [runWithInterruptionOnOpenPhase, writeBatchSchedule, phaseAction, publishAction, publishPreparedWrite,
      publishPrepared, present, fits, prepared, loaded, checked, excluded, stopped, Phase.installed, liftExcept,
      Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure,
      ExceptT.pure, EStateM.pure]

section

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

/-- The same returned publication prefix leaves both files synced and
the consumed marker slot finalized before the sole rename callback. -/
noncomputable def NativeReadyWriteFileSyncs.beforeMarkerRename (seen : NativeReadyWriteFileSyncs prepared) :=
  observeReturnedWriteCall (stop := stop) seen.afterSelect (seen.append prepared.keeperPath (WAL.encodeBatch prepared.batch)) >>= fun _ =>
  observeReturnedWriteCall (stop := stop) seen.afterMarkerOpen (seen.stage prepared.stagedPath prepared.marker) >>= fun _ =>
  observeReturnedWriteCall (stop := stop) seen.census (seen.sync #[prepared.keeperPath, prepared.stagedPath])

theorem NativeReadyWriteFileSyncs.reachesMarkerRename (seen : NativeReadyWriteFileSyncs prepared) :
    (seen.beforeMarkerRename (stop := stop)).run (state.cache, state.census, prepared.initial) =
      .ok (.ok ()) (seen.appendCache, seen.census, prepared.bothSynced) := by
  simp only [beforeMarkerRename, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, seen.appendReturns, seen.stageReturns, seen.groupReturns]

noncomputable def NativeWriteMarkerRenameStop.onOpenPhase (seen : NativeWriteMarkerRenameStop prepared)
    (opened : NativeOpenedHandle heap) :=
  seen.request.runWithInterruptionOnOpenPhase state.session.directory seen.synced.activeGuard.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (fun path payload => observeReturnedWriteCall seen.synced.afterSelect (seen.synced.append path payload))
      (fun path payload => observeReturnedWriteCall seen.synced.afterMarkerOpen (seen.synced.stage path payload))
      (fun paths => observeReturnedWriteCall seen.synced.census (seen.synced.sync paths))
      (fun source target (cache, files) => match seen.rename source target files with
        | .ok result next => .ok result (cache, next)
        | .error issued next => .error issued (cache, next))) opened.phase opened.get opened.set

end

variable {opened : NativeOpenedHandle heap}

/-- The opened table reads its original phase and stores poison on
that cell. The successful append, stage and grouped fsync reach the
same custody as the reported marker rename, whose outer stop has no
write response. The existing endpoint determines both crash choices. -/
theorem NativeOpenedPosition.stopsWriteAtMarkerRename (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state}
    (seen : NativeWriteMarkerRenameStop prepared) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerRename current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      (seen.synced.beforeMarkerRename (stop := FilePath × FilePath)).run (state.cache, state.census, prepared.initial) =
        .ok (.ok ()) (seen.synced.appendCache, seen.synced.census, prepared.bothSynced) ∧
      seen.rename prepared.stagedPath prepared.markerPath (seen.synced.census, prepared.bothSynced) =
        .error (prepared.stagedPath, prepared.markerPath) seen.reached ∧
      seen.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error (prepared.stagedPath, prepared.markerPath) (poisoned, seen.synced.appendCache, seen.reached) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let guard := seen.synced.activeGuard
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed guard.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    have regular : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
      guard.extent, regular, Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨current.uses.writeSchedules, current.current.ready.stopsAtMarkerRename seen, poisoned, loaded,
    excluded, poison, seen.synced.reachesMarkerRename, seen.stopped, ?_⟩
  unfold NativeWriteMarkerRenameStop.onOpenPhase
  apply seen.request.stopsPublicationOnOpenPhase state.session.directory seen.rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  exact seen.stopsPublication

end Alvoki.Storage.DiskSession
