import Alvoki.Storage.Disk.MixedTraceSnapshotReads

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin SnapshotTable)
open WalSegmentRepair
open scoped List

/-- The second trace starts at the exact writer and lock description
returned by the first. Its submitted groups follow the earlier groups. -/
theorem SegmentedBatchDatabaseTrace.append
    (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection priorLog middleDescriptor middle)
    (suffix : SegmentedBatchDatabaseTrace directory middleDescriptor middle allowCollection log descriptor last) :
    SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection (priorLog ++ log) descriptor last := by
  induction suffix with
  | start => simpa using prior
  | ordinary _ step ih => simpa only [List.append_assoc] using ih.ordinary step
  | table _ step ih => exact .table ih step
  | checkpoint _ observed installed ih => exact .checkpoint ih observed installed
  | cleanReopenObserved _ closed endpoint ih => exact .cleanReopenObserved ih closed endpoint
  | checkpointManifestStageError _ endpoint ih => exact .checkpointManifestStageError ih endpoint
  | checkpointManifestError _ endpoint ih => exact .checkpointManifestError ih endpoint
  | checkpointRunError _ endpoint ih => exact .checkpointRunError ih endpoint
  | checkpointPowerLossObserved _ cut projected survives failures selected installed ih =>
    exact .checkpointPowerLossObserved ih cut projected survives failures selected installed
  | acknowledgedBatch _ report selected ih => simpa only [List.append_assoc] using ih.acknowledgedBatch report selected
  | batchError _ report installed ih => simpa only [List.append_assoc] using ih.batchError report installed
  | batchErrorAdmitted _ failure observed installed ih =>
    simpa only [List.append_assoc] using ih.batchErrorAdmitted failure observed installed
  | batchPowerLoss _ cut observed report installed ih =>
    simpa only [List.append_assoc] using ih.batchPowerLoss cut observed report installed
  | batchMarkerProcessExit _ cut observed report installed ih =>
    simpa only [List.append_assoc] using ih.batchMarkerProcessExit cut observed report installed
  | batchMarkerAdmitted _ cut observed installed ih =>
    simpa only [List.append_assoc] using ih.batchMarkerAdmitted cut observed installed
  | batchAppendPowerLoss _ report observed installed ih =>
    simpa only [List.append_assoc] using ih.batchAppendPowerLoss report observed installed
  | batchAppendProcessExit _ report observed installed ih =>
    simpa only [List.append_assoc] using ih.batchAppendProcessExit report observed installed
  | batchAppendAdmitted _ report installed ih =>
    simpa only [List.append_assoc] using ih.batchAppendAdmitted report installed
  | collectRuns enabled _ reports ih => exact .collectRuns enabled ih reports
  | collectRunsPowerLoss enabled _ loss installed ih => exact .collectRunsPowerLoss enabled ih loss installed
  | rotationPowerLossAdmitted _ cut installed ih => exact .rotationPowerLossAdmitted ih cut installed

/-- The token identities and reached registry entry for the supplied handle.
A foreign token cannot use a coinciding local handle number. -/
structure SnapshotReadGuard where
  issuer : Nat
  current : Nat
  handle : SnapshotHandle
  registered : Option SnapshotPin

def SnapshotReadGuard.rejects (guard : SnapshotReadGuard) : Prop :=
  guard.issuer ≠ guard.current ∨ (guard.issuer = guard.current ∧ guard.registered = none)

/-- Successful responses use the pin's sequence at the time of the read.
Denied responses retain the reached guard evidence for the requested handle. -/
inductive RecordedSnapshotRead where
  | lookup (sequence key : UInt64) (value : Option UInt64)
  | range (sequence lo hi : UInt64) (entries : List (Compaction.Model.Entry (Option UInt64)))
  | lookupDenied (key : UInt64) (guard : SnapshotReadGuard)
  | rangeDenied (lo hi : UInt64) (guard : SnapshotReadGuard)

def RecordedSnapshotRead.agrees (read : RecordedSnapshotRead) (reference : SnapshotTable UInt64) : Prop :=
  match read with
  | .lookup sequence key value => value = reference.table.lookup key sequence
  | .range sequence lo hi entries => entries = reference.table.range lo hi sequence
  | .lookupDenied _ guard | .rangeDenied _ _ guard => guard.rejects

/-- The ready read schedule consumes the observed phase and pointer
comparison at its reached writer. -/
structure ObservedSnapshotReader (directory : DiskDirectory) (descriptor : Nat) (writer : SegmentedWriterState) where
  session : SegmentedSession
  sameDirectory : session.directory = directory
  sameDescriptor : session.descriptor = descriptor
  phase : session.phase = .ready writer.installed
  issuer : Nat
  sameSession : Bool
  compared : sameSession = decide (issuer = session.sessionRef)

def ObservedSnapshotReader.guard (observed : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) : SnapshotReadGuard :=
  ⟨observed.issuer, observed.session.sessionRef, handle, writer.installed.table.pins.find handle⟩

theorem ObservedSnapshotReader.readResult (observed : ObservedSnapshotReader directory descriptor writer)
    (read : PackedTable → Option α) :
    observed.session.runSnapshotRead observed.sameSession read =
      .ok (if observed.issuer = observed.session.sessionRef then read writer.installed.table else none)
        observed.session := by
  rw [SegmentedSession.runSnapshotRead, observed.phase, observed.compared]
  by_cases localToken : observed.issuer = observed.session.sessionRef <;>
    simp [localToken, readSnapshotWith, withLocalHandle, Phase.installed, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

private theorem ObservedSnapshotReader.readNone_iff (observed : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (read : PackedTable → Option α) (readAt : SnapshotPin → α)
    (fromRegistry : read writer.installed.table = (writer.installed.table.pins.find handle).map readAt) :
    observed.session.runSnapshotRead observed.sameSession read = .ok none observed.session ↔
      (observed.guard handle).rejects := by
  rw [observed.readResult, fromRegistry]
  unfold ObservedSnapshotReader.guard SnapshotReadGuard.rejects
  by_cases localToken : observed.issuer = observed.session.sessionRef
  · cases writer.installed.table.pins.find handle <;> simp [localToken]
  · simp [localToken]

/-- A ready point response has outer absence precisely when the guard
rejects the token or the local pin is inactive. -/
theorem ObservedSnapshotReader.lookupDenied_iff (observed : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (key : UInt64) :
    observed.session.runSnapshotRead observed.sameSession (fun table => table.lookup handle key) =
      .ok none observed.session ↔ (observed.guard handle).rejects :=
  observed.readNone_iff handle _ (fun pin => writer.installed.table.lookupAt key pin.sequence) rfl

theorem ObservedSnapshotReader.rangeDenied_iff (observed : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (lo hi : UInt64) :
    observed.session.runSnapshotRead observed.sameSession (fun table => table.range handle lo hi) =
      .ok none observed.session ↔ (observed.guard handle).rejects :=
  observed.readNone_iff handle _ (fun pin => writer.installed.table.rangeAt lo hi pin.sequence) rfl

/-- A successfully guarded pin is active at the reached writer and its
issuing token identifies that same session. -/
structure ObservedLocalPin (directory : DiskDirectory) (descriptor : Nat) (writer : SegmentedWriterState)
    extends ObservedSnapshotReader directory descriptor writer where
  pin : SnapshotPin
  active : pin ∈ writer.installed.table.pins.active
  localToken : issuer = session.sessionRef

inductive RecordedSnapshotRead.Observed (directory : DiskDirectory) (descriptor : Nat)
    (writer : SegmentedWriterState) : RecordedSnapshotRead → Prop where
  | lookup (pin : ObservedLocalPin directory descriptor writer)
      (returned : pin.session.runSnapshotRead pin.sameSession (fun table => table.lookup pin.pin.handle key) =
        .ok (some value) pin.session) :
      Observed directory descriptor writer (.lookup pin.pin.sequence key value)
  | range (pin : ObservedLocalPin directory descriptor writer)
      (returned : pin.session.runSnapshotRead pin.sameSession (fun table => table.range pin.pin.handle lo hi) =
        .ok (some entries) pin.session) :
      Observed directory descriptor writer (.range pin.pin.sequence lo hi entries)
  | lookupDenied (reader : ObservedSnapshotReader directory descriptor writer) (handle : SnapshotHandle)
      (returned : reader.session.runSnapshotRead reader.sameSession (fun table => table.lookup handle key) =
        .ok none reader.session) :
      Observed directory descriptor writer (.lookupDenied key (reader.guard handle))
  | rangeDenied (reader : ObservedSnapshotReader directory descriptor writer) (handle : SnapshotHandle)
      (returned : reader.session.runSnapshotRead reader.sameSession (fun table => table.range handle lo hi) =
        .ok none reader.session) :
      Observed directory descriptor writer (.rangeDenied lo hi (reader.guard handle))

/-- A successful native result identifies a local registered pin. The
caller supplies only the handle, the reached comparison and the result. -/
private theorem ObservedSnapshotReader.localPinOfSome (reader : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (read : PackedTable → Option α) (readAt : SnapshotPin → α)
    (fromRegistry : read writer.installed.table = (writer.installed.table.pins.find handle).map readAt)
    (returned : reader.session.runSnapshotRead reader.sameSession read = .ok (some value) reader.session) :
    ∃ pin : ObservedLocalPin directory descriptor writer,
      pin.toObservedSnapshotReader = reader ∧ pin.pin.handle = handle := by
  rw [reader.readResult, fromRegistry] at returned
  by_cases localToken : reader.issuer = reader.session.sessionRef
  · cases found : writer.installed.table.pins.find handle with
    | none => simp [localToken, found] at returned
    | some pin =>
      change List.find? (fun pin => decide (pin.handle = handle)) writer.installed.table.pins.active = some pin at found
      have active := List.mem_of_find?_eq_some found
      have compared := List.find?_some (p := fun candidate : SnapshotPin => decide (candidate.handle = handle)) found
      have sameHandle : pin.handle = handle := of_decide_eq_true compared
      exact ⟨⟨reader, pin, active, localToken⟩, rfl, sameHandle⟩
  · simp [localToken] at returned

theorem ObservedSnapshotReader.recordLookup (reader : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (key : UInt64) (result : Option (Option UInt64))
    (returned : reader.session.runSnapshotRead reader.sameSession (fun table => table.lookup handle key) =
      .ok result reader.session) :
    match result with
    | none => RecordedSnapshotRead.Observed directory descriptor writer (.lookupDenied key (reader.guard handle))
    | some value =>
      ∃ pin, writer.installed.table.pins.find handle = some pin ∧
        RecordedSnapshotRead.Observed directory descriptor writer (.lookup pin.sequence key value) := by
  cases result with
  | none => exact .lookupDenied reader handle returned
  | some _ =>
    obtain ⟨pin, sameReader, rfl⟩ :=
      reader.localPinOfSome handle _ (fun pin => writer.installed.table.lookupAt key pin.sequence) rfl returned
    subst reader
    exact ⟨pin.pin, writer.installed.table.pins.find_of_mem pin.active, .lookup pin returned⟩

theorem ObservedSnapshotReader.recordRange (reader : ObservedSnapshotReader directory descriptor writer)
    (handle : SnapshotHandle) (lo hi : UInt64) (result : Option (List (Compaction.Model.Entry (Option UInt64))))
    (returned : reader.session.runSnapshotRead reader.sameSession (fun table => table.range handle lo hi) =
      .ok result reader.session) :
    match result with
    | none => RecordedSnapshotRead.Observed directory descriptor writer (.rangeDenied lo hi (reader.guard handle))
    | some entries =>
      ∃ pin, writer.installed.table.pins.find handle = some pin ∧
        RecordedSnapshotRead.Observed directory descriptor writer (.range pin.sequence lo hi entries) := by
  cases result with
  | none => exact .rangeDenied reader handle returned
  | some _ =>
    obtain ⟨pin, sameReader, rfl⟩ :=
      reader.localPinOfSome handle _ (fun pin => writer.installed.table.rangeAt lo hi pin.sequence) rfl returned
    subst reader
    exact ⟨pin.pin, writer.installed.table.pins.find_of_mem pin.active, .range pin returned⟩

private theorem ObservedLocalPin.responsesForReplay
    (observed : ObservedLocalPin directory descriptor before)
    (ready : before.RetainedReady directory descriptor)
    (replay : SnapshotWalReplay .empty (before.history ++ trailing) reference) :
    (∀ key, observed.session.runSnapshotRead observed.sameSession (fun table => table.lookup observed.pin.handle key) =
      .ok (some (reference.table.lookup key observed.pin.sequence)) observed.session) ∧
    ∀ lo hi, observed.session.runSnapshotRead observed.sameSession (fun table => table.range observed.pin.handle lo hi) =
      .ok (some (reference.table.range lo hi observed.pin.sequence)) observed.session := by
  have readySession : before.RetainedReady observed.session.directory observed.session.descriptor := by
    rw [observed.sameDirectory, observed.sameDescriptor]
    exact ready
  exact readySession.guardedReadsForReplay observed.phase replay observed.active
    observed.localToken observed.compared

theorem RecordedSnapshotRead.Observed.agreesForReplay {read : RecordedSnapshotRead}
    (observed : RecordedSnapshotRead.Observed directory descriptor before read)
    (ready : before.RetainedReady directory descriptor)
    (replay : SnapshotWalReplay .empty (before.history ++ trailing) reference) : read.agrees reference := by
  cases observed with
  | lookup pin returned =>
    change _ = reference.table.lookup _ _
    exact Option.some.inj (EStateM.Result.ok.inj
      (returned.symm.trans ((pin.responsesForReplay ready replay).1 _))).1
  | range pin returned =>
    change _ = reference.table.range _ _ _
    exact Option.some.inj (EStateM.Result.ok.inj
      (returned.symm.trans ((pin.responsesForReplay ready replay).2 _ _))).1
  | lookupDenied reader handle returned =>
    exact (reader.lookupDenied_iff handle _).mp returned
  | rangeDenied reader handle returned =>
    exact (reader.rangeDenied_iff handle _ _).mp returned

/-- Interleave ordered read responses with admitted write and recovery
stretches. A read uses the reached writer and leaves that writer in place. -/
inductive SegmentedClientReadTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) :
    List DatabaseSubmissions → List RecordedSnapshotRead → Nat → SegmentedWriterState → Prop where
  | start : SegmentedClientReadTrace directory initialDescriptor initial allowCollection [] [] initialDescriptor initial
  | advance (prior : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
      (step : SegmentedBatchDatabaseTrace directory writer before allowCollection subsequent descriptor after) :
      SegmentedClientReadTrace directory initialDescriptor initial allowCollection (log ++ subsequent) reads descriptor after
  | read (prior : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
      (observed : RecordedSnapshotRead.Observed directory writer before response) :
      SegmentedClientReadTrace directory initialDescriptor initial allowCollection log (reads ++ [response]) writer before

theorem SegmentedClientReadTrace.writes
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor last) :
    SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last := by
  induction trace with
  | start => exact .start
  | advance _ step previous => exact previous.append step
  | read _ _ previous => exact previous

/-- Replay of the reached writer's history and any valid trailing writes
explains every response in the client log, even before a new open returns. -/
theorem SegmentedClientReadTrace.responsesForReplay
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (replayed : SnapshotWalReplay .empty (last.history ++ trailing) reference) :
    ∀ read ∈ reads, read.agrees reference := by
  induction trace generalizing trailing with
  | start => simp
  | advance prior step previous =>
    have earlier := (prior.writes.preservesRetained initialReady).1
    obtain ⟨_, retained, history, _⟩ := step.preservesRetained earlier
    rw [history, List.append_assoc] at replayed
    exact previous replayed
  | read prior observed previous =>
    intro read present
    rcases List.mem_append.mp present with earlier | latest
    · exact previous replayed read earlier
    · obtain rfl := List.mem_singleton.mp latest
      exact observed.agreesForReplay (prior.writes.preservesRetained initialReady).1 replayed

/-- A replay after a further admitted suffix explains the same recorded
responses. The suffix's retained frames extend the reached history. -/
theorem SegmentedClientReadTrace.responses
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (suffix : SegmentedBatchDatabaseTrace directory descriptor last allowCollection trailing finalDescriptor final)
    (replayed : SnapshotWalReplay .empty final.history reference) :
    ∀ read ∈ reads, read.agrees reference := by
  have ready := (trace.writes.preservesRetained initialReady).1
  obtain ⟨_, retained, history, _⟩ := suffix.preservesRetained ready
  rw [history] at replayed
  exact trace.responsesForReplay initialReady replayed

/-- From installed bootstrap, one replay includes every acknowledged
group in order and only submitted writes. The replay explains successful
reads, and the reached token and registry evidence explains denied reads. -/
theorem SegmentedClientReadTrace.keyValueRefinement
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ read ∈ reads, read.agrees reference := by
  obtain ⟨reference, replayed, retained, acknowledged, submitted, _⟩ := trace.writes.keyValueRefinement bootstrap held
  exact ⟨reference, replayed, retained, acknowledged, submitted,
    trace.responses (bootstrap.writerReady held).toRetained .start replayed⟩

/-- An observed failed checkpoint submits no write group and adds no
read result. The live reopen is an admitted continuation of the ledger. -/
theorem SegmentedClientReadTrace.afterManifestStageError {input : System.FilePath}
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before} {report : ObservedManifestStageFailure attempt}
    {manifest runs} {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {release : SegmentedFailureRelease writer}
    {opened : CheckpointHeldOpen input directory layout (report.reachedPublication manifest runs)} {session final}
    (endpoint : ManifestStageFailureReopened (report := report) release opened session final after) :
    SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads opened.calls.slot.description after := by
  simpa only [List.append_nil] using trace.advance (.checkpointManifestStageError .start endpoint)

/-- The exact returned live failure, release and reported bounded retry
extend the client ledger at the actually installed session. -/
theorem SegmentedClientReadTrace.reopenAfterManifestStageError {input : System.FilePath}
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    {attempt : SegmentedCheckpointReport directory before} {report : ObservedManifestStageFailure attempt}
    {manifest runs} (bindings : ManifestStageFailureBindings report manifest runs)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := report.reachedPublication manifest runs
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
        ManifestStageFailureReopened release opened session final after ∧
        SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads opened.calls.slot.description after := by
  intro publication attempts reports
  obtain ⟨layout, opened, session, final, after, endpoint⟩ :=
    bindings.reopens (trace.writes.preservesRetained initialReady).1 release retry attempts reports
  exact ⟨layout, opened, session, final, after, endpoint, trace.afterManifestStageError endpoint⟩

/-- The replay justifies earlier read responses and future guarded
acquisitions in the returned session, using the same submission log. -/
abbrev GuardedClientReplay (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (after : SegmentedWriterState) (session : SegmentedSession) : Prop :=
  ∃ reference : SnapshotTable UInt64,
    SnapshotWalReplay .empty after.history reference ∧
    DatabaseBatchRetention log after.history ∧
    log.flatMap DatabaseSubmissions.acknowledged <+ after.history ∧
    after.history <+ log.flatMap DatabaseSubmissions.submitted ∧
    (∀ read ∈ reads, read.agrees reference) ∧
    ∀ snapshot, after.installed.table.pins.floor ≤ snapshot → snapshot ≤ after.installed.table.committed →
      ∃ (issued : Nat × SnapshotPin) (pinned : PackedTable) (acquired : SegmentedSession),
        SegmentedSession.runAcquireAt snapshot session = .ok (some issued) acquired ∧
        acquired.phase = .ready { after.installed with table := pinned } ∧
        issued.1 = acquired.sessionRef ∧ issued.2.sequence = snapshot ∧ issued.2 ∈ pinned.pins.active ∧
        ∀ sameSession : Bool, sameSession = decide (issued.1 = acquired.sessionRef) →
          (∀ key, withLocalHandle (m := Except IO.Error) acquired.phase.installed (.ok sameSession) none
              (fun state => pure (state.table.lookup issued.2.handle key)) =
            .ok (some (reference.table.lookup key snapshot))) ∧
          ∀ start stop, withLocalHandle (m := Except IO.Error) acquired.phase.installed (.ok sameSession) none
              (fun state => pure (state.table.range issued.2.handle start stop)) =
            .ok (some (reference.table.range start stop snapshot))

/-- Use one abstract replay for previously recorded responses and reads
from every supported snapshot registered in the reached ready session. -/
theorem SegmentedClientReadTrace.guardedReplay
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads descriptor last)
    {session : SegmentedSession} (ready : session.phase = .ready last.installed) :
    GuardedClientReplay log reads last session := by
  obtain ⟨reference, replay, retained, acknowledged, submitted, readsAfter⟩ :=
    trace.writes.guardedAcquireReads bootstrap held ready
  exact ⟨reference, replay, retained, acknowledged, submitted,
    trace.responses (bootstrap.writerReady held).toRetained .start replay, readsAfter⟩

/-- The same WAL replay explains all earlier recorded responses and
guarded reads from newly acquired snapshots in the installed session.
The unchanged log still accounts for acknowledgement and submission. -/
theorem SegmentedClientReadTrace.manifestStageErrorRefines
    {first : LockedFileState WalSegmentRotation.State} {input : System.FilePath}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before} {report : ObservedManifestStageFailure attempt}
    {manifest runs} {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {release : SegmentedFailureRelease writer}
    {opened : CheckpointHeldOpen input directory layout (report.reachedPublication manifest runs)} {session final}
    (endpoint : ManifestStageFailureReopened (report := report) release opened session final after) :
    GuardedClientReplay log reads after session :=
  (trace.afterManifestStageError endpoint).guardedReplay bootstrap held endpoint.phase

end Alvoki.Storage.DiskSession
