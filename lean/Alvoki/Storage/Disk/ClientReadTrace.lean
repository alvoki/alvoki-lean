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
  | cleanReopenObserved _ closed endpoint ih => exact .cleanReopenObserved ih closed endpoint
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

private theorem ObservedLocalPin.responsesAfterSuffix
    (observed : ObservedLocalPin directory descriptor before)
    (suffix : SegmentedBatchDatabaseTrace directory descriptor before allowCollection log next last)
    (ready : before.RetainedReady directory descriptor)
    (replay : SnapshotWalReplay .empty last.history reference) :
    (∀ key, observed.session.runSnapshotRead observed.sameSession (fun table => table.lookup observed.pin.handle key) =
      .ok (some (reference.table.lookup key observed.pin.sequence)) observed.session) ∧
    ∀ lo hi, observed.session.runSnapshotRead observed.sameSession (fun table => table.range observed.pin.handle lo hi) =
      .ok (some (reference.table.range lo hi observed.pin.sequence)) observed.session := by
  have atSession : SegmentedBatchDatabaseTrace observed.session.directory observed.session.descriptor
      before allowCollection log next last := by
    rw [observed.sameDirectory, observed.sameDescriptor]
    exact suffix
  have readySession : before.RetainedReady observed.session.directory observed.session.descriptor := by
    rw [observed.sameDirectory, observed.sameDescriptor]
    exact ready
  exact atSession.guardedReadsBeforeSuffix readySession observed.phase replay observed.active
    observed.localToken observed.compared

theorem RecordedSnapshotRead.Observed.agreesAfterSuffix {read : RecordedSnapshotRead}
    (observed : RecordedSnapshotRead.Observed directory descriptor before read)
    (suffix : SegmentedBatchDatabaseTrace directory descriptor before allowCollection log next last)
    (ready : before.RetainedReady directory descriptor)
    (replay : SnapshotWalReplay .empty last.history reference) : read.agrees reference := by
  cases observed with
  | lookup pin returned =>
    change _ = reference.table.lookup _ _
    exact Option.some.inj (EStateM.Result.ok.inj
      (returned.symm.trans ((pin.responsesAfterSuffix suffix ready replay).1 _))).1
  | range pin returned =>
    change _ = reference.table.range _ _ _
    exact Option.some.inj (EStateM.Result.ok.inj
      (returned.symm.trans ((pin.responsesAfterSuffix suffix ready replay).2 _ _))).1
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

/-- A replay of the exact trace and any further admitted suffix
explains every response recorded in chronological order. -/
theorem SegmentedClientReadTrace.responses
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (suffix : SegmentedBatchDatabaseTrace directory descriptor last allowCollection trailing finalDescriptor final)
    (replayed : SnapshotWalReplay .empty final.history reference) :
    ∀ read ∈ reads, read.agrees reference := by
  induction trace generalizing trailing finalDescriptor final reference with
  | start => simp
  | advance _ step previous => exact previous (step.append suffix) replayed
  | read prior observed previous =>
    intro read present
    rcases List.mem_append.mp present with earlier | latest
    · exact previous suffix replayed read earlier
    · obtain rfl := List.mem_singleton.mp latest
      exact observed.agreesAfterSuffix suffix (prior.writes.preservesRetained initialReady).1 replayed

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

end Alvoki.Storage.DiskSession
