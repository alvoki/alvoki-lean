import Alvoki.Storage.Disk.MixedTraceSnapshotReads

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotPin SnapshotTable)
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

/-- A successful read response carries the active snapshot sequence at
the time of the operation. Point absence is a value of a successful read. -/
inductive RecordedSnapshotRead where
  | lookup (sequence key : UInt64) (value : Option UInt64)
  | range (sequence lo hi : UInt64) (entries : List (Compaction.Model.Entry (Option UInt64)))

def RecordedSnapshotRead.agrees (read : RecordedSnapshotRead) (reference : SnapshotTable UInt64) : Prop :=
  match read with
  | .lookup sequence key value => value = reference.table.lookup key sequence
  | .range sequence lo hi entries => entries = reference.table.range lo hi sequence

/-- The point and range guards use the reported ready phase and pointer
comparison of a local active pin at this writer. -/
structure ObservedLocalPin (directory : DiskDirectory) (descriptor : Nat) (writer : SegmentedWriterState) where
  session : SegmentedSession
  sameDirectory : session.directory = directory
  sameDescriptor : session.descriptor = descriptor
  phase : session.phase = .ready writer.installed
  pin : SnapshotPin
  active : pin ∈ writer.installed.table.pins.active
  issuer : Nat
  localToken : issuer = session.sessionRef
  sameSession : Bool
  compared : sameSession = decide (issuer = session.sessionRef)

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
group in order and only submitted writes. That same replay explains
every recorded successful point and range response. -/
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
