import Alvoki.Storage.Disk.DiskLockLifecycle
import Alvoki.Storage.Disk.SessionReadGuards

namespace Alvoki.Storage

open Sequential (SnapshotPin SnapshotPins)

/-- The pin returned by a successful acquisition is active in its returned table. -/
theorem PackedTable.acquireAt_active {before after : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (acquired : before.acquireAt snapshot = some (pin, after)) :
    pin ∈ after.pins.active := by
  obtain ⟨⟨_, pins⟩, recorded, same⟩ := Option.map_eq_some_iff.mp acquired
  cases same
  change pin ∈ pins.active
  obtain ⟨_, _, _, _, active, _, _⟩ := SnapshotPins.acquire_spec recorded
  rw [active]
  exact List.mem_cons_self ..

end Alvoki.Storage

namespace Alvoki.Storage.DiskSession

/-- Apply the outer native lock schedule to the reported shared recovery.
The lock interpreter carries the exact installation and file image on success.
The error callback supplies the native cause represented by a recovery error. -/
def runLockedMarkedOpen (directory : DiskDirectory) (descriptor : Nat) (acquired : Except IO.Error Bool)
    (unlock : UnlockReport) (cause : String → IO.Error)
    (recovery : EStateM.Result String WAL.Boundary.ReopenImage (PackedTable × UInt64 × Nat)) :
    EStateM IO.Error LockOwners ((PackedTable × UInt64 × Nat) × WAL.Boundary.ReopenImage) :=
  runOpen directory descriptor acquired (match recovery with
    | .ok installed after => .ok (installed, after)
    | .error error _ => .error (cause error)) unlock

/-- Interpret native reads over the same live lock map. The comparison is the
observation of `ST.Ref.ptrEq` on the still-live session references. -/
def runGuardedRead (phase : Phase PackedTable) (sameSession : Bool) (read : PackedTable → Option α) :
    EStateM IO.Error LockOwners (Option α) :=
  withLocalHandle phase.installed (pure sameSession) none (fun state => pure (read state))

theorem runGuardedRead_eq (phase : Phase PackedTable) (sameSession : Bool)
    (read : PackedTable → Option α) (owners : LockOwners) :
    runGuardedRead phase sameSession read owners = match readWithHandle phase sameSession read with
      | .ok value => .ok value owners
      | .error cause => .error cause owners := by
  cases phase <;> cases sameSession <;> rfl

private theorem successfulClose_phase {directory : DiskDirectory} {descriptor : Nat} {unlock : UnlockReport}
    {before after : LockSession PackedTable}
    (closed : runClose directory descriptor unlock before = .ok () after) : after.phase = .closed := by
  by_cases prior : before.phase = .closed
  · unfold runClose at closed
    rw [prior] at closed
    have same : before = after := (EStateM.Result.ok.inj closed).2
    exact same ▸ prior
  · rw [runClose_open prior unlock] at closed
    cases unlock with
    | success => cases closed; rfl
    | failure => contradiction

/-- A live handle's old session reports closed after a successful close.
When a separately opened session gets a different live token, the same
snapshot handle is foreign there, even if the local pin number was reused. -/
theorem runGuardedRead_afterCloseAndReopen {directory : DiskDirectory} {descriptor : Nat}
    {unlock : UnlockReport} {before after : LockSession PackedTable}
    (closed : runClose directory descriptor unlock before = .ok () after)
    (table : PackedTable) (newOwners : LockOwners) (oldComparison : Bool)
    {newComparison : Bool} {oldToken newToken : Nat}
    (compared : newComparison = decide (oldToken = newToken)) (freshToken : oldToken ≠ newToken)
    (read : PackedTable → Option α) :
    runGuardedRead after.phase oldComparison read after.owners =
      .error (IO.userError "database is closed") after.owners ∧
    runGuardedRead (.ready table) newComparison read newOwners = .ok none newOwners := by
  refine ⟨?_, ?_⟩
  · rw [successfulClose_phase closed]
    rfl
  · rw [runGuardedRead_eq, readWithHandle_foreign table read compared freshToken]

end Alvoki.Storage.DiskSession

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotPin SnapshotTable)

private theorem observedCheckpointGeneration {fixed : FixedMarkedCheckpoint}
    {durable : CheckpointPublication.RunFiles} {manifest : Option ByteArray} {generation : UInt64}
    (sameFiles : durable = fixed.image.durable) (selected : manifest = fixed.manifest)
    (reads : CheckpointFileReads durable manifest) {loaded : Option (PackedTable × UInt64)}
    (reported : reads.result = .ok loaded)
    (expected : ((fixed.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
      (·.getD 0) : Except String UInt64) = .ok generation) :
    (loaded.getD (.empty, 0)).2 = generation := by
  subst durable
  subst manifest
  have installed := fixed.written.loaded_generation fixed.accepted reads reported
  exact Except.ok.inj (installed.symm.trans expected)

/-- On a fixed-checkpoint reopen of an already settled writer, the native
shared open's observed table, generation and WAL length give the exact ready
boundary. File observations use the stable locked namespace contract. -/
theorem ObservedMarkedState.Valid.reopenSettledFromSharedOpen {state : ObservedMarkedState}
    (valid : state.Valid) {before after : ReopenImage}
    (attempts : MarkedReopenAttempts state.writer.image before)
    (checkpointReads : CheckpointFileReads state.durable before.directory.active.manifest)
    (walReads : MarkedWalReads before) {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    {table : PackedTable} {generation : UInt64} {walBytes : Nat} {writer : MarkedWriterState}
    (opened : runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before =
      .ok (table, generation, walBytes) after)
    (observed : MarkedWriterState.observeReopen table after = some writer) :
    (⟨writer, generation, state.durable⟩ : ObservedMarkedState).Valid ∧
      writer.history = state.writer.history ∧ generation = state.generation ∧
      walBytes = writer.walBytes ∧ writer.table.pins.active = [] := by
  obtain ⟨fixed, sameFiles, represented⟩ := valid
  have fits : (WAL.encode state.writer.history).size < UInt64.size :=
    represented.ready.length ▸ represented.ready.fits
  have exactPair := (attempts.visible_of_settled represented.ready.settled fits).1
  have marked : before.directory.active.walBoundary ≠ none := by
    rw [congrArg DirectoryPublication.Bindings.walBoundary exactPair]
    exact Option.some_ne_none _
  have visible : before.directory.active.manifest = fixed.manifest :=
    congrArg DirectoryPublication.Bindings.manifest exactPair
  let image : CheckpointPublication.Image := ⟨before.directory.project .manifest, state.durable⟩
  obtain ⟨loaded, _, reported, _, _, installed, _⟩ :=
    walReads.runSharedMarkedOpen_success (image := image) marked checkpointReads opened
  have generationEq := installed.trans
    (observedCheckpointGeneration sameFiles.symm visible checkpointReads reported represented.generationMatches)
  obtain ⟨_, _, _, _, _, bytes⟩ :=
    walReads.runSharedMarkedOpen_installedWal (image := image) marked checkpointReads opened
  have step : MarkedSessionStep state.durable state.writer ⟨[], none⟩ writer :=
    .clean .start (MarkedSessionOpen.ofSharedOpen attempts marked checkpointReads walReads opened) observed
  obtain ⟨suffix, ready, extended, retained, fresh⟩ :=
    ObservedMarkedState.Valid.sessionStep ⟨fixed, sameFiles, represented⟩ step
  have noWrites : suffix = [] := by
    rcases retained with empty | ⟨_, impossible, _⟩
    · exact empty
    · contradiction
  refine ⟨?_, by simpa only [noWrites, List.append_nil] using extended, generationEq, bytes writer observed, fresh⟩
  rw [generationEq]
  exact ready

/-- A successful locked reopen yields the valid ready boundary and ownership
under the stable Linux lock-object and read observation contracts. A live
open-file description retains the lock passed to the native installer. -/
theorem ObservedMarkedState.Valid.reopenSettledWithLock {state : ObservedMarkedState}
    (valid : state.Valid) {before after : ReopenImage}
    (attempts : MarkedReopenAttempts state.writer.image before)
    (checkpointReads : CheckpointFileReads state.durable before.directory.active.manifest)
    (walReads : MarkedWalReads before) {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    {directory : DiskDirectory} {descriptor : Nat} {acquired : Except IO.Error Bool}
    {unlock : DiskSession.UnlockReport} {cause : String → IO.Error}
    {owners installedOwners : DiskSession.LockOwners}
    (contract : DiskSession.TryLockObserves owners directory acquired)
    {table : PackedTable} {generation : UInt64} {walBytes : Nat} {writer : MarkedWriterState}
    (opened : DiskSession.runLockedMarkedOpen directory descriptor acquired unlock cause
      (runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before) owners =
        .ok ((table, generation, walBytes), after) installedOwners)
    (observed : MarkedWriterState.observeReopen table after = some writer) :
    installedOwners.Owns directory descriptor ∧
      (⟨writer, generation, state.durable⟩ : ObservedMarkedState).Valid ∧
      writer.history = state.writer.history ∧ generation = state.generation ∧
      walBytes = writer.walBytes ∧ writer.table.pins.active = [] := by
  unfold DiskSession.runLockedMarkedOpen at opened
  obtain ⟨_, owns, recovered, _⟩ := DiskSession.runOpen_success contract opened
  split at recovered
  · rename_i actual actualAfter shared
    cases Except.ok.inj recovered
    exact ⟨owns, valid.reopenSettledFromSharedOpen attempts checkpointReads walReads shared observed⟩
  · contradiction

/-- A ready local pin reads its canonical WAL snapshot through the shared
guard. The lock map is preserved. Reference identity and the ready phase
are observations of the still-live native session. -/
theorem ObservedMarkedState.Valid.guardedPinnedReads_preserveLocks {state : ObservedMarkedState}
    (valid : state.Valid) {reference : SnapshotTable UInt64}
    (replayed : SnapshotWalReplay .empty state.writer.history reference)
    {pin : SnapshotPin} (active : pin ∈ state.writer.table.pins.active)
    (owners : DiskSession.LockOwners) {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) (localHandle : issuer = current) :
    (∀ key, DiskSession.runGuardedRead (.ready state.writer.table) sameSession
      (fun table => table.lookup pin.handle key) owners =
        .ok (some (reference.table.lookup key pin.sequence)) owners) ∧
    ∀ start stop, DiskSession.runGuardedRead (.ready state.writer.table) sameSession
      (fun table => table.range pin.handle start stop) owners =
        .ok (some (reference.table.range start stop pin.sequence)) owners := by
  obtain ⟨lookup, range⟩ := valid.guardedPinnedReads replayed active compared localHandle
  exact ⟨fun key => by rw [DiskSession.runGuardedRead_eq, lookup],
    fun start stop => by rw [DiskSession.runGuardedRead_eq, range]⟩

end Alvoki.WAL.Boundary
