import Alvoki.Storage.Disk.NativeReadyReadPrefix
import Alvoki.Storage.Disk.CheckpointCompletionHeldReopen
import Alvoki.Storage.Disk.Checkpoint.PrimitiveDispatch

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open Alvoki.Sequential (SnapshotTable)

private abbrev CheckpointState (image : Type) := CensusDirectoryCache × image
private abbrev CheckpointWrite (image : Type) := FilePath → ByteArray → EStateM IO.Error image CheckpointOpenHandle

/-- One guarded run or fresh staged-manifest write returns its actual
handle, whose file sync uses it before the observed temporary release.
The tracked inventory has no other allocations or drops in this pair. -/
structure CompletedCheckpointTemporaryFile {image : Type}
    (descriptors : image → DescriptorInventory) (calls : CheckpointCacheCalls CheckpointOpenHandle image)
    (write : CheckpointWrite image) (path : FilePath) (bytes : ByteArray) (before after : image) where
  handle : CheckpointOpenHandle
  flushed : image
  wrote : write path bytes before = .ok handle flushed
  synced : calls.fsync handle flushed = .ok () after
  free : ∀ old ∈ (descriptors before).slots, old.address ≠ handle.2.1.address
  fresh : (descriptors before).references handle.2.1.description = []
  allocated : handle.1 = (descriptors before).insert handle.2.1 free
  atFileSync : descriptors flushed = handle.1
  drop : LockReferenceDrop
  close : drop = handle.2.1.closeEvent
  afterClose : descriptors after = (descriptors flushed).afterDrops [drop]

namespace CompletedCheckpointTemporaryFile

variable {image : Type} {descriptors : image → DescriptorInventory}
  {calls : CheckpointCacheCalls CheckpointOpenHandle image} {write : CheckpointWrite image}
  {path : FilePath} {bytes : ByteArray} {before after : image}

/-- Allocation and release concern the same raw slot used by the file
sync. No slot from the entry inventory is removed by that release. -/
theorem keepsCensus (seen : CompletedCheckpointTemporaryFile descriptors calls write path bytes before after) :
    descriptors after = descriptors before ∧ seen.handle.2.1 ∈ (descriptors seen.flushed).slots ∧
    (descriptors after).references seen.handle.2.1.description = [] := by
  have removed := DescriptorInventory.insert_thenClose (descriptors before) seen.handle.2.1 seen.free []
  simp only [List.nil_append] at removed
  have survives : ∀ slot ∈ (descriptors before).slots, (!seen.handle.2.1.closeEvent.removes slot.reference) = true := by
    intro slot live
    cases removed : seen.handle.2.1.closeEvent.removes slot.reference with
    | false => rfl
    | true =>
      exfalso
      apply seen.free slot live
      simpa [DescriptorSlot.address, DescriptorSlot.closeEvent, LockReferenceDrop.removes,
        Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using removed
  have entry : (descriptors before).afterDrops [seen.handle.2.1.closeEvent] = descriptors before := by
    cases known : descriptors before with
    | mk slots distinct inode =>
      simp only [DescriptorInventory.afterDrops, List.all_cons, List.all_nil, Bool.and_true,
        DescriptorInventory.mk.injEq, and_true]
      exact List.filter_eq_self.mpr (by simpa only [known] using survives)
  have after := seen.afterClose.trans (by rw [seen.atFileSync, seen.close, seen.allocated, removed, entry])
  have live : seen.handle.2.1 ∈ (descriptors seen.flushed).slots := by
    rw [seen.atFileSync, seen.allocated]
    exact List.mem_cons_self
  exact ⟨after, live, after.symm ▸ seen.fresh⟩

/-- The file barrier consumes the pending handle created by the preceding
write. With an empty pending list at entry the whole cache is preserved. -/
theorem returns (seen : CompletedCheckpointTemporaryFile descriptors calls write path bytes before after)
    (directory : DiskDirectory) (different : path ≠ directory.path) (cache : CensusDirectoryCache)
    (pending : cache.pending = []) :
    ((stageFreshWithCache path bytes write >>= fun _ => (calls.callbacks directory).sync #[path])
      (cache, before)) = .ok () (cache, after) := by
  have consumed : cache.consume path = cache := by
    cases cache
    simp_all [Cache.consume]
  have synced : sync directory.path calls.openRead calls.fsync path (cache.remember path seen.handle, seen.flushed) =
      .ok () (cache, after) := by
    rw [syncRemembered different seen.handle calls.openRead calls.fsync seen.flushed]
    simp only [seen.synced, consumed]
  simp only [CheckpointCacheCalls.callbacks, Bind.bind, EStateM.bind, stageFreshWithCache, seen.wrote]
  rw [SyncPathGroup.run_single, synced]

end CompletedCheckpointTemporaryFile

/-- The native cache and temporary descriptor observations common to a
checkpoint that has completed its manifest rename. -/
structure NativeCheckpointPrefix {image : Type} (state : NativeReadyState)
    {attempt : SegmentedCheckpointReport state.session.directory state.writer}
    {callbacks : CheckpointFileCallbacks (CheckpointState image)}
    (observed : ReturnedCheckpointPrefix (callbacks.perform state.session.directory attempt.prepared attempt.manifest)
      attempt.table.runs.length) where
  primitives : CheckpointPrimitiveCalls CheckpointOpenHandle image
  callbacks : callbacks = primitives.cached.callbacks state.session.directory
  descriptors : image → DescriptorInventory
  initialCache : (observed.atRun 0).1 = state.cache
  initialCensus : descriptors (observed.atRun 0).2 = state.census
  capturedDirectory : DescriptorInventory
  directoryCached : state.cache.directory = some (capturedDirectory, state.directorySlot, 0)
  capturedInode : capturedDirectory.inode state.directorySlot.description = state.census.inode state.directorySlot.description
  pending : state.cache.pending = []
  runLifetime : ∀ index < attempt.table.runs.length,
    ∃ run : Compaction.CheckedRun, attempt.table.runs.toArray[index]? = some run ∧
      Nonempty (CompletedCheckpointTemporaryFile descriptors primitives.cached primitives.cached.writeRun
        (state.session.directory.file (.run attempt.prepared.generation index)) run.run.bytes
        (observed.atRun index).2 (observed.atRun (index + 1)).2)
  runsDirectory : descriptors observed.runsSettled.2 = descriptors (observed.atRun attempt.table.runs.length).2
  manifestLifetime : CompletedCheckpointTemporaryFile descriptors primitives.cached primitives.cached.writeStaged
    (state.session.directory.file .stagedManifest) attempt.manifest observed.runsSettled.2 observed.stagedSynced.2
  rename : descriptors observed.renamed.2 = descriptors observed.stagedSynced.2

namespace NativeCheckpointPrefix

variable {image : Type} {state : NativeReadyState}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {callbacks : CheckpointFileCallbacks (CheckpointState image)}
  {observed : ReturnedCheckpointPrefix (callbacks.perform state.session.directory attempt.prepared attempt.manifest)
    attempt.table.runs.length}

private theorem runCache (report : NativeCheckpointPrefix state observed) {index : Nat}
    (within : index < attempt.table.runs.length) (pending : (observed.atRun index).1.pending = []) :
    (observed.atRun (index + 1)).1 = (observed.atRun index).1 := by
  obtain ⟨run, found, ⟨seen⟩⟩ := report.runLifetime index within
  change attempt.prepared.table.runs.toArray[index]? = some run at found
  have ran := seen.returns state.session.directory (file_ne_directory _ (.run attempt.prepared.generation index))
    (observed.atRun index).1 pending
  have exact : (callbacks.perform state.session.directory attempt.prepared attempt.manifest (.writeRun index) >>=
        fun _ => callbacks.perform state.session.directory attempt.prepared attempt.manifest (.syncRun index))
      (observed.atRun index) = .ok () ((observed.atRun index).1, (observed.atRun (index + 1)).2) := by
    simpa only [report.callbacks, CheckpointFileCallbacks.perform, performCheckpointFileStep, found, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, CheckpointCacheCalls.callbacks] using ran
  have same := (EStateM.Result.ok.inj ((observed.pairs index within).symm.trans exact)).2
  simpa only using congrArg (Prod.fst : CheckpointState image → CensusDirectoryCache) same

theorem beforeRunsDirectory (report : NativeCheckpointPrefix state observed) (index : Nat)
    (within : index ≤ attempt.table.runs.length) :
    (observed.atRun index).1 = state.cache ∧ report.descriptors (observed.atRun index).2 = state.census := by
  induction index with
  | zero => exact ⟨report.initialCache, report.initialCensus⟩
  | succ index earlier =>
    have within' : index < attempt.table.runs.length := within
    obtain ⟨cache, census⟩ := earlier (Nat.le_of_lt within')
    obtain ⟨_, _, ⟨seen⟩⟩ := report.runLifetime index within'
    have pending : (observed.atRun index).1.pending = [] :=
      (congrArg Cache.pending cache).trans report.pending
    exact ⟨(report.runCache within' pending).trans cache, seen.keepsCensus.1.trans census⟩

theorem callbackCache (report : NativeCheckpointPrefix state observed)
    {before after : CheckpointState image} (step : CheckpointPublication.Step)
    (returned : callbacks.perform state.session.directory attempt.prepared attempt.manifest step before = .ok () after)
    (unchanged : match step with
      | .syncRunsDirectory | .manifest .syncDirectory | .manifest .renameStaged => True
      | _ => False) : after.1 = before.1 := by
  have cache := report.primitives.cached.stepCache state.session.directory attempt.prepared attempt.manifest step before.1 before.2
  have effect : report.primitives.cached.perform state.session.directory attempt.prepared attempt.manifest step before = .ok () after := by
    simpa only [report.callbacks] using returned
  change (reachedState (report.primitives.cached.perform state.session.directory attempt.prepared attempt.manifest step before)).1 = _ at cache
  rw [effect] at cache
  cases step with
  | syncRunsDirectory => exact cache
  | manifest step => cases step <;> first | exact cache | contradiction
  | writeRun | syncRun => contradiction

private theorem manifestCache (report : NativeCheckpointPrefix state observed)
    (pending : observed.runsSettled.1.pending = []) :
    observed.stagedSynced.1 = observed.runsSettled.1 := by
  let perform := callbacks.perform state.session.directory attempt.prepared attempt.manifest
  have returned : (perform (.manifest .writeStaged) >>= fun _ => perform (.manifest .syncStaged))
      observed.runsSettled = .ok () observed.stagedSynced := by
    simp only [perform, Bind.bind, EStateM.bind, observed.stageManifest, observed.syncManifest]
  have exact := report.manifestLifetime.returns state.session.directory (file_ne_directory _ .stagedManifest)
    observed.runsSettled.1 pending
  rw [show perform = report.primitives.cached.perform state.session.directory attempt.prepared attempt.manifest by
    simp only [perform, report.callbacks]] at returned
  have same : (report.primitives.cached.perform state.session.directory attempt.prepared attempt.manifest (.manifest .writeStaged) >>=
        fun _ => report.primitives.cached.perform state.session.directory attempt.prepared attempt.manifest (.manifest .syncStaged))
      observed.runsSettled = .ok () (observed.runsSettled.1, observed.stagedSynced.2) := by
    exact exact
  have pair := (EStateM.Result.ok.inj (returned.symm.trans same)).2
  simpa only using congrArg (Prod.fst : CheckpointState image → CensusDirectoryCache) pair

theorem beforeFinalDirectory (report : NativeCheckpointPrefix state observed) :
    observed.renamed.1 = state.cache ∧ report.descriptors observed.renamed.2 = state.census := by
  obtain ⟨cache, census⟩ := report.beforeRunsDirectory _ (Nat.le_refl _)
  have runDir := report.callbackCache _ observed.syncRunsDirectory trivial
  have pending := (congrArg Cache.pending (runDir.trans cache)).trans report.pending
  have manifest := report.manifestCache pending
  have rename := report.callbackCache _ observed.renameManifest trivial
  exact ⟨rename.trans (manifest.trans (runDir.trans cache)), report.rename.trans
    (report.manifestLifetime.keepsCensus.1.trans (report.runsDirectory.trans census))⟩

theorem directoryFsync (report : NativeCheckpointPrefix state observed)
    {before after : CheckpointState image} (cached : before.1 = state.cache)
    (returned : callbacks.sync #[state.session.directory.path] before = .ok () after) :
    report.primitives.fsync (report.capturedDirectory, state.directorySlot, 0) before.2 = .ok () after.2 := by
  have actual : SyncPathGroup.run (sync state.session.directory.path report.primitives.openRead report.primitives.fsync)
      #[state.session.directory.path] before = .ok () after := by
    simpa only [report.callbacks, CheckpointCacheCalls.callbacks, CheckpointPrimitiveCalls.cached] using returned
  obtain ⟨cache, files⟩ := before
  rw [SyncPathGroup.run_single] at actual
  simp only [sync, Cache.resolve, beq_self_eq_true, ↓reduceIte] at actual
  change cache = state.cache at cached
  rw [cached, report.directoryCached] at actual
  cases result : report.primitives.fsync (report.capturedDirectory, state.directorySlot, 0) files with
  | error _ reached => simp [result, withCache] at actual
  | ok value reached =>
    cases value
    simp only [result, withCache, EStateM.Result.ok.injEq, true_and] at actual
    exact congrArg (EStateM.Result.ok ()) (congrArg (Prod.snd : CheckpointState image → image) actual)

end NativeCheckpointPrefix

/-- The successful final barrier extends the common returned prefix.
The file-only completion report ties the actual published bytes to the
ready writer. -/
structure NativeReadyCheckpoint {image : Type} (state : NativeReadyState)
    {attempt : SegmentedCheckpointReport state.session.directory state.writer}
    (reports : CheckpointCompletionReports (CheckpointState image) attempt)
    extends NativeCheckpointPrefix state reports.observed.toReturnedCheckpointPrefix where
  physical : reports.CloseFiles
  bindings : image → FilePath → Option Nat
  heldBindings : ∀ raw ∈ [(reports.observed.atRun attempt.table.runs.length).2,
                            reports.observed.renamed.2, reports.observed.completed.2],
    bindings raw state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  finalDirectory : descriptors reports.observed.completed.2 = descriptors reports.observed.renamed.2

namespace NativeReadyCheckpoint

variable {image : Type} {state : NativeReadyState}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CheckpointState image) attempt}

/-- The paired file dispatch and its reported allocation and finalizer
preserve the original ready cache and census through checkpoint return. -/
theorem preservesCustody (report : NativeReadyCheckpoint state reports) :
    reports.observed.completed.1 = state.cache ∧ report.descriptors reports.observed.completed.2 = state.census := by
  obtain ⟨cache, census⟩ := report.toNativeCheckpointPrefix.beforeFinalDirectory
  have final := report.toNativeCheckpointPrefix.callbackCache _ reports.observed.syncManifestDirectory trivial
  exact ⟨final.trans cache, report.finalDirectory.trans census⟩

/-- Both native directory barriers use the captured descriptor for the
same held root. The reported slot is live in the census reached by the
temporary-file pairs, and the canonical `LOCK` still names the writer's inode. -/
theorem directoryBarriers (report : NativeReadyCheckpoint state reports) (valid : state.Valid) :
    let handle := (report.capturedDirectory, state.directorySlot, 0)
    let beforeRuns := (reports.observed.atRun attempt.table.runs.length).2
    let beforeManifest := reports.observed.renamed.2
    report.primitives.fsync handle beforeRuns = .ok () reports.observed.runsSettled.2 ∧
    report.primitives.fsync handle beforeManifest = .ok () reports.observed.completed.2 ∧
    ∀ raw ∈ [beforeRuns, beforeManifest, reports.observed.completed.2],
      report.descriptors raw = state.census ∧
      state.directorySlot ∈ (report.descriptors raw).slots ∧ state.owner ∈ (report.descriptors raw).slots ∧
      report.bindings raw state.session.directory.path = some (handle.1.inode state.directorySlot.description) ∧
      report.bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  dsimp only
  obtain ⟨runCache, runCensus⟩ := report.toNativeCheckpointPrefix.beforeRunsDirectory _ (Nat.le_refl _)
  obtain ⟨manifestCache, manifestCensus⟩ := report.toNativeCheckpointPrefix.beforeFinalDirectory
  refine ⟨report.toNativeCheckpointPrefix.directoryFsync runCache reports.observed.syncRunsDirectory,
    report.toNativeCheckpointPrefix.directoryFsync manifestCache reports.observed.syncManifestDirectory, ?_⟩
  intro raw member
  have custody : report.descriptors raw = state.census := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact runCensus
    · exact manifestCensus
    · exact report.preservesCustody.2
  obtain ⟨path, lock⟩ := report.heldBindings raw member
  exact ⟨custody, custody.symm ▸ valid.directoryLive, custody.symm ▸ valid.ownerLive,
    path.trans (congrArg some report.capturedInode.symm), lock⟩

/-- Execute the native checkpoint schedule with the exact cache and
owner read from the ready state. The file observations supply the raw
entry image and prove its projection to that writer's files. -/
noncomputable def run (report : NativeReadyCheckpoint state reports) :=
  runCheckpointWithEffects (report.primitives.cached.perform state.session.directory)
    (state.session.phase, ⟨(state.cache, (reports.observed.atRun 0).2), state.files.owners⟩)

def next (report : NativeReadyCheckpoint state reports) (writer : SegmentedWriterState) : NativeReadyState :=
  { state with
    session := { state.session with phase := .ready writer.installed }
    writer
    census := report.descriptors reports.observed.completed.2
    cache := reports.observed.completed.1 }

/-- The exact returned state keeps the logical history and session
references. The publication evidence identifies the selected manifest
and durable run bytes in the same reached file state. -/
structure Completed (report : NativeReadyCheckpoint state reports) (writer : SegmentedWriterState) : Prop where
  returned : report.run = .ok () ((report.next writer).session.phase,
    ⟨((report.next writer).cache, reports.observed.completed.2), (report.next writer).files.owners⟩)
  valid : (report.next writer).Valid
  files : report.physical.files reports.observed.completed.2 = (report.next writer).files.image
  manifest : reports.manifest reports.observed.completed = .settled (some attempt.manifest)
  manifestBinding : (report.physical.files reports.observed.completed.2).directory.active.manifest = some attempt.manifest
  runs : ∀ index < attempt.table.runs.length,
    (reports.runs reports.observed.completed).guaranteed writer.installed.generation index = attempt.plan.files[index]?
  selected : SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
    (report.physical.files reports.observed.completed.2).directory.active.manifest writer.checkpoint
  installed : writer.installed = attempt.prepared
  sameHistory : writer.history = state.writer.history
  pins : writer.installed.table.pins = state.writer.installed.table.pins
  cache : (report.next writer).cache = state.cache
  census : (report.next writer).census = state.census
  owners : (report.next writer).files.owners = state.files.owners
  directory : report.bindings reports.observed.completed.2 state.session.directory.path =
    some (report.capturedDirectory.inode state.directorySlot.description)
  lock : report.bindings reports.observed.completed.2 (state.session.directory.file .lock) =
    some ((report.next writer).census.inode (report.next writer).owner.description)

/-- The successful native return and the published checkpoint selection
use one installed writer. -/
theorem completesWithPublication (report : NativeReadyCheckpoint state reports) (valid : state.Valid) :
    ∃ writer, report.Completed writer ∧ attempt.Installs writer := by
  have initialTrace : SegmentedBatchDatabaseTrace state.session.directory state.session.descriptor state.writer
      false [] state.session.descriptor state.writer := .start
  obtain ⟨writer, completed, _⟩ := initialTrace.checkpointFromObservedSteps valid.retained reports
  obtain ⟨cache, census⟩ := report.preservesCustody
  have files := completed.closeFiles report.physical valid.retained
  have ready : (report.next writer).Valid :=
    ⟨rfl, valid.owner, by simpa only [next, census] using valid.ownerLive,
      by simpa only [next, census] using valid.directoryLive, by simpa only [next, cache] using valid.captured,
      completed.retained⟩
  have returnedCustody := (report.directoryBarriers valid).2.2 reports.observed.completed.2 (by simp)
  have physicalManifest := congrArg Publication.Image.active (report.physical.manifest reports.observed.completed)
  have settledManifest := completed.manifest.trans completed.installed.settled
  have selected : SelectedIntegrityCheckpoint writer.published.durable
      (reports.manifest reports.observed.completed).active writer.checkpoint := by
    rw [completed.manifest, completed.retained.manifestFiles]
    change SelectedIntegrityCheckpoint writer.published.durable writer.files.directory.active.manifest writer.checkpoint
    rw [completed.retained.directoryFiles]
    exact completed.installed.checkpoint
  have flushed := reports.preflight.preparedFacts.1
  change (flushForCheckpoint state.writer.installed.table id : Except String PackedTable) = .ok attempt.table at flushed
  have pins : attempt.table.pins = state.writer.installed.table.pins := by
    cases empty : state.writer.installed.table.memoryIsEmpty with
    | false =>
      have flushed : state.writer.installed.table.flush = .ok attempt.table := by
        simpa [flushForCheckpoint, empty] using flushed
      exact (PackedTable.flush_spec flushed).2.2.1
    | true =>
      have same : Except.ok (ε := String) state.writer.installed.table = .ok attempt.table := by
        simpa [flushForCheckpoint, empty, Pure.pure, Except.pure] using flushed
      exact congrArg PackedTable.pins (Except.ok.inj same).symm
  refine ⟨writer, ⟨?_, ready, files, settledManifest,
    physicalManifest.trans (congrArg Publication.Image.active settledManifest), ?_, ?_,
    completed.installed.installed, completed.installed.history, ?_, cache, census, completed.installed.owners,
    returnedCustody.2.2.2.1, ?_⟩, completed.installed⟩
  · change runCheckpointWithEffects (report.primitives.cached.perform state.session.directory)
      (state.session.phase, ⟨(state.cache, (reports.observed.atRun 0).2), state.writer.owners⟩) =
        .ok () (.ready writer.installed, ⟨reports.observed.completed, writer.owners⟩)
    have initialState : (state.cache, (reports.observed.atRun 0).2) = reports.observed.atRun 0 := by
      rw [← report.initialCache]
    rw [initialState, valid.phase]
    simpa only [report.callbacks] using completed.returned
  · intro index within
    rw [completed.runs index within, completed.installed.installed]
    exact completed.installed.runs index
  · change (report.physical.files reports.observed.completed.2).directory.active.manifest = _ at physicalManifest
    rw [physicalManifest]
    exact SelectedIntegrityCheckpoint.withRunMap selected completed.selectedRuns.symm
  · rw [completed.installed.installed]
    exact pins
  · simpa only [next, census] using returnedCustody.2.2.2.2

theorem completes (report : NativeReadyCheckpoint state reports) (valid : state.Valid) :
    ∃ writer, report.Completed writer := by
  obtain ⟨writer, completed, _⟩ := report.completesWithPublication valid
  exact ⟨writer, completed⟩

end NativeReadyCheckpoint

/-- A healthy checkpoint follows an exact returned ready read prefix.
It contributes no writes to the ledger. The same WAL replay explains
recorded responses and future supported reads from the new ready table. -/
theorem NativeReadyReadPrefix.checkpoints
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    {image : Type} {attempt : SegmentedCheckpointReport state.session.directory state.writer}
    {reports : CheckpointCompletionReports (CheckpointState image) attempt}
    (reported : NativeReadyCheckpoint state reports) :
    ∃ writer, reported.Completed writer ∧ writer.history = history ∧
      InstalledClientReplay log reads history writer.installed (reported.next writer).session := by
  obtain ⟨valid, previous, reference, replayed, retained, acknowledged, submitted, observed⟩ := prior.refines
  obtain ⟨writer, completed⟩ := reported.completes valid
  have history := completed.sameHistory.trans previous
  obtain ⟨_, refined, represented⟩ := completed.valid.retained.resumed.canonical
  have guarded := (reported.next writer).session.guardedAcquireReads completed.valid.phase fun _ floor committed =>
    represented.acquireReads refined completed.valid.retained.resumed.bounds (history.symm ▸ replayed) floor committed
  exact ⟨writer, completed, history, reference, replayed, retained, acknowledged, submitted, observed, guarded⟩

end Alvoki.Storage.DiskSession
