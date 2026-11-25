import Alvoki.Storage.Disk.SegmentedDatabaseTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

private theorem SegmentedCheckpointReport.Valid.reachedRunWrite
    {directory : DiskDirectory} {before : SegmentedWriterState} {checkpoint : SegmentedCheckpointReport directory before}
    (observed : checkpoint.Valid) {index : Nat} {payload : ByteArray}
    (atIndex : (checkpoint.table.runs.map (·.run.bytes))[index]? = some payload) :
    ∃ done todo start finish,
      CheckpointPublication.steps checkpoint.table.runs.length = done ++ .writeRun index :: todo ∧
      (done.forM checkpoint.perform) 0 = .ok () start ∧
      checkpoint.writeRun (directory.file (.run (SegmentedCheckpointReport.generation before) index)) payload start =
        .ok () finish := by
  have within : index < checkpoint.table.runs.length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp atIndex).choose
  have member : .writeRun index ∈ CheckpointPublication.steps checkpoint.table.runs.length := by
    unfold CheckpointPublication.steps CheckpointPublication.runSteps
    apply List.mem_append_left
    apply List.mem_append_left
    change CheckpointPublication.Step.writeRun index ∈
      (List.range checkpoint.table.runs.length).flatMap
        (fun i => [CheckpointPublication.Step.writeRun i, CheckpointPublication.Step.syncRun i])
    exact List.mem_flatMap.mpr ⟨index, List.mem_range.mpr within, List.mem_cons_self⟩
  have writes : checkpoint.perform (.writeRun index) =
      checkpoint.writeRun (directory.file (.run (SegmentedCheckpointReport.generation before) index)) payload := by
    rw [List.getElem?_map] at atIndex
    cases found : checkpoint.table.runs[index]? with
    | none => simp [found] at atIndex
    | some run =>
      have bytes := Option.some.inj (by simpa only [found, Option.map_some] using atIndex)
      simp [SegmentedCheckpointReport.perform, performCheckpointFileStep, List.getElem?_toArray, found, bytes, pure_bind]
  obtain ⟨done, todo, order⟩ := List.append_of_mem member
  have returned := observed.succeeded
  rw [CheckpointPublication.run, order, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at returned
  simp only [Bind.bind, EStateM.bind] at returned
  cases reached : (done.forM checkpoint.perform) 0 with
  | error cause start => simp [reached] at returned
  | ok _ start =>
    simp only [reached, List.forM, Bind.bind, EStateM.bind, writes] at returned
    cases written : checkpoint.writeRun (directory.file (.run (SegmentedCheckpointReport.generation before) index))
        payload start with
    | error cause finish => simp [written] at returned
    | ok result finish => cases result; exact ⟨done, todo, start, finish, order, reached, written⟩

/-- An explicit run rewrite and successful checkpoint, followed by a healthy
cached close and reopen, load the rewritten run's exact bytes at its original
index. The selected manifest already covers the complete WAL history.
The exact published and reread bytes are bounded by newer rows and one floor
anchor per key. The retention floor is preserved, and every earlier active
pin can be reacquired at the same sequence. -/
theorem SegmentedDatabaseTrace.retainRunVersionsCheckpointCloseCached
    {directory initialDescriptor initial allowCollection log writer nextDescriptor before published}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    {index : Nat} {table : PackedTable} (retained : before.installed.table.retainRunVersions index = some table)
    (checkpoint : SegmentedCheckpointReport directory (before.withTable table))
    (observed : checkpoint.Valid) (publication : checkpoint.Installs published)
    (reopen : SegmentedCleanReopenReport directory published writer nextDescriptor) (reopening : reopen.Valid)
    (sizes : SizedCheckpointRunReports directory reopen.raw.reports published.wal.directory.active.manifest
      published.published.durable)
    (cached : CachedWalFileReports directory reopen.raw.reports published.wal published.target.range.watermark ByteArray.empty) :
    ∃ after session final, ∃ source output : Compaction.CheckedRun,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], none⟩]) nextDescriptor after ∧
      before.installed.table.runs[index]? = some source ∧
      output.history = source.history.retain before.installed.table.pins.floor ∧
      output.run.bytes.size ≤
        16 + 32 * Compaction.Model.retentionRowBound source.history.rows before.installed.table.pins.floor ∧
      let generation := SegmentedCheckpointReport.generation before
      runOpenWithInstallation directory nextDescriptor reopen.nextRef (.ok true) reopen.unlock
        (reopen.raw.reopenCached sizes cached reopen.removeFile reopen.write reopen.sync reopen.renameFile)
        (SegmentedCleanReopenReport.released directory published) = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners ∧
      after.installed.generation = generation ∧ after.history = before.history ∧
      (∃ done todo start finish,
        CheckpointPublication.steps checkpoint.table.runs.length = done ++ .writeRun index :: todo ∧
        (done.forM checkpoint.perform) 0 = .ok () start ∧
        checkpoint.writeRun (directory.file (.run generation index)) output.run.bytes start = .ok () finish) ∧
      after.published.durable generation index = some output.run.bytes ∧
      sizes.readPrefix (directory.file (.run generation index)) output.run.bytes.size = .ok output.run.bytes ∧
      (after.installed.table.runs.map (·.run.bytes))[index]? = some output.run.bytes ∧
      after.installed.table.pins.floor = before.installed.table.pins.floor ∧
      ∀ oldPin ∈ before.installed.table.pins.active,
        ∃ newPin pinned, after.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
          newPin.sequence = oldPin.sequence ∧
          (∀ key, pinned.lookup newPin.handle key = before.installed.table.lookup oldPin.handle key) ∧
          ∀ start stop, pinned.range newPin.handle start stop = before.installed.table.range oldPin.handle start stop := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨publishedReady, publishedHistory, source, output, sourceAt, retainedRows, durable⟩ :=
    publication.afterRunRetention retained ready observed
  have stretch : SegmentedWriterTrace directory writer before [] 1 published :=
    .checkpoint (.table .empty (.retainRunVersions retained)) checkpoint observed publication
  have wrote := SegmentedDatabaseTrace.writes prior stretch
  obtain ⟨after, session, final, endpoint, ran, phase, files, owners⟩ :=
    reopen.installsRetainedCached reopening publishedReady sizes cached
  have trace := SegmentedDatabaseTrace.close wrote reopen reopening endpoint
  obtain ⟨base, selected, sameData, baseClock⟩ := publication.restored
  have replayed := endpoint.replay
  rw [selected] at replayed
  change recoverSelected base (WAL.encode published.history) = .ok after.installed.table at replayed
  have fullyCovered : recoverSelected base (WAL.encode published.history) = .ok base := by
    simpa only [List.append_nil, replay, List.foldlM_nil, Pure.pure, Except.pure] using
      recoverSelected_encoded base published.history [] (by simpa using publishedReady.resumed.ordered) baseClock.symm
  have exactTable : after.installed.table = base := Except.ok.inj (replayed.symm.trans fullyCovered)
  have runAt := publication.runs index
  change published.published.durable (SegmentedCheckpointReport.generation before) index =
    (checkpoint.table.runs.map (·.run.bytes))[index]? at runAt
  have emitted := observed.reachedRunWrite (runAt.symm.trans durable)
  have loadedRun : (after.installed.table.runs.map (·.run.bytes))[index]? = some output.run.bytes := by
    rw [exactTable, sameData.runs, ← runAt]
    exact durable
  have manifest : published.wal.directory.active.manifest = some checkpoint.manifest := by
    have projected := congrArg Publication.Image.active publishedReady.manifestFiles
    change published.published.manifest.active = published.files.directory.active.manifest at projected
    rw [publishedReady.directoryFiles, publication.settled] at projected
    exact projected.symm
  have indexBound : index < checkpoint.table.runs.length := by
    have present := runAt.symm.trans durable
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp present).choose
  let generation := SegmentedCheckpointReport.generation before
  have declared : index < (Manifest.IntegrityCheckpoint.fromRuns
      (checkpointHeader checkpoint.table generation) checkpoint.plan.files).header.runCount.toNat := by
    simpa [Manifest.IntegrityCheckpoint.fromRuns, checkpointHeader, UInt64.toNat_ofNat_of_lt' observed.runCountFits]
      using indexBound
  obtain ⟨_, _, _, _, readExact⟩ := sizes.runs checkpoint.manifest _ manifest publication.decodedManifest
    index declared output.run.bytes durable
  have afterReady := endpoint.preservesRetained reopening publishedReady
  have history : after.history = before.history := endpoint.history.trans publishedHistory
  have gen : after.installed.generation = generation := endpoint.generation.trans
    (congrArg Installed.generation publication.installed)
  have retainedFloor : table.pins.floor = before.installed.table.pins.floor :=
    congrArg Sequential.SnapshotPins.floor (PackedTable.retainRunVersions_spec retained).2.2.1
  have flushedFloor : checkpoint.table.pins.floor = table.pins.floor := by
    have flushed := observed.flushed
    unfold flushForCheckpoint at flushed
    split at flushed
    · exact congrArg (fun table : PackedTable => table.pins.floor) (Except.ok.inj flushed).symm
    · exact congrArg Sequential.SnapshotPins.floor (PackedTable.flush_spec flushed).2.2.1
  have floor : after.installed.table.pins.floor = before.installed.table.pins.floor :=
    (congrArg (fun table : PackedTable => table.pins.floor) exactTable).trans
      (sameData.floor.trans (flushedFloor.trans retainedFloor))
  have kept : after.published.durable generation index = some output.run.bytes := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := endpoint.openEffect
    exact durable
  have bytes := Compaction.CheckedRun.byteSize_le_of_retainedHistory retainedRows
  refine ⟨after, session, final, source, output, trace, sourceAt, retainedRows, bytes, ran, phase, files, owners, gen,
    history, emitted, kept, readExact, loadedRun, floor, ?_⟩
  intro oldPin active
  exact ready.reacquireReadsStable afterReady (suffix := []) (by simpa using history) active
    (floor.symm ▸ before.installed.table.pins.safe oldPin active)

end Alvoki.Storage.DiskSession
