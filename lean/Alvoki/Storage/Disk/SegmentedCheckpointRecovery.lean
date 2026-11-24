import Alvoki.Storage.Disk.CheckpointRetrySession
import Alvoki.Storage.Disk.SegmentedCheckpointStep

import Alvoki.Storage.Disk.SegmentedFailureRelease

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- One actual checkpoint dispatch failure, the release of its writer lock,
and the reached bounded reopen attempts. The final attempt supplies its
own lock and filesystem reports for the selected metadata and keeper. -/
structure SegmentedCheckpointFailure (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  checkpoint : SegmentedCheckpointReport directory before
  cause : IO.Error
  flushed : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok checkpoint.table
  generationFits : before.installed.generation.toNat + 1 < UInt64.size
  runCountFits : checkpoint.table.runs.length < UInt64.size
  encoded : encodeCheckpointIntegrityManifest checkpoint.table (SegmentedCheckpointReport.generation before) =
    .ok checkpoint.manifest
  reached : CheckpointPublication.ReachedFileReports checkpoint.report checkpoint.perform
    (CheckpointPublication.steps checkpoint.table.runs.length) 0
  failed : CheckpointPublication.run checkpoint.table.runs.length checkpoint.perform 0 = .error cause checkpoint.cut
  published : CheckpointPublication.Image
  projected : before.published.executeVersioned checkpoint.plan checkpoint.cut = some published
  release : SegmentedFailureRelease writer
  retry : LockedFileState FileImage
  attempts :
    let wal := published.segmentedCheckpointView before.wal
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨{ before.files with directory := wal.directory }, before.owners.set (directory.file .lock) none⟩ retry
  reopen : BoundedReopenAttempt
  reopenDescriptor : reopen.descriptor = descriptor
  acquired : reopen.acquired = .ok true
  acquisition : TryLockObserves retry.owners directory (.ok true)
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef
  reads : ∀ selected : CanonicalKeeperLayout retry.image before.history, selected.tail = ByteArray.empty →
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        (published.segmentedCheckpointView before.wal) retry.image.directory.active selected.range.watermark
        published.durable selected.tail,
      reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile
  settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory
  healthy : ∀ selected : CanonicalKeeperLayout retry.image before.history,
    selected.target.first = before.wal.active.first → selected.tail = ByteArray.empty →
    ∀ action prior next,
      ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile
        action prior =
        .ok () next

namespace SegmentedCheckpointFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

/-- The reached checkpoint publication error and installed endpoint of the final
bounded open. The endpoint records the manifest and ordered checkpoint
binding that the actual file reports select. -/
structure Installs (failure : SegmentedCheckpointFailure directory before writer descriptor)
    (after : SegmentedWriterState) : Prop where
  poisoned : runPreparedCheckpoint failure.checkpoint.prepared failure.checkpoint.perform
    (.ready before.installed, ⟨0, before.owners⟩) =
    .error failure.cause (.poisoned, ⟨failure.checkpoint.cut, before.owners⟩)
  released : failure.release.Observed (directory := directory)
    (.poisoned, ⟨failure.checkpoint.cut, before.owners⟩)
    ⟨failure.checkpoint.cut, before.owners.set (directory.file .lock) none⟩
  reopened : ∃ session final, failure.reopen.run directory failure.retry = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = failure.published.durable
  manifest : after.published.manifest = after.files.directory.project .manifest
  targetPair : after.target.pair = failure.retry.image.directory.active
  targetFirst : after.target.first = before.wal.active.first
  targetBytes : after.target.trimmed = before.wal.active.bytes
  checkpoint : SelectedIntegrityCheckpoint after.published.durable after.target.pair.manifest after.checkpoint
  generation : (after.installed.generation = before.installed.generation ∧
      after.target.pair.manifest = before.wal.directory.active.manifest) ∨
    (after.installed.generation = SegmentedCheckpointReport.generation before ∧
      after.target.pair.manifest = some failure.checkpoint.manifest)

private theorem checkpointRetryFiles_exact (published : CheckpointPublication.Image)
    (ready : before.Ready directory writer) :
    let wal := published.segmentedCheckpointView before.wal
    wal.checkpointReopenFiles wal.directory before.files.keeper.staged =
      { before.files with directory := wal.directory } := by
  intro wal
  have bytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have visible := ready.resumed.ready.keeper
  have stable := ready.resumed.ready.keeperDurable
  rw [bytes] at visible stable
  have keeper : before.files.keeper =
      { Publication.Image.settled (some before.wal.active.bytes) with staged := before.files.keeper.staged } := by
    change before.files.keeper =
      ⟨some before.wal.active.bytes, [some before.wal.active.bytes], before.files.keeper.staged⟩
    rw [← stable, ← visible]
  obtain ⟨visible, stable⟩ := ready.resumed.ready.pruned
  have later : before.files.later = .settled [] := by
    change before.files.later = ⟨[], [[]]⟩
    rw [← stable, ← visible]
  change (⟨wal.directory, (before.wal.checkpointReopenFiles before.wal.directory none).kept,
      { Publication.Image.settled (some before.wal.active.bytes) with staged := before.files.keeper.staged },
      .settled []⟩ : FileImage) =
    ⟨wal.directory, before.files.kept, before.files.keeper, before.files.later⟩
  rw [← ready.sealedFiles, ← keeper, ← later]

/-- Recover the exact ready writer through the reported release and any
finite delay of bounded-open failures, reference drops, and power losses.
The complete acknowledged WAL and the keeper remain in place. -/
theorem installs (failure : SegmentedCheckpointFailure directory before writer descriptor)
    (ready : before.Ready directory writer) :
    ∃ after, failure.Installs after ∧ after.Ready directory descriptor := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have append := ready.appendInput
  have projects : before.published.manifest = before.wal.directory.project .manifest := by
    rw [← ready.directoryFiles]
    exact ready.manifestFiles
  obtain ⟨_, _, _, count, _, _, counted⟩ := DirectoryPublication.Bindings.walRange_accounting append.range
  have bytes : (WAL.encode before.history).size = count.toNat := by
    rw [counted, WAL.encode_size, Nat.mul_comm]
  have walFits : (WAL.encode before.history).size < UInt64.size := bytes.symm ▸ count.toNat_lt_size
  have runBytesFit : ∀ bytes ∈ failure.checkpoint.table.runs.map (·.run.bytes), bytes.size < UInt64.size := by
    by_cases bounded : (failure.checkpoint.table.runs.map (·.run.bytes)).all
        (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact fun bytes member => of_decide_eq_true (List.all_eq_true.mp bounded bytes member)
    · have encoded := failure.encoded
      simp [encodeCheckpointIntegrityManifest, bounded, Bind.bind, Except.bind] at encoded
  have failed : CheckpointPublication.run failure.checkpoint.table.runs.toArray.size failure.checkpoint.perform 0 =
      .error failure.cause failure.checkpoint.cut := by
    simpa only [List.size_toArray] using failure.failed
  obtain ⟨_, _, poisoned, closed, drops, published, projected, retryProof⟩ :=
    BoundedReopenTrace.installsAfterCheckpointError (descriptor := descriptor) ready.held
      ready.layout ready.chain append.ordered append.settled append.marker walFits before.published projects
      append.checkpoint before.installed model append.generation append.first refined represented ready.resumed.bounds
      failure.checkpoint.table failure.flushed failure.generationFits failure.runCountFits runBytesFit
      failure.checkpoint.writeRun failure.checkpoint.writeStage failure.checkpoint.sync failure.checkpoint.renameFile
      failure.checkpoint.report before.files.keeper.staged failure.liveRefs failure.fresh failure.reopen.unlock
      failure.reopen.removeFile failure.reopen.write failure.reopen.sync failure.reopen.renameFile
      (ready.freshCheckpoint failure.generationFits) failure.encoded failure.reached failed
  have exactPublished : published = failure.published := Option.some.inj (projected.symm.trans failure.projected)
  subst published
  have released : failure.release.Observed (directory := directory)
      (.poisoned, ⟨failure.checkpoint.cut, before.owners⟩)
      ⟨failure.checkpoint.cut, before.owners.set (directory.file .lock) none⟩ := by
    cases failure.release with
    | closed => exact closed
    | references held dropList last => exact drops held dropList last
  have attempts := failure.attempts
  have initial := checkpointRetryFiles_exact failure.published ready
  dsimp only at attempts initial
  rw [← initial] at attempts
  obtain ⟨kept, layout, chain, manifestChoice, _, selected, _, keeper, tail, _, _, bounded⟩ :=
    retryProof attempts failure.acquisition
  obtain ⟨raw, recover⟩ := failure.reads selected tail
  have opened := bounded raw failure.settles (failure.healthy selected keeper tail)
  have execution : failure.reopen.run directory failure.retry =
      runOpenWithInstallation directory descriptor failure.reopen.nextRef (.ok true) failure.reopen.unlock
        (raw.reopen failure.reopen.removeFile failure.reopen.write failure.reopen.sync failure.reopen.renameFile)
        failure.retry := by
    rw [BoundedReopenAttempt.run, failure.reopenDescriptor, failure.acquired, recover]
  rw [← execution] at opened
  obtain ⟨session, final, after, returned, path, lock, phase, files, owners, wal, target, history, durable, resumed⟩ :=
    opened.writerReady layout chain keeper kept
  have exactWal : after.wal = { before.wal with directory := after.files.directory } := by
    rw [wal, files]; rfl
  have targetPair : after.target.pair = failure.retry.image.directory.active := by rw [target]; rfl
  have targetFirst : after.target.first = before.wal.active.first := target ▸ keeper
  have targetBytes : after.target.trimmed = before.wal.active.bytes := by
    rw [resumed.resumed.contents, history, targetFirst, ready.layout.activeBytes]
  have generationChoice : (after.installed.generation = before.installed.generation ∧
        after.target.pair.manifest = before.wal.directory.active.manifest) ∨
      (after.installed.generation = SegmentedCheckpointReport.generation before ∧
        after.target.pair.manifest = some failure.checkpoint.manifest) := by
    have installedGeneration := resumed.generationRead
    rw [targetPair] at installedGeneration
    rcases manifestChoice with old | new
    · rw [old] at installedGeneration
      exact .inl ⟨Except.ok.inj (installedGeneration.symm.trans append.generation),
        (congrArg DirectoryPublication.Bindings.manifest targetPair).trans old⟩
    · let generation := SegmentedCheckpointReport.generation before
      let runs := failure.checkpoint.table.runs.map (·.run.bytes)
      let header := checkpointHeader failure.checkpoint.table generation
      let metadata := Manifest.IntegrityCheckpoint.fromRuns header runs
      have written := (WrittenCheckpoint.of_flushForCheckpoint failure.flushed refined failure.runCountFits
        ready.resumed.bounds.runs ready.resumed.bounds.memory generation).1
      have stamps : metadata.runs.length = metadata.header.runCount.toNat := by
        simpa [metadata, Manifest.IntegrityCheckpoint.fromRuns, runs, header] using written.count
      have exactBytes : failure.checkpoint.manifest = metadata.encode :=
        Except.ok.inj (failure.encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation runBytesFit))
      have decoded : Manifest.IntegrityCheckpoint.decode failure.checkpoint.manifest = .ok metadata := by
        rw [exactBytes]
        exact Manifest.IntegrityCheckpoint.decode_encode metadata written.validFloor stamps
      rw [new, Option.mapM, decoded] at installedGeneration
      exact .inr ⟨(Except.ok.inj installedGeneration).symm,
        (congrArg DirectoryPublication.Bindings.manifest targetPair).trans new⟩
  exact ⟨after, ⟨poisoned, released, ⟨session, final, returned, path, lock, phase, files, owners⟩,
    history, exactWal, durable, resumed.manifestFiles, targetPair, targetFirst, targetBytes, resumed.resumed.selected,
    generationChoice⟩, resumed⟩

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair) (first : left.first = right.first)
    (bytes : left.trimmed = right.trimmed) : left = right := by
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases bytes
  rfl

private theorem sameCheckpoint {durable binding left right}
    (a : SelectedIntegrityCheckpoint durable binding left) (b : SelectedIntegrityCheckpoint durable binding right) :
    left = right := by
  cases a with
  | absent => cases b; rfl
  | present decode stored loaded =>
    cases b with
    | present otherDecode otherStored otherLoaded =>
      cases Except.ok.inj (decode.symm.trans otherDecode)
      cases Option.some.inj (stored.symm.trans otherStored)
      cases Except.ok.inj (loaded.symm.trans otherLoaded)
      rfl

/-- The reached file projection and the exact returned session determine
the next proof-side writer state. -/
theorem Installs.unique {failure : SegmentedCheckpointFailure directory before writer descriptor}
    {left right : SegmentedWriterState} (a : failure.Installs left) (b : failure.Installs right) :
    left = right := by
  obtain ⟨leftSession, leftFinal, leftResult, _, _, leftPhase, leftFiles, leftOwners⟩ := a.reopened
  obtain ⟨rightSession, rightFinal, rightResult, _, _, rightPhase, rightFiles, rightOwners⟩ := b.reopened
  obtain ⟨session, final⟩ := EStateM.Result.ok.inj (leftResult.symm.trans rightResult)
  have installed : left.installed = right.installed := by
    rw [session] at leftPhase
    exact Phase.ready.inj (leftPhase.symm.trans rightPhase)
  have files : left.files = right.files := by rw [leftFiles, rightFiles, final]
  have owners : left.owners = right.owners := by rw [leftOwners, rightOwners, final]
  have history := a.history.trans b.history.symm
  have wal : left.wal = right.wal := by rw [a.wal, b.wal, files]
  have durable := a.durable.trans b.durable.symm
  have manifest : left.published.manifest = right.published.manifest := by rw [a.manifest, b.manifest, files]
  have published : left.published = right.published := by
    calc
      left.published = ⟨right.published.manifest, left.published.durable⟩ :=
        congrArg (fun binding => CheckpointPublication.Image.mk binding left.published.durable) manifest
      _ = right.published := congrArg (CheckpointPublication.Image.mk right.published.manifest) durable
  have target := sameTarget (a.targetPair.trans b.targetPair.symm) (a.targetFirst.trans b.targetFirst.symm)
    (a.targetBytes.trans b.targetBytes.symm)
  have selected := a.checkpoint
  rw [published, target] at selected
  have checkpoint := sameCheckpoint selected b.checkpoint
  cases left
  cases right
  cases installed
  cases wal
  cases history
  cases files
  cases published
  cases target
  cases checkpoint
  cases owners
  rfl

theorem Installs.preservesReady {failure : SegmentedCheckpointFailure directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : failure.Installs after) (ready : before.Ready directory writer) :
    after.Ready directory descriptor := by
  obtain ⟨selected, installs, next⟩ := failure.installs ready
  exact installs.unique endpoint ▸ next

end SegmentedCheckpointFailure
end Alvoki.Storage.DiskSession
