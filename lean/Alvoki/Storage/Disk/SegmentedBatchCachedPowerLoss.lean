import Alvoki.Storage.Disk.SegmentedBatchMarkerProcessExit
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports
import Alvoki.Storage.Disk.DiskOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

namespace SegmentedBatchMarkerPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}
  {cut : SegmentedBatchMarkerPowerLossReport directory before writer}

/-- The first machine power loss settles the selected pair. Its bounded
retry lineage keeps that pair, including across later crashes. -/
private theorem retryPair {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
      cut.crashed retry) :
    retry.image.directory.active = cut.pair := by
  have selected {current : FileImage} (origin : BeforeReopenBarrier cut.crashed.image current) :
      current.directory.active = cut.pair := by
    cases origin with
    | live => rfl
    | crash pair _ _ survived _ _ => exact List.mem_singleton.mp survived
  cases attempts.lineage (fun left right pair => BatchRetryTarget.unique left right pair) with
  | before origin => exact selected origin
  | repairing origin _ prepared trace =>
    exact (trace.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.trans
      (prepared.pair.symm.trans (selected origin))

/-- Reports of admitted retries and the healthy cached worker at the
reached image. The selected layout determines which observations the
final lock holder must supply. -/
structure CachedReopenReports (cut : SegmentedBatchMarkerPowerLossReport directory before writer)
    (descriptor : Nat) (source : LockedFileState FileImage := cut.crashed) where
  retry : LockedFileState FileImage
  attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
    source retry
  nextRef : Nat
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < nextRef
  acquisition : TryLockObserves retry.owners directory (.ok true)
  unlock : UnlockReport
  recover : EStateM IO.Error FileImage Reopened
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit
  reads : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ cut.batch) → selected.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        wal retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
      ∃ sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest before.published.durable,
        ∃ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
          recover = raw.reopenCached sizes cached removeFile write sync renameFile
  settles : sync #[directory.path] retry.image = .ok () retry.image.syncDirectory
  healthy : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ cut.batch) → selected.target.first = before.wal.active.first →
    ∀ action prior next,
      ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next

namespace CachedReopenReports

variable {source : LockedFileState FileImage}

def run (report : CachedReopenReports cut descriptor source) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock report.recover report.retry

structure InstallsFromCut (report : CachedReopenReports cut descriptor source) (after : SegmentedWriterState) : Prop where
  retries : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
    cut.inFlight report.retry
  reopened : ∃ session final, report.run = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners
  history : after.history = before.history ∨ after.history = before.history ++ cut.batch
  selectedPair : after.target.pair = report.retry.image.directory.active
  selectedMarker : after.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64)
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor

structure Installs (report : CachedReopenReports cut descriptor) (after : SegmentedWriterState) :
    Prop extends InstallsFromCut report after where
  pair : after.target.pair = cut.pair
  marker : cut.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64)

private theorem installsFromCut (report : CachedReopenReports cut descriptor source)
    (observed : cut.Reached) (ready : before.RetainedReady directory writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
      cut.inFlight report.retry) :
    ∃ after, report.InstallsFromCut after := by
  let effects := cut.cut.writeEffects cut.appendCrashTails (before.wal.directory.staged .walBoundary)
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have accepted := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨kept, manifest, history, allowed, marker, layout, valid, selected, _, first, generation, _, installs⟩ :=
    attempts.installsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count
      observed.prepared (observed.preparedHistory ready).2.1 accepted effects cut.physicalProjection
      report.liveRefs report.fresh report.acquisition report.unlock report.removeFile report.write
      report.sync report.renameFile
  let wal := before.wal.appendSelectedView report.retry.image.directory.active history
  obtain ⟨raw, sizes, cached, observedRead⟩ := report.reads history selected allowed first
  have selectedManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := selectedManifest.symm ▸ ready.resumed.selected
  have cachedEq := raw.reopenCached_eq sizes cached layout valid (List.mem_cons_self ..) selected.decoded rfl
    selected.through oldCheckpoint report.removeFile report.write report.sync report.renameFile
  have sealed : report.retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := kept
  have spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize := ready.spans
  obtain ⟨session, final, after, returned, path, slot, phase, files, owners, _, target, exactHistory, _, durable, next⟩ :=
    (installs raw report.settles (report.healthy history selected allowed first)).writerRetained layout valid spans
      rfl first sealed
  have ran : report.run = .ok session final := by
    unfold run
    rw [observedRead, cachedEq]
    exact returned
  have loaded := next.resumed.selected
  rw [durable, target] at loaded
  have checkpoint := Except.ok.inj ((raw.readCheckpoint loaded).symm.trans (raw.readCheckpoint oldCheckpoint))
  have generation : after.installed.generation = before.installed.generation := by
    rw [next.resumed.generation, checkpoint, ← ready.resumed.generation]
  have pair : after.target.pair = report.retry.image.directory.active := congrArg Target.pair target
  have boundary : after.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) := by
    rw [pair, exactHistory]
    exact marker
  exact ⟨after, ⟨attempts, ⟨session, final, ran, path, slot, phase, files, owners⟩,
    exactHistory ▸ allowed, pair, boundary, checkpoint, generation, durable, next⟩⟩

/-- The actual cached worker installs the prior history or the entire
batch from the machine crash's surviving pair. The exact selected
checkpoint and its durable run bytes carry forward unchanged. -/
theorem installs (report : CachedReopenReports cut descriptor)
    (observed : cut.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after := by
  obtain ⟨after, installed⟩ := report.installsFromCut observed.toReached ready (observed.powerLoss.trans report.attempts)
  have pair := installed.selectedPair.trans (retryPair report.attempts)
  exact ⟨after, ⟨installed, pair, pair ▸ installed.selectedMarker⟩⟩

end CachedReopenReports

/-- The first transition drops references from the exiting process.
Subsequent retries use the live file image and its possible survivors. -/
structure ProcessExitCachedReopenReports (cut : SegmentedBatchMarkerPowerLossReport directory before writer)
    (descriptor : Nat) where
  references : HeldLockReferences writer
  process : Nat
  reopen : cut.CachedReopenReports descriptor (references.afterFileDrops [.exited process] directory cut.inFlight)

/-- Install the exact history selected by the final retry after process
exit. The checkpoint is unchanged and the entire batch is kept or lost. -/
theorem ProcessExitCachedReopenReports.installs (report : ProcessExitCachedReopenReports cut descriptor)
    (observed : cut.Reached) (ready : before.RetainedReady directory writer) :
    ∃ after, report.reopen.InstallsFromCut after := by
  have released := (observed.processExit ready report.references report.process).1
  exact report.reopen.installsFromCut observed ready (released.trans report.reopen.attempts)

/-- The admitted marked open returns the next writer at the lock description
it actually opened. The physical cut and all retries precede this open. -/
structure AdmittedRetry {files : Type} (cut : SegmentedBatchMarkerPowerLossReport directory before writer)
    (input : FilePath) (retry : LockedFileState FileImage) (descriptor : Nat) (after : SegmentedWriterState) : Prop where
  retries : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
    cut.inFlight retry
  reopened : ∃ (history : List WAL.Write) (layout : CanonicalKeeperLayout retry.image history)
    (reported : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory reported.slot) (session : SegmentedSession)
    (final : LockedFileState FileImage),
    reported.runWithAdmission admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    final.owners.Owns directory descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
    final.image.directory.active = retry.image.directory.active ∧ after.history = history
  history : after.history = before.history ∨ after.history = before.history ++ cut.batch
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor

/-- The post-retry layout comes from the reached batch cut. Exact native
admission and checkpoint/WAL reads for that layout then install the next
writer. There is one selection for the whole batch, including after a live
exit followed by another machine power loss. -/
theorem Reached.installsAdmitted {files : Type} {input : FilePath} {retry : LockedFileState FileImage}
    (observed : cut.Reached) (ready : before.RetainedReady directory writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
      cut.inFlight retry)
    (reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ cut.batch) →
      layout.target.first = before.wal.active.first →
      ∃ reported : MarkedRetryChunkReports files directory layout before.published,
        Nonempty (OpenAdmissionReports input directory reported.slot)) :
    ∃ descriptor after, AdmittedRetry (files := files) cut input retry descriptor after := by
  let effects := cut.cut.writeEffects cut.appendCrashTails (before.wal.directory.staged .walBoundary)
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have oldAccepted := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨kept, manifest, history, allowed, _, layout, valid, selected, _, first, _, descriptors, offsets,
    prepared, _, accepted, ordered, _, _⟩ :=
    attempts.selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count observed.prepared
      (observed.preparedHistory ready).2.1 oldAccepted effects cut.physicalProjection
  obtain ⟨reported, ⟨admission⟩⟩ := reads history selected allowed first
  have following := reported.selectedAfterWatermark offsets descriptors
  have installed := runOpenWithAdmission_markedRetryFromChunks reported admission
    prepared.keeperPrefix prepared.newer following accepted ordered
  rw [reported.runWithAdmission_eq admission] at installed
  obtain ⟨_, cutReady⟩ := installed.appendCutReady accepted ordered
  let wal := before.wal.appendSelectedView retry.image.directory.active history
  have sealed : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := kept
  have spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize := ready.spans
  obtain ⟨session, final, after, returned, path, slot, phase, files, owners, _, target, exactHistory, _, durable, next⟩ :=
    cutReady.writerRetained layout valid spans rfl first sealed
  have readyAfter : after.RetainedReady directory reported.slot.description := reported.inventoryDescription ▸ next
  have oldManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := oldManifest.symm ▸ ready.resumed.selected
  have loaded := readyAfter.resumed.selected
  rw [durable, target] at loaded
  have checkpoint := loaded.uniqueResult oldCheckpoint
  have generation : after.installed.generation = before.installed.generation := by
    rw [readyAfter.resumed.generation, checkpoint, ← ready.resumed.generation]
  have held : final.owners.Owns directory reported.slot.description := owners ▸ readyAfter.held
  have pair : final.image.directory.active = retry.image.directory.active :=
    files ▸ (readyAfter.resumed.ready.selected.trans (congrArg Target.pair target))
  exact ⟨reported.slot.description, after, attempts, ⟨history, selected, reported, admission, session, final,
    (reported.runWithAdmission_eq admission).trans returned, path, slot.trans reported.inventoryDescription,
    phase, held, files, owners, pair, exactHistory⟩, exactHistory ▸ allowed, checkpoint, generation, durable, readyAfter⟩

end SegmentedBatchMarkerPowerLossReport
end Alvoki.Storage.DiskSession
