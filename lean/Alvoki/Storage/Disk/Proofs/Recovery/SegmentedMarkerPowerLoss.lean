import Alvoki.Storage.Disk.Proofs.Append.RetainedAppendRecovery
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCachedExtentReports
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentMarkerPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary
open WAL (frameSize)

/-- Project the reached marker callback into the active segment, keeping
the old run manifest, the immutable sealed bytes and unrelated scratch. -/
def markerCutFiles (cut : MarkerInterruption) (before : SegmentedWriterState) (event : WAL.Write)
    (appendCrashTails : List ByteArray) : FileImage :=
  let scratch := before.wal.directory.staged .walBoundary
  let marker := WAL.Boundary.encode (WAL.encode (before.history ++ [event])).size.toUInt64
  let reached := cut.reached before.history event appendCrashTails scratch
  let actual := cut.interrupt marker reached
  let observed := actual.reopenImage (before.history.drop before.wal.active.first)
    before.wal.directory.active.manifest (before.wal.directory.staged .manifest) before.files.keeper.staged
  before.wal.appendReopenFiles observed before.files.keeper.staged

private theorem markerCutChoices (cut : MarkerInterruption) (before : SegmentedWriterState) (event : WAL.Write)
    (appendCrashTails : List ByteArray) :
    let effects := cut.writeEffects appendCrashTails (before.wal.directory.staged .walBoundary)
    let actual := markerCutFiles cut before event appendCrashTails
    let modeled := appendCutFiles before.wal before.history event effects before.files.keeper.staged
    actual.directory.crashImages = modeled.directory.crashImages ∧
      actual.keeper.crashImages = modeled.keeper.crashImages := by
  intro effects actual modeled
  obtain ⟨_, tails, _, markers⟩ :=
    cut.matchesWriteEffects before.history event appendCrashTails (before.wal.directory.staged .walBoundary)
  exact ⟨congrArg (List.map (DirectoryPublication.Bindings.mk before.wal.directory.active.manifest)) markers,
    congrArg (List.map (fun tail => some (WAL.encode (before.history.drop before.wal.active.first) ++ tail))) tails⟩

private theorem fixedAppendPair {directory : DiskDirectory} {before retry : LockedFileState FileImage}
    {history : List WAL.Write} {event : WAL.Write} {first : Nat}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget history event first) before retry)
    (settled : before.image.directory.crashImages = [before.image.directory.active]) :
    retry.image.directory.active = before.image.directory.active := by
  have fromSource {current : FileImage} (source : BeforeReopenBarrier before.image current) :
      current.directory.active = before.image.directory.active := by
    cases source with
    | live => rfl
    | crash pair _ _ chosen _ _ => exact List.mem_singleton.mp (settled ▸ chosen)
  cases attempts.lineage (fun a b pair => AppendRetryTarget.unique a b pair) with
  | before observed => exact fromSource observed
  | repairing observed _ prepared trace =>
    exact (trace.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.trans
      (prepared.pair.symm.trans (fromSource observed))

/-- A submitted append interrupted in one of the marker callbacks, the
files that survived power loss, and the next healthy bounded-open reports. -/
structure SegmentedMarkerPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  event : WAL.Write
  table : PackedTable
  activeMetadata : FilePath → Except IO.Error IO.FS.Metadata
  cut : MarkerInterruption
  appendCrashTails : List ByteArray
  pair : DirectoryPublication.Bindings
  keeper : ByteArray
  retry : LockedFileState FileImage
  attempts : BoundedReopenTrace directory (AppendRetryTarget before.history event before.wal.active.first)
    ⟨(markerCutFiles cut before event appendCrashTails).crash pair (some keeper) [],
      before.owners.set (directory.file .lock) none⟩ retry
  reopen : BoundedReopenAttempt
  descriptorEq : reopen.descriptor = descriptor
  acquired : reopen.acquired = .ok true
  acquisition : TryLockObserves retry.owners directory (.ok true)
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef
  reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
      reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile
  settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory
  healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
    ∀ action prior next,
      ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
        .ok () next

namespace SegmentedMarkerPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

def physical (report : SegmentedMarkerPowerLossReport directory before writer descriptor) : FileImage :=
  markerCutFiles report.cut before report.event report.appendCrashTails

def crashed (report : SegmentedMarkerPowerLossReport directory before writer descriptor) : LockedFileState FileImage :=
  ⟨report.physical.crash report.pair (some report.keeper) [], before.owners.set (directory.file .lock) none⟩

structure Valid (report : SegmentedMarkerPowerLossReport directory before writer descriptor) : Prop where
  prepared : prepareWrite before.installed.table report.event.key report.event.value = some (report.event, report.table)
  fits : before.installed.walBytes + frameSize < UInt64.size
  activeGuard : ∃ metadata,
    report.activeMetadata (directory.file (.walSegment before.installed.activeFirst)) = .ok metadata ∧
    metadata.type = .file ∧ metadata.numLinks = 1 ∧
    metadata.byteSize.toNat = before.installed.walBytes - before.installed.activeFirst * frameSize
  metadata : report.pair ∈ report.physical.directory.crashImages
  payload : some report.keeper ∈ report.physical.keeper.crashImages

theorem Valid.powerLoss {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    (observed : report.Valid) :
    BoundedReopenTrace directory (AppendRetryTarget before.history report.event before.wal.active.first)
      ⟨report.physical, before.owners⟩ report.crashed :=
  .powerLoss .empty observed.metadata observed.payload (List.mem_singleton_self _)

private theorem Valid.preparedHistory {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    report.event.sequence.toNat = before.history.length + 1 ∧
    WAL.OrdinalsFrom 1 (before.history ++ [report.event]) ∧
    (WAL.encode (before.history ++ [report.event])).size < UInt64.size := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨event, ordinal, ordered, _, bytes⟩ :=
    prepareWrite_extends_history ready.resumed.ordered count observed.prepared
  refine ⟨by rw [event]; exact ordinal, ordered, ?_⟩
  rw [bytes, ← ready.resumed.bytes]
  exact observed.fits

theorem Valid.submittedSequence {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    (observed : report.Valid) (ready : before.Ready directory writer) :
    report.event.sequence.toNat = before.history.length + 1 :=
  (observed.preparedHistory ready.toRetained).1

structure Installs (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop extends
    AppendRetryEndpoint directory before report.event report.retry descriptor
      (report.reopen.run directory report.retry) after where
  powerLoss : BoundedReopenTrace directory (AppendRetryTarget before.history report.event before.wal.active.first)
    ⟨report.physical, before.owners⟩ report.crashed
  marker : report.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64)
  priorCheckpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation

private theorem Valid.modeledRetries {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    (observed : report.Valid) :
    let effects := report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary)
    BoundedReopenTrace directory (AppendRetryTarget before.history report.event before.wal.active.first)
      ⟨appendCutFiles before.wal before.history report.event effects before.files.keeper.staged, before.owners⟩
      report.retry := by
  let effects := report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary)
  let modeled := appendCutFiles before.wal before.history report.event effects before.files.keeper.staged
  obtain ⟨markers, keepers⟩ := markerCutChoices report.cut before report.event report.appendCrashTails
  have first : BoundedReopenTrace directory (AppendRetryTarget before.history report.event before.wal.active.first)
      ⟨modeled, before.owners⟩ report.crashed :=
    .powerLoss .empty (markers ▸ observed.metadata) (keepers ▸ observed.payload) (List.mem_singleton_self _)
  exact first.trans report.attempts

/-- Recover from the actual physical power-loss cut, then run the healthy
bounded open on the exact surviving files. The marker chooses the old
history or that history plus the one submitted frame. -/
theorem installs (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.Ready directory writer) :
    ∃ after, report.Installs after ∧ after.Ready directory descriptor := by
  let effects := report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary)
  have attempts := observed.modeledRetries
  have ⟨_, extended, fits⟩ := observed.preparedHistory ready.toRetained
  obtain ⟨_, history, survived, manifest, marker, wal, walEq, layout, chain, kept, selected, _, keeper, opened⟩ :=
    attempts.installsAfterAppendCut (descriptor := descriptor) ready.appendInput report.event extended fits effects
      before.files.keeper.staged report.liveRefs report.fresh report.acquisition report.reopen.unlock
      report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  subst wal
  obtain ⟨raw, exactRead⟩ := report.reads history selected survived keeper
  obtain ⟨session, final, after, returned, path, acquired, phase, files, owners, actualWal, target, exactHistory,
    durable, next⟩ := (opened raw report.settles (report.healthy history selected survived keeper)).writerReady
      layout chain keeper kept
  have actualResult : report.reopen.run directory report.retry = .ok session final := by
    unfold BoundedReopenAttempt.run
    rw [report.descriptorEq, report.acquired, exactRead]
    exact returned
  have afterWal : after.wal = { before.wal.appendSelectedView report.retry.image.directory.active after.history with
      directory := after.files.directory } := by rw [actualWal, files, exactHistory]
  have survivingPair : report.retry.image.directory.active = report.pair :=
    fixedAppendPair report.attempts rfl
  have exactMarker : report.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) := by
    rw [← survivingPair, exactHistory]
    exact marker
  have beforePair : before.wal.directory.active = before.target.pair :=
    (congrArg DirectoryPublication.Image.active ready.directoryFiles.symm).trans ready.resumed.ready.selected
  have selectedManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest beforePair)
  have loaded := next.resumed.selected
  rw [durable, target] at loaded
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := selectedManifest.symm ▸ ready.resumed.selected
  have priorCheckpoint := Except.ok.inj ((raw.readCheckpoint loaded).symm.trans (raw.readCheckpoint oldCheckpoint))
  have generation : after.installed.generation = before.installed.generation := by
    rw [next.resumed.generation, priorCheckpoint, ← ready.resumed.generation]
  exact ⟨after, ⟨⟨⟨session, final, actualResult, path, acquired, phase, files, owners⟩, exactHistory ▸ survived,
    afterWal, target ▸ rfl, by rw [target, keeper]; rfl, next.resumed.through, next.resumed.contents, durable,
    next.manifestFiles, next.resumed.selected⟩, observed.powerLoss, exactMarker, priorCheckpoint, generation⟩, next⟩

/-- After covered WAL deletion, the same physical power-loss cut leaves
one selected marker and the retained suffix needed by the original checkpoint. -/
theorem installsRetained (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  let effects := report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary)
  have ⟨_, extended, fits⟩ := observed.preparedHistory ready
  obtain ⟨after, endpoint, next, marker, checkpoint, generation⟩ := observed.modeledRetries.reopensRetainedAppend
    ready report.event extended fits effects report.reopen report.descriptorEq report.acquired report.acquisition
    report.liveRefs report.fresh report.reads report.settles report.healthy
  have samePair : report.retry.image.directory.active = report.pair := fixedAppendPair report.attempts rfl
  have exactMarker := (congrArg DirectoryPublication.Bindings.walBoundary samePair).symm.trans marker
  exact ⟨after, ⟨endpoint, observed.powerLoss, exactMarker, checkpoint, generation⟩, next⟩

/-- The exact cached reads for whichever history the visible marker
selects. The keeper's reported extent includes its unselected tail. -/
def CachedReads (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
    (recover : EStateM IO.Error FileImage Reopened) : Prop :=
  ∀ history, ∀ selected : CanonicalKeeperLayout report.retry.image history,
    (history = before.history ∨ history = before.history ++ [report.event]) →
    selected.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView report.retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (report.retry.owners.set (directory.file .lock) (some descriptor))
        descriptor wal report.retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
      ∃ sizes : SizedCheckpointRunReports directory raw.reports report.retry.image.directory.active.manifest
          before.published.durable,
        ∃ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
          recover = raw.reopenCached sizes cached report.reopen.removeFile report.reopen.write report.reopen.sync
            report.reopen.renameFile

/-- Recover from the reached marker publication cut and any admitted
retry prefix. The actual cached action installs the history selected by
the surviving marker and preserves the exact prior checkpoint. -/
theorem installsRetainedCached (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (recover : EStateM IO.Error FileImage Reopened) (reads : report.CachedReads recover) :
    ∃ after, AppendRetryEndpoint directory before report.event report.retry descriptor
      (runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
        report.reopen.unlock recover report.retry) after ∧
      after.RetainedReady directory descriptor ∧
      report.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation := by
  let effects := report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary)
  have ⟨_, extended, fits⟩ := observed.preparedHistory ready
  have lineage := observed.modeledRetries.lineage (fun a b pair => AppendRetryTarget.unique a b pair)
  obtain ⟨after, endpoint, next, marker, checkpoint, generation⟩ := lineage.reopensRetainedAppendWith
    ready report.event extended fits effects report.reopen report.descriptorEq report.acquired report.acquisition
    report.liveRefs report.fresh recover (by
      intro history selected survived first wal layout valid oldCheckpoint
      obtain ⟨raw, sizes, cached, reported⟩ := reads history selected survived first
      have chosen : wal.Selects report.retry.image.directory.active := List.mem_cons_self ..
      exact ⟨raw, reported.trans (raw.reopenCached_eq sizes cached layout valid chosen selected.decoded rfl
        selected.through oldCheckpoint report.reopen.removeFile report.reopen.write report.reopen.sync
        report.reopen.renameFile)⟩) report.settles report.healthy
  have samePair : report.retry.image.directory.active = report.pair := fixedAppendPair report.attempts rfl
  exact ⟨after, endpoint, next, (congrArg DirectoryPublication.Bindings.walBoundary samePair).symm.trans marker,
    checkpoint, generation⟩

theorem Installs.unique {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right :=
  a.toAppendRetryEndpoint.unique b.toAppendRetryEndpoint

theorem Installs.preservesReady {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory writer) : after.Ready directory descriptor := by
  obtain ⟨_, installed, next⟩ := report.installs observed ready
  exact installed.unique endpoint ▸ next

theorem Installs.preservesRetained {report : SegmentedMarkerPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory writer) : after.RetainedReady directory descriptor := by
  obtain ⟨_, installed, next⟩ := report.installsRetained observed ready
  exact installed.unique endpoint ▸ next

end SegmentedMarkerPowerLossReport

end Alvoki.Storage.DiskSession
