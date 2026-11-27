import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedLongStageCreateError
import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedBarrierRetryReopen
import Alvoki.Storage.Disk.NativeUncertainWritePowerLoss

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {history : List WAL.Write} {log : List DatabaseSubmissions}
  {before : NativeReadPosition history log} {pending : NativePendingWrite before}
  {crash : NativeUncertainWriteCrash pending.write pending.observed} {input : FilePath}
  {layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history}

/-- The first reported reopen after this reboot reads the surviving
checkpoint and WAL, then fails while creating fresh staging for the long
keeper. The reboot has no borrowed state from the poisoned process. -/
structure RebootLongStageErrorReports (crash : NativeUncertainWriteCrash pending.write pending.observed)
    (input : FilePath) (layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history) where
  admission : CensusOpenAdmissionReports input before.state.session.directory crash.reboot crash.retry
  reads : CapturedMarkedReadReports admission layout before.state.writer.published
  keeper : CapturedKeeperOpenReports reads
  chronology : CapturedMarkedReadCensus reads keeper
  failure : NativeMarkedLongStageCreateError reads keeper
  directory : reads.bindings before.state.session.directory.path = crash.names before.state.session.directory.path
  lock : reads.bindings (before.state.session.directory.file .lock) = crash.names (before.state.session.directory.file .lock)
  manifest : CheckpointCrashChild crash.names admission (before.state.session.directory.file .manifest) "MANIFEST"
  marker : CheckpointCrashChild crash.names admission (before.state.session.directory.file .walBoundary) "WAL.commit"
  runs : ∀ bytes manifest, crash.retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
      CheckpointCrashChild crash.names admission
        (before.state.session.directory.file (.run manifest.header.generation index))
        (renderRunFileName manifest.header.generation index)
  wal : ∀ segment ∈ layout.sealed ++ [layout.keeper], CheckpointCrashChild crash.names admission
    (before.state.session.directory.file (.walSegment segment.first)) (renderWalSegmentName segment.first)
  bytes : ∀ inode payload, reads.reads.objectBytes inode = some payload → crash.contents inode = payload
  noFlat : optionalMetadataWith (admission.lookup (before.state.session.directory.file .wal))
    (admission.reached, admission.held) = .ok none (admission.reached, admission.held)
  markerMetadata : IO.FS.Metadata
  markerFound : optionalMetadataWith (admission.lookup (before.state.session.directory.file .walBoundary))
    (admission.reached, admission.held) = .ok (some markerMetadata) (admission.reached, admission.held)
  unlock : Except IO.Error Unit
  unlocked : admission.unlock admission.owner () failure.atStage = match unlock with
    | .ok () => .ok () (failure.atStage.1, failure.afterUnlock unlock)
    | .error cause => .error cause (failure.atStage.1, failure.afterUnlock unlock)

namespace RebootLongStageErrorReports

/-- Witness one elected read's exact inode and bytes in the reported
survivor. The raw read callbacks still supply the bounded consumption. -/
def ReadsSurvivor (report : RebootLongStageErrorReports crash input layout)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : report.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsFile (report : RebootLongStageErrorReports crash input layout)
    {path : FilePath} {name : String} {object : DeviceInode} {payload : ByteArray}
    (child : CheckpointCrashChild crash.names report.admission path name)
    (bound : report.admission.view.child report.admission.root name = some object)
    (contents : report.reads.reads.objectBytes (report.admission.view.modelObject object) = some payload)
    (call : RunChunkPathReport report.reads.reads path name report.admission.root report.admission.view) :
    report.ReadsSurvivor path payload :=
  ⟨call.observesFile bound contents, child.sameObject call bound contents,
    report.bytes _ _ (call.observesFile bound contents).contents⟩

def ReadsCheckpoint (report : RebootLongStageErrorReports crash input layout) : Prop :=
  (∀ bytes, crash.retry.image.directory.active.manifest = some bytes →
    report.ReadsSurvivor (before.state.session.directory.file .manifest) bytes) ∧
  ∀ bytes manifest, crash.retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
    ∀ payload, before.state.writer.published.durable manifest.header.generation index = some payload →
      report.ReadsSurvivor (before.state.session.directory.file (.run manifest.header.generation index)) payload

private theorem readsCheckpoint (report : RebootLongStageErrorReports crash input layout) : report.ReadsCheckpoint := by
  constructor
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := report.reads.metadata.manifestFile bytes present
    exact report.readsFile report.manifest file.bound file.contents file.calls
  · intro bytes manifest present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := report.reads.runs bytes manifest present decoded index within payload stored
    exact report.readsFile (report.runs bytes manifest present decoded index within) bound contents calls

def ReadsWal (report : RebootLongStageErrorReports crash input layout) : Prop :=
  (∀ bytes, crash.retry.image.directory.active.walBoundary = some bytes →
    report.ReadsSurvivor (before.state.session.directory.file .walBoundary) bytes) ∧
  report.ReadsSurvivor (before.state.session.directory.file (.walSegment layout.keeper.first))
    (layout.keeper.bytes ++ layout.tail) ∧
  ∀ segment ∈ layout.sealed,
    report.ReadsSurvivor (before.state.session.directory.file (.walSegment segment.first)) segment.bytes

private theorem readsWal (report : RebootLongStageErrorReports crash input layout) : report.ReadsWal := by
  refine ⟨?_, ?_, ?_⟩
  · intro bytes present
    obtain ⟨file, _⟩ := report.reads.metadata.markerFile bytes present
    exact report.readsFile report.marker file.bound file.contents file.calls
  · let file := report.reads.wal.keeper
    exact report.readsFile (report.wal _ (List.mem_append_right _ (by simp))) file.bound file.contents file.calls
  · intro segment present
    let file := report.reads.wal.sealedFile segment present
    exact report.readsFile (report.wal _ (List.mem_append_left _ present)) file.bound file.contents file.calls

end RebootLongStageErrorReports

private theorem selectedOldHistory
    (ready : before.state.writer.RetainedReady before.state.session.directory before.state.session.descriptor)
    (manifest : crash.retry.image.directory.active.manifest = before.state.writer.wal.directory.active.manifest)
    (oldMarker : crash.retry.image.directory.active.walBoundary = before.state.writer.wal.directory.active.walBoundary)
    {chosen : List WAL.Write} (layout : CanonicalKeeperLayout crash.retry.image chosen)
    (allowed : chosen = before.state.writer.history ∨ chosen = before.state.writer.history ++ pending.write.failure.batch) :
    chosen = before.state.writer.history := by
  have equalRange : layout.range = before.state.writer.target.range := by
    apply Option.some.inj
    rw [← layout.decoded, ← before.state.writer.target.decoded, ← ready.walPair]
    simp only [DirectoryPublication.Bindings.walRange, manifest, oldMarker]
  have length := layout.through.symm.trans ((congrArg MarkedWalRange.through equalRange).trans ready.resumed.through)
  rcases allowed with old | whole
  · exact old
  have batchLength := (Alvoki.Storage.prepareBatch_spec pending.write.failure.prepared).1
  have rows : pending.write.failure.rows.length ≠ 0 := by simpa using pending.write.failure.nonempty
  rw [whole, List.length_append] at length
  omega

/-- An actual returned uncertain write and joint power-loss report fix
the old committed history when the old marker survives. The held repair
then returns its reported stage or unlock error and no ready session.
The old recorded reads and the single uncertain submission are retained. -/
theorem NativePendingWrite.rejectsOldMarkerStageAfterPowerLoss
    (pending : NativePendingWrite before) (crash : NativeUncertainWriteCrash pending.write pending.observed)
    {input : FilePath}
    (oldMarker : crash.retry.image.directory.active.walBoundary = before.state.writer.wal.directory.active.walBoundary)
    (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history,
      Prepared crash.retry.image layout.target layout.plan → Nonempty (RebootLongStageErrorReports crash input layout)) :
    ∃ (layout : CanonicalKeeperLayout crash.retry.image before.state.writer.history)
      (report : RebootLongStageErrorReports crash input layout),
      (∀ bootstrap install, report.failure.run report.chronology bootstrap install =
        .error (report.failure.diagnostic report.unlock)
          (report.failure.atStage.1, report.failure.afterUnlock report.unlock)) ∧
      (report.failure.afterUnlock report.unlock).image = crash.retry.image.syncDirectory ∧
      SelectedIntegrityCheckpoint before.state.writer.published.durable
        (report.failure.afterUnlock report.unlock).image.directory.active.manifest before.state.writer.checkpoint ∧
      report.admission.owner ∈ report.failure.atStage.1.slots ∧
      report.admission.cached ∈ report.failure.atStage.1.slots ∧
      (TryLockObserves (report.failure.afterUnlock report.unlock).owners before.state.session.directory (.ok true)
        ↔ report.unlock = .ok ()) ∧
      report.reads.bindings before.state.session.directory.path = some (before.state.census.inode before.state.directorySlot.description) ∧
      report.reads.bindings (before.state.session.directory.file .lock) = some (before.state.census.inode before.state.owner.description) ∧
      report.ReadsCheckpoint ∧ report.ReadsWal ∧
      PendingClientReplay pending.submissions before.reads history ∧
      (∀ read ∈ before.reads, read.BoundedBy history.length) ∧
      ∃ seed : NativeMarkedBarrierSeed (crash.reboot, crash.retry) before.state.writer.history
          before.state.writer.published before.state.writer.checkpoint, seed.layout = layout := by
  obtain ⟨valid, earlierHistory, earlierReplay⟩ := before.readPrefix.refines
  obtain ⟨_, kept, manifest, chosen, allowed, _, walLayout, walValid, layout, first, descriptors, offsets,
    prepared, accepted, ordered⟩ :=
    pending.write.failure.refinesReopenPrefixWithWal valid.retained crash.reported
  have old := selectedOldHistory valid.retained manifest oldMarker layout allowed
  subst chosen
  obtain ⟨report⟩ := observe layout prepared
  have manifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair)
  let selected : SelectedIntegrityCheckpoint before.state.writer.published.durable
      crash.retry.image.directory.active.manifest before.state.writer.checkpoint :=
    manifest.symm ▸ valid.retained.resumed.selected
  have following := report.reads.walReads.selectedAfterWatermark offsets descriptors
  have returns := report.failure.returns report.chronology selected prepared following accepted ordered
    report.noFlat report.markerFound report.unlock report.unlocked
  obtain ⟨_, files, ownerLive, directoryLive, release, checkpoint⟩ :=
    returns (fun _ _ => throw report.failure.cause) (fun _ _ _ _ => throw report.failure.cause)
  have directory := report.directory.trans (crash.directory.trans (pending.observed.directoryBound.trans
    (congrArg some pending.observed.sameDirectory)))
  have lock := report.lock.trans (crash.lock.trans (pending.observed.lockBound.trans (congrArg some pending.observed.lockInode)))
  have replay := earlierReplay.appendUncertain (batch := pending.write.failure.batch) before.readPrefix.readsBounded
    (.inl rfl) (earlierHistory ▸ ordered)
  exact ⟨layout, report, fun bootstrap install => (returns bootstrap install).1,
    files, checkpoint, ownerLive, directoryLive, release, directory, lock, report.readsCheckpoint, report.readsWal,
    replay.1, replay.2, ⟨layout, prepared, selected, accepted, following, ordered, _, walLayout, walValid,
      valid.retained.spans, prepared.pair, first, kept⟩, rfl⟩

end Alvoki.Storage.DiskSession
