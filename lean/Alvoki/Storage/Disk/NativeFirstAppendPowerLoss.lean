import Alvoki.Storage.Disk.NativePendingFirstAppend
import Alvoki.Storage.Disk.NativeWriteCrashReads

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

/-- The reported filesystem survivor at the native append stop. The
keeper inode still has the old marked prefix, followed by one permitted
tail. The settled marker and the same directory and lock survive. -/
structure NativeFirstAppendCrash (stop : NativeFirstAppendStop prepared) where
  tail : ByteArray
  survives : tail ∈ ByteArray.empty :: stop.cut.crashTails
  raw : WriteCrashView
  root : raw.names state.session.directory.path = some (stop.view.modelObject stop.root)
  lock : raw.names (state.session.directory.file .lock) = some (stop.view.modelObject stop.lock.child)
  keeper : raw.names prepared.keeperPath = some (stop.view.modelObject stop.keeper.child)
  marker : raw.names prepared.markerPath = some (stop.view.modelObject stop.marker.child)

namespace NativeFirstAppendCrash

variable {stop : NativeFirstAppendStop prepared}

def origin (crash : NativeFirstAppendCrash stop) : stop.logical.Stop state.session.descriptor :=
  .powerLoss crash.tail crash.survives

def retry (crash : NativeFirstAppendCrash stop) : LockedFileState FileImage :=
  crash.origin.origin

theorem vacant (crash : NativeFirstAppendCrash stop) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  simp [retry, origin, BatchAppendInterruption.Stop.origin, FirstAppendCut.crashed, TryLockObserves, LockOwners.set]

/-- The unchanged marker determines the original checkpoint and exact
keeper read layout, independent of the admitted excess tail bytes. -/
structure Plan (crash : NativeFirstAppendCrash stop) where
  loss : BoundedReopenTrace state.session.directory (· = state.writer.target)
    ⟨stop.files, state.files.owners⟩ crash.retry
  pair : crash.retry.image.directory.active = state.writer.target.pair
  layout : CanonicalKeeperLayout crash.retry.image state.writer.history
  recovery : BatchAppendInterruption.PreparedRetry state.writer layout
  selected : SelectedIntegrityCheckpoint state.writer.published.durable crash.retry.image.directory.active.manifest
    state.writer.checkpoint

theorem plans (crash : NativeFirstAppendCrash stop) (valid : state.Valid) : Nonempty crash.Plan := by
  obtain ⟨_, loss, pair, layout, recovery⟩ := crash.origin.refinesReopenPrefix valid.retained .start
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  exact ⟨⟨loss, pair, layout, recovery, manifest.symm ▸ valid.retained.resumed.selected⟩⟩

end NativeFirstAppendCrash

/-- The reported reopened read prefix observes the original physical
root and the same keeper and marker device/inode, with the chosen
durable bytes for the marker and keeper and all selected files. -/
structure NativeFirstAppendCrashReads {stop : NativeFirstAppendStop prepared} (crash : NativeFirstAppendCrash stop)
    (input : FilePath) (layout : CanonicalKeeperLayout crash.retry.image state.writer.history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint)
    extends NativeWriteCrashReads crash.raw input crash.vacant layout selected where
  root : opening.admission.root = stop.root
  sameObjects : opening.admission.view.modelObject = stop.view.modelObject
  keeperObject : opening.reads.wal.keeper.object = stop.keeper.child
  markerChild : opening.admission.view.child opening.admission.root "WAL.commit" = some stop.marker.child
  manifestChild : opening.admission.view.child opening.admission.root "MANIFEST" = stop.view.child stop.root "MANIFEST"
  runChild : ∀ bytes manifest, crash.retry.image.directory.active.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
      let name := renderRunFileName manifest.header.generation index
      opening.admission.view.child opening.admission.root name = stop.view.child stop.root name
  sealChild : ∀ segment ∈ layout.sealed,
    let name := renderWalSegmentName segment.first
    opening.admission.view.child opening.admission.root name = stop.view.child stop.root name

/-- The stopped write remains a single uncertain submission. The
surviving marker excludes that batch from the history that the old
keeper prefix and chosen checkpoint install in the next session. -/
structure NativeFirstAppendCrashContinuation (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeFirstAppendStop prepared}
    (crash : NativeFirstAppendCrash stop) (input : FilePath)
    (next : NativeReadPosition history (log ++ [.uncertainBatch prepared.batch])) : Prop where
  stopped : NativePendingFirstAppend current stop
  loss : BoundedReopenTrace current.state.session.directory (· = current.state.writer.target)
    ⟨stop.files, current.state.files.owners⟩ crash.retry
  reads : next.reads = current.reads
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  replay : InstalledClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
    next.state.writer.installed next.state.session
  exactOpen :
    ∃ (layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (seen : NativeFirstAppendCrashReads crash input layout selected),
      next.opened = seen.opening.finish.run seen.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.session.directory = current.state.session.directory ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      seen.opening.reads.bindings current.state.session.directory.path =
        some (current.state.census.inode current.state.directorySlot.description) ∧
      seen.opening.reads.bindings (current.state.session.directory.file .lock) =
        some (current.state.census.inode current.state.owner.description) ∧
      seen.toNativeWriteCrashReads.ReadsSurvivor prepared.markerPath
        (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      seen.toNativeWriteCrashReads.ReadsSurvivor prepared.keeperPath
        (current.state.writer.wal.active.bytes ++ crash.tail)

/-- Keep the same captured reader available to the raw opener. The
pending batch is excluded from the replay before any keeper repair. -/
theorem NativeReadPosition.recoversFirstAppendPowerLossFrom (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeFirstAppendStop prepared}
    (crash : NativeFirstAppendCrash stop) {input : FilePath} (plan : crash.Plan)
    (seen : NativeFirstAppendCrashReads crash input plan.layout plan.selected) :
    ∃ next, NativeFirstAppendCrashContinuation current crash input next ∧
      next.opened = seen.opening.finish.run seen.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.owner = seen.opening.admission.owner ∧
      next.state.directorySlot = seen.opening.admission.cached := by
  obtain ⟨valid, earlierHistory, _⟩ := current.readPrefix.refines
  let stopped := current.stopsAtFirstAppend stop
  obtain ⟨loss, pair, layout, selectedLayout, selected⟩ := plan
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  let ready := valid.retained
  have accepted := manifest.symm ▸ ready.resumed.accepted
  have pending : PendingClientReplay (log ++ [.uncertainBatch prepared.batch])
      current.reads current.state.writer.history := earlierHistory.symm ▸ stopped.replay
  have bounded : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length :=
    earlierHistory.symm ▸ stopped.bounded
  have pairWal := ready.walPair.trans (congrArg Target.pair selectedLayout.target).symm
  obtain ⟨after, seed, cache, census, owner, directorySlot, _, durable, checkpoint, path, _, _, _, _, phaseFresh, sessionFresh⟩ :=
    seen.opening.finish.startsNativeReadPrefix seen.opening.chronology seen.opening.markerFound selectedLayout.prepared
      (seen.opening.reads.walReads.selectedAfterWatermark selectedLayout.offsets selectedLayout.descriptors)
      accepted ready.resumed.ordered ready.layout ready.valid ready.spans pairWal selectedLayout.first
      (selectedLayout.kept.trans ready.sealedFiles) pending bounded
  have continued : NativeReadyReadPrefix (seen.opening.finish.run seen.opening.chronology) after history
      (log ++ [.uncertainBatch prepared.batch]) current.reads after :=
    Eq.mp (congrArg (fun journal => NativeReadyReadPrefix (seen.opening.finish.run seen.opening.chronology) after
      journal (log ++ [.uncertainBatch prepared.batch]) current.reads after) earlierHistory) seed
  let next : NativeReadPosition history (log ++ [.uncertainBatch prepared.batch]) :=
    ⟨seen.opening.finish.run seen.opening.chronology, after, after, current.reads, continued⟩
  have marker := (congrArg DirectoryPublication.Bindings.walBoundary pair).trans (ready.selectPriorKeeper crash.tail).1
  rw [earlierHistory] at marker
  have markerRead := seen.toNativeWriteCrashReads.readsMarker marker
  have keeperRead := seen.toNativeWriteCrashReads.readsKeeper
  have physicalKeeper : crash.retry.image.keeper.active =
      some (current.state.writer.wal.active.bytes ++ crash.tail) := by
    change some (WAL.encode (current.state.writer.history.drop current.state.writer.wal.active.first) ++ crash.tail) = _
    rw [ready.layout.activeBytes]
  have keeperBytes : layout.keeper.bytes ++ layout.tail = current.state.writer.wal.active.bytes ++ crash.tail :=
    Option.some.inj (layout.visible.symm.trans physicalKeeper)
  have keeperPath : current.state.session.directory.file (.walSegment layout.keeper.first) = prepared.keeperPath :=
    congrArg (fun offset => current.state.session.directory.file (.walSegment offset))
      ((congrArg Target.first selectedLayout.target).trans ready.resumed.keeper.symm)
  rw [keeperPath, keeperBytes] at keeperRead
  exact ⟨next, ⟨stopped, loss, rfl, fun same => phaseFresh (same.symm ▸ seen.previousTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.previousTokens.2), checkpoint, durable, continued.guardedReplay,
    ⟨layout, selected, seen, rfl, seed.frames.1, rfl, path, cache, census, owner, directorySlot,
      seen.directory.trans (crash.root.trans (congrArg some stop.directoryIdentity)),
      seen.lock.trans (crash.lock.trans (congrArg some stop.lockIdentity)), markerRead, keeperRead⟩⟩,
    rfl, seed.frames.1, cache, owner, directorySlot⟩

theorem NativeReadPosition.recoversFirstAppendPowerLoss (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeFirstAppendStop prepared}
    (crash : NativeFirstAppendCrash stop) {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history,
      BatchAppendInterruption.PreparedRetry current.state.writer layout →
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeFirstAppendCrashReads crash input layout selected)) :
    ∃ next, NativeFirstAppendCrashContinuation current crash input next := by
  obtain ⟨plan⟩ := crash.plans current.readPrefix.refines.1
  obtain ⟨seen⟩ := observe plan.layout plan.recovery plan.selected
  obtain ⟨next, reopened, _⟩ := current.recoversFirstAppendPowerLossFrom crash plan seen
  exact ⟨next, reopened⟩

end Alvoki.Storage.DiskSession
