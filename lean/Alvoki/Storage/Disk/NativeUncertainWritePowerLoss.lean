import Alvoki.Storage.Disk.NativeExecutionPendingWrite
import Alvoki.Storage.Disk.NativeWriteCrashReads

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

/-- A joint filesystem survivor of the exact returned write failure.
The reboot takes a new empty slot census. Names and bytes are reported
from the same surviving namespace of the original directory. -/
structure NativeUncertainWriteCrash {state : NativeReadyState} (write : NativeReadyWriteFailure state)
    {cache : CensusDirectoryCache} (census : NativePendingWriteCensus state cache) where
  image : FileImage
  survives :
    ∃ pair ∈ write.failure.released.image.directory.crashImages,
      ∃ payload ∈ write.failure.released.image.keeper.crashImages,
        ∃ later ∈ write.failure.released.image.later.crashImages,
          image = write.failure.released.image.crash pair payload later
  names : FilePath → Option Nat
  contents : Nat → ByteArray
  directory : names state.session.directory.path = census.bindings state.session.directory.path
  lock : names (state.session.directory.file .lock) = census.bindings (state.session.directory.file .lock)
  rebootObjects : Nat → Nat

namespace NativeUncertainWriteCrash

variable {state : NativeReadyState} {write : NativeReadyWriteFailure state}
  {cache : CensusDirectoryCache} {census : NativePendingWriteCensus state cache}

def reboot (crash : NativeUncertainWriteCrash write census) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

def retry (crash : NativeUncertainWriteCrash write census) : LockedFileState FileImage :=
  ⟨crash.image, state.writer.owners.set (state.session.directory.file .lock) none⟩

theorem vacant (crash : NativeUncertainWriteCrash write census) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  simp [retry, TryLockObserves, LockOwners.set]

theorem reported (crash : NativeUncertainWriteCrash write census) :
    ReportedReopenPrefix state.session.directory state.writer.wal.active.first
      ⟨write.failure.released.image, state.writer.owners⟩ crash.retry := by
  obtain ⟨pair, metadata, payload, keeper, later, names, selected⟩ := crash.survives
  unfold retry
  rw [selected]
  exact .powerLoss .start metadata keeper names

/-- The selected marker determines the exact history and retained WAL
view used by the aborted write's recovery. -/
def wal (crash : NativeUncertainWriteCrash write census) (history : List WAL.Write) : WalSegmentImage :=
  state.writer.wal.appendSelectedView crash.retry.image.directory.active history

structure Plan (crash : NativeUncertainWriteCrash write census) where
  history : List WAL.Write
  allowed : history = state.writer.history ∨ history = state.writer.history ++ write.failure.batch
  marker : crash.retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  layout : CanonicalKeeperLayout crash.retry.image history
  walLayout : (crash.wal history).ReadLayout history
  walValid : (crash.wal history).Valid history
  first : layout.target.first = (crash.wal history).active.first
  descriptors : layout.sealed ++ [layout.keeper] = (crash.wal history).readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads ((crash.wal history).segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, ((crash.wal history).readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.retry.image layout.target layout.plan
  kept : crash.retry.image.kept = ((crash.wal history).checkpointReopenFiles (crash.wal history).directory none).kept
  selected : SelectedIntegrityCheckpoint state.writer.published.durable
    crash.retry.image.directory.active.manifest state.writer.checkpoint
  accepted : state.writer.published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
    crash.retry.image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history

theorem plans (crash : NativeUncertainWriteCrash write census) (valid : state.Valid) : Nonempty crash.Plan := by
  obtain ⟨_, kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, first, descriptors, offsets,
    prepared, accepted, ordered⟩ := write.failure.refinesReopenPrefixWithWal valid.retained crash.reported
  have selectedManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair)
  exact ⟨⟨chosen, allowed, marker, layout, walLayout, walValid, first, descriptors, offsets, prepared, kept,
    selectedManifest.symm ▸ valid.retained.resumed.selected, accepted, ordered⟩⟩

end NativeUncertainWriteCrash

/-- The admitted read reports use the same reported reboot view as the
returned uncertain write's file survivor. -/
abbrev NativeUncertainWriteCrashReads {state : NativeReadyState} {write : NativeReadyWriteFailure state}
    {cache : CensusDirectoryCache} {census : NativePendingWriteCensus state cache}
    (crash : NativeUncertainWriteCrash write census) (input : FilePath)
    {history : List WAL.Write} (layout : CanonicalKeeperLayout crash.retry.image history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint) :=
  NativeWriteCrashReads ⟨crash.names, crash.contents, crash.rebootObjects⟩ input crash.vacant layout selected

structure NativeUncertainWriteCrashEffects {state : NativeReadyState} (write : NativeReadyWriteFailure state)
    (cache : CensusDirectoryCache) (input : FilePath) where
  census : NativePendingWriteCensus state cache
  crash : NativeUncertainWriteCrash write census
  plan : crash.Plan
  reader : NativeUncertainWriteCrashReads crash input plan.layout plan.selected

structure NativeUncertainWriteCrashObservation (state : NativeReadyState) (input : FilePath) where
  write : NativeReadyWriteFailure state
  cache : CensusDirectoryCache
  returned : write.returnedAt cache
  effects : NativeUncertainWriteCrashEffects write cache input

/-- Recover the same earlier ledger after an actual uncertain write and
a reported power loss. The uncertain group is either entirely present
or absent, as determined by the selected marker. -/
structure NativeUncertainWriteCrashContinuation (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeUncertainWriteCrashObservation current.state input) (retained : List WAL.Write)
    (next : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch observed.write.failure.batch])) : Prop where
  wholeOrNone : retained = [] ∨ retained = observed.write.failure.batch
  reads : next.reads = current.reads
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  marker : next.state.files.image.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64)
  exactOpen :
    let effects := observed.effects
    let reader := effects.reader
    effects.plan.history = history ++ retained ∧ effects.crash.reboot.slots = [] ∧
      next.opened = reader.opening.finish.run reader.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.session.directory = current.state.session.directory ∧
      next.state.cache = reader.opening.admission.cache ∧ next.state.census = reader.opening.finish.census ∧
      next.state.owner = reader.opening.admission.owner ∧ next.state.directorySlot = reader.opening.admission.cached ∧
      reader.opening.reads.bindings (current.state.session.directory.file .lock) =
        some (current.state.census.inode current.state.owner.description) ∧
      reader.opening.reads.bindings current.state.session.directory.path =
        some (current.state.census.inode current.state.directorySlot.description)
  replay : InstalledClientReplay (log ++ [.uncertainBatch observed.write.failure.batch]) current.reads
    (history ++ retained) next.state.writer.installed next.state.session

theorem NativeReadPosition.recoversUncertainWriteAfterPowerLoss (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeUncertainWriteCrashObservation current.state input) :
    ∃ retained next, NativeUncertainWriteCrashContinuation current observed retained next := by
  obtain ⟨valid, earlierHistory, replay⟩ := current.readPrefix.refines
  let effects := observed.effects
  let plan := effects.plan
  let seen := effects.reader
  have allowed : plan.history = history ∨ plan.history = history ++ observed.write.failure.batch :=
    plan.allowed.imp (·.trans earlierHistory)
      (·.trans (congrArg (· ++ observed.write.failure.batch) earlierHistory))
  obtain ⟨pending, bounded⟩ := replay.appendUncertain current.readPrefix.readsBounded allowed plan.ordered
  obtain ⟨reached, seed, cacheEq, censusEq, owner, directorySlot, pair, durable, checkpoint, directory, _, _, _, _,
    phaseFresh, sessionFresh⟩ :=
    seen.opening.finish.startsNativeReadPrefix seen.opening.chronology seen.opening.markerFound plan.prepared.newer
      (seen.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors) plan.accepted plan.ordered
      plan.walLayout plan.walValid valid.retained.spans plan.prepared.pair plan.first plan.kept pending bounded
  obtain ⟨retained, whole, chosen⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = observed.write.failure.batch) ∧ plan.history = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨_, .inr rfl, whole⟩
  have continued : NativeReadyReadPrefix (seen.opening.finish.run seen.opening.chronology) reached (history ++ retained)
      (log ++ [.uncertainBatch observed.write.failure.batch]) current.reads reached :=
    Eq.mp (congrArg (fun rows => NativeReadyReadPrefix (seen.opening.finish.run seen.opening.chronology) reached rows
      (log ++ [.uncertainBatch observed.write.failure.batch]) current.reads reached) chosen) seed
  let next : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch observed.write.failure.batch]) :=
    ⟨seen.opening.finish.run seen.opening.chronology, reached, reached, current.reads, continued⟩
  refine ⟨retained, next, whole, rfl, ?_, ?_, checkpoint, durable, ?_,
    ⟨chosen, rfl, rfl, continued.frames.1, directory,
      cacheEq, censusEq, owner, directorySlot, ?_, ?_⟩, next.readPrefix.guardedReplay⟩
  · exact fun same => phaseFresh (same.symm ▸ seen.previousTokens.1)
  · exact fun same => sessionFresh (same.symm ▸ seen.previousTokens.2)
  · exact (congrArg DirectoryPublication.Bindings.walBoundary pair).trans
      (plan.marker.trans (congrArg (fun rows => some (WAL.Boundary.encode (WAL.encode rows).size.toUInt64)) chosen))
  · exact seen.lock.trans (effects.crash.lock.trans (effects.census.lockBound.trans
      (congrArg some effects.census.lockInode)))
  · exact seen.directory.trans (effects.crash.directory.trans (effects.census.directoryBound.trans
      (congrArg some effects.census.sameDirectory)))

end Alvoki.Storage.DiskSession
