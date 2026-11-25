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
  observe : ∀ chosen, ∀ layout : CanonicalKeeperLayout crash.retry.image chosen,
    (chosen = state.writer.history ∨ chosen = state.writer.history ++ write.failure.batch) →
    Prepared crash.retry.image layout.target layout.plan →
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
        crash.retry.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeUncertainWriteCrashReads crash input layout selected)

structure NativeUncertainWriteCrashObservation (state : NativeReadyState) (input : FilePath) where
  write : NativeReadyWriteFailure state
  inspect : ∀ cache, write.returnedAt cache → Nonempty (NativeUncertainWriteCrashEffects write cache input)

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
    ∃ cache, observed.write.returnedAt cache ∧
      ∃ (effects : NativeUncertainWriteCrashEffects observed.write cache input)
        (layout : CanonicalKeeperLayout effects.crash.retry.image (history ++ retained))
        (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          effects.crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
        (reads : NativeUncertainWriteCrashReads effects.crash input layout selected),
        effects.crash.reboot.slots = [] ∧
        next.opened = reads.opening.finish.run reads.opening.chronology ∧
        next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
        next.state.session.directory = current.state.session.directory ∧
        next.state.cache = reads.opening.admission.cache ∧ next.state.census = reads.opening.finish.census ∧
        next.state.owner = reads.opening.admission.owner ∧ next.state.directorySlot = reads.opening.admission.cached ∧
        reads.opening.reads.bindings (current.state.session.directory.file .lock) =
          some (current.state.census.inode current.state.owner.description) ∧
        reads.opening.reads.bindings current.state.session.directory.path =
          some (current.state.census.inode current.state.directorySlot.description)
  replay : InstalledClientReplay (log ++ [.uncertainBatch observed.write.failure.batch]) current.reads
    (history ++ retained) next.state.writer.installed next.state.session

theorem NativeReadPosition.recoversUncertainWriteAfterPowerLoss (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeUncertainWriteCrashObservation current.state input) :
    ∃ retained next, NativeUncertainWriteCrashContinuation current observed retained next := by
  obtain ⟨valid, earlierHistory, replay⟩ := current.readPrefix.refines
  obtain ⟨cache, returned⟩ := observed.write.returnsUnknown valid
  obtain ⟨effects⟩ := observed.inspect cache returned
  obtain ⟨_, kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, first, descriptors, offsets,
    prepared, accepted, ordered⟩ := observed.write.failure.refinesReopenPrefixWithWal valid.retained effects.crash.reported
  have manifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair)
  let selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      effects.crash.retry.image.directory.active.manifest current.state.writer.checkpoint :=
    manifest.symm ▸ valid.retained.resumed.selected
  obtain ⟨seen⟩ := effects.observe chosen layout allowed prepared selected
  have allowed : chosen = history ∨ chosen = history ++ observed.write.failure.batch :=
    allowed.imp (·.trans earlierHistory)
      (·.trans (congrArg (· ++ observed.write.failure.batch) earlierHistory))
  obtain ⟨pending, bounded⟩ := replay.appendUncertain current.readPrefix.readsBounded allowed ordered
  obtain ⟨reached, seed, cacheEq, censusEq, owner, directorySlot, pair, durable, checkpoint, directory, _, _,
    phaseFresh, sessionFresh⟩ :=
    seen.opening.finish.startsNativeReadPrefix seen.opening.chronology seen.opening.markerFound prepared
      (seen.opening.reads.walReads.selectedAfterWatermark offsets descriptors) accepted ordered walLayout walValid
      valid.retained.spans prepared.pair first kept pending bounded
  obtain ⟨retained, whole, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = observed.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨_, .inr rfl, whole⟩
  let next : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch observed.write.failure.batch]) :=
    ⟨seen.opening.finish.run seen.opening.chronology, reached, reached, current.reads, seed⟩
  refine ⟨retained, next, whole, rfl, ?_, ?_, checkpoint, durable,
    (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    ⟨cache, returned, effects, layout, selected, seen, rfl, rfl, seed.frames.1, directory,
      cacheEq, censusEq, owner, directorySlot, ?_, ?_⟩, next.readPrefix.guardedReplay⟩
  · exact fun same => phaseFresh (same.symm ▸ seen.previousTokens.1)
  · exact fun same => sessionFresh (same.symm ▸ seen.previousTokens.2)
  · exact seen.lock.trans (effects.crash.lock.trans (effects.census.lockBound.trans
      (congrArg some effects.census.lockInode)))
  · exact seen.directory.trans (effects.crash.directory.trans (effects.census.directoryBound.trans
      (congrArg some effects.census.sameDirectory)))

end Alvoki.Storage.DiskSession
