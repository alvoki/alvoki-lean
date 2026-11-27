import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterReopen
import Alvoki.Storage.Disk.WalSealedUnlinkSurvivors

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair)
    (first : left.first = right.first) (trimmed : left.trimmed = right.trimmed) : left = right := by
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases trimmed
  rfl

/-- Install the next retained writer from the precise sealed namespace
chosen by a collection power loss. The model releases the dead owner's
lock. A successful new acquisition and recovery barriers install the same
WAL target, history and strict checkpoint from those surviving files. -/
theorem SegmentedWriterState.RetainedReady.openAfterCollectionPowerLoss {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    {cut : WalSealedUnlinkImage} {pair : DirectoryPublication.Bindings} {sealed : List WalSegment}
    (trace : WalSealedUnlinkTrace state.wal cut)
    (pairSurvives : pair ∈ cut.visible.directory.crashImages) (sealedSurvives : sealed ∈ cut.crashSealed)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (raw : HealthyBoundedWalReports directory
      ((state.owners.release (directory.file .lock) descriptor).set (directory.file .lock) (some nextDescriptor))
      nextDescriptor (cut.crash pair sealed).visible pair state.target.range.watermark
      state.published.durable ByteArray.empty)
    (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let survivors := (cut.crash pair sealed).visible
    let owners := state.owners.release (directory.file .lock) descriptor
    let files := survivors.checkpointReopenFiles survivors.directory none
    sync #[directory.path] files = .ok () files.syncDirectory →
    sync #[directory.file (.walSegment survivors.active.first)] files.syncDirectory =
      .ok () files.syncDirectory.syncKeeper →
    owners (directory.file .lock) = none ∧
    ∃ session final, ∃ next : SegmentedWriterState,
      runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
        (raw.reopen removeFile write sync renameFile) ⟨files, owners⟩ = .ok session final ∧
      session.directory = directory ∧ session.descriptor = nextDescriptor ∧
      session.phase = .ready next.installed ∧ next.files = final.image ∧ next.owners = final.owners ∧
      final.owners = owners.set (directory.file .lock) (some nextDescriptor) ∧
      next.wal = { survivors with directory := final.image.directory } ∧
      next.target = state.target ∧ next.history = state.history ∧ next.checkpoint = state.checkpoint ∧
      next.installed.generation = state.installed.generation ∧ next.published.durable = state.published.durable ∧
      next.RetainedReady directory nextDescriptor := by
  intro survivors owners files syncDirectory syncKeeper
  have released : owners (directory.file .lock) = none := by
    simp [owners, LockOwners.release_owned ready.held, LockOwners.set]
  have acquired : TryLockObserves owners directory (.ok true) := fun _ => released
  have retry := ((trace.powerLoss pairSurvives sealedSurvives).projects ready.layout).1
  obtain ⟨session, final, next, returned, path, descriptor, phase, nextFiles, nextOwners, wal,
    pairEq, history, generation, durable, nextReady⟩ :=
    ready.openAfterCollection retry raw none liveRefs fresh acquired unlock removeFile write sync renameFile
      syncDirectory syncKeeper
  have survivingPair : pair = state.target.pair :=
    (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have selectedNext : SelectedIntegrityCheckpoint state.published.durable pair.manifest next.checkpoint := by
    rw [survivingPair, ← pairEq, ← durable]
    exact nextReady.resumed.selected
  have selectedPrior : SelectedIntegrityCheckpoint state.published.durable pair.manifest state.checkpoint := by
    rw [survivingPair]
    exact ready.resumed.selected
  have checkpoint := Except.ok.inj ((raw.readCheckpoint selectedNext).symm.trans (raw.readCheckpoint selectedPrior))
  have first : next.target.first = state.target.first := by
    rw [nextReady.active, wal]
    exact (congrArg WalSegment.first retry.keepsActive).trans ready.active.symm
  have trimmed : next.target.trimmed = state.target.trimmed := by
    rw [nextReady.resumed.contents, history, first, ready.resumed.contents]
  change runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
    (raw.reopen removeFile write sync renameFile) ⟨files, owners⟩ = .ok session final at returned
  have acquiredOwner : final.owners = owners.set (directory.file .lock) (some nextDescriptor) := by
    have outcome := returned
    rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired] at outcome
    dsimp only at outcome
    cases recovery : raw.reopen removeFile write sync renameFile files with
    | ok opened image =>
      rw [recovery] at outcome
      exact congrArg LockedFileState.owners (EStateM.Result.ok.inj outcome).2.symm
    | error cause image =>
      rw [recovery] at outcome
      cases unlock <;> contradiction
  exact ⟨released, session, final, next, returned, path, descriptor, phase, nextFiles, nextOwners, acquiredOwner,
    wal, sameTarget pairEq first trimmed, history, checkpoint, generation, durable, nextReady⟩

end Alvoki.Storage.DiskSession
