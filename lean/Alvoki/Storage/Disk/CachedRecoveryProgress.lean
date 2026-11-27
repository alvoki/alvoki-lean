import Alvoki.Storage.Disk.Proofs.Recovery.ListedMarkedFinish
import Alvoki.Storage.Disk.RotationAuthorityRetry

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- A successful cached install fixes the checkpoint and WAL selection.
After observed power loss and any finite bounded retries without writes,
the reached layout still admits the same selection. On a fresh admitted
open, the held reads of the original published runs and the successful
primitive returns of the reached repair branch reinstall the same data. -/
theorem CachedRetryInstalled.completesAfterCrashAndRetries
    {directory : DiskDirectory} {input : FilePath}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history}
    {reported : CachedRetryReadReports directory layout}
    {descriptors : DescriptorInventory} {slot : DescriptorSlot}
    {bindings : FilePath → Option Nat} {published : CheckpointPublication.Image} {liveRefs : List Nat}
    {result : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession}
    (first : CachedRetryInstalled (before := before) reported descriptors slot bindings published liveRefs result)
    {firstSession : SegmentedSession} {firstFinal : LockedFileState FileImage}
    (returned : result = .ok firstSession firstFinal)
    (prepared : Prepared before.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {pair : DirectoryPublication.Bindings} {keeper : Option ByteArray} {later : List Nat}
    (metadataSurvives : pair ∈ firstFinal.image.directory.crashImages)
    (keeperSurvives : keeper ∈ firstFinal.image.keeper.crashImages)
    (laterSurvives : later ∈ firstFinal.image.later.crashImages)
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (· = layout.target)
      ⟨firstFinal.image.crash pair keeper later, firstFinal.owners.set (directory.file .lock) none⟩ retry)
    (reports : ∀ selected : CanonicalKeeperLayout retry.image history,
      selected.target = layout.target → selected.sealed = layout.sealed → selected.keeper = layout.keeper →
      Nonempty (PrimitiveCheckpointHeldOpen input directory selected published)) :
    BoundedReopenTrace directory (· = layout.target) firstFinal retry ∧
      retry.image.directory.active = layout.target.pair ∧
      retry.image.kept = before.image.kept ∧
      ∃ (selected : CanonicalKeeperLayout retry.image history)
        (observed : PrimitiveCheckpointHeldOpen input directory selected published)
        (session : SegmentedSession) (final : LockedFileState FileImage) (installed : Installed),
        selected.target = layout.target ∧ selected.sealed = layout.sealed ∧ selected.keeper = layout.keeper ∧
        Prepared retry.image selected.target selected.plan ∧
        observed.wal.operations.runWithAdmission observed.admission = .ok session final ∧
        firstSession.phase = .ready installed ∧ session.phase = .ready installed ∧
        final.image.Ready layout.target ∧ final.owners.Owns directory observed.calls.slot.description ∧
        CachedRetryInstalled (before := retry) observed.wal.operations.reported observed.calls.descriptors
          observed.calls.slot observed.calls.bindings published observed.calls.liveRefs
          (observed.wal.operations.runWithAdmission observed.admission) := by
  have firstEffects : EffectTrace layout.target before.image firstFinal.image := by
    obtain ⟨_, _, _, _, final, ran, _, _, _, _, _, _, _, _, _, _, _, _, effects, _⟩ := first
    have same := (EStateM.Result.ok.inj (ran.symm.trans returned)).2
    exact same ▸ effects
  have crash : EffectTrace layout.target before.image (firstFinal.image.crash pair keeper later) :=
    .crash firstEffects metadataSurvives keeperSurvives laterSurvives
  have repaired := crash.trans (attempts.effectsAfterFixedAuthority rfl)
  obtain ⟨selected, target, range, _, seals, sameKeeper, kept, nextPrepared⟩ :=
    repaired.canonicalRetryLayout layout prepared
  have readyToRepair : Prepared retry.image selected.target selected.plan := target.symm ▸ nextPrepared
  have sameManifest := congrArg DirectoryPublication.Bindings.manifest (prepared.pair.trans nextPrepared.pair.symm)
  have nextFollowing : ∀ start ∈ ((selected.sealed ++ [selected.keeper]).map WalSegment.first).drop 1,
      selected.range.watermark < start := by
    rw [seals, sameKeeper, range]
    exact following
  obtain ⟨observed⟩ := reports selected target seals sameKeeper
  obtain ⟨_, _, _, second⟩ := observed.wal.installs observed.namespaceMatches observed.rootMatches
    observed.authorization observed.metadata observed.finish.authorized observed.finish.healthyFinish
    observed.admission readyToRepair.keeperPrefix readyToRepair.newer nextFollowing (sameManifest ▸ accepted) ordered
  obtain ⟨earlierSession, _, session, final, installed, left, right, firstPhase, phase⟩ :=
    first.sameInstalled second sameManifest (congrArg WalSegment.first sameKeeper.symm)
  have exactFirst := (EStateM.Result.ok.inj (left.symm.trans returned)).1
  have exactFinal : final.image.Ready layout.target ∧ final.owners.Owns directory observed.calls.slot.description := by
    obtain ⟨_, _, _, _, reached, ran, _, description, _, _, _, _, _, held, _, _, _, ready, _⟩ := second
    have same := (EStateM.Result.ok.inj (ran.symm.trans right)).2
    exact ⟨same ▸ target ▸ ready, same ▸ (description.trans observed.wal.inventoryDescription) ▸ held⟩
  have loss : BoundedReopenTrace directory (· = layout.target) firstFinal
      ⟨firstFinal.image.crash pair keeper later, firstFinal.owners.set (directory.file .lock) none⟩ :=
    .powerLoss .empty metadataSurvives keeperSurvives laterSurvives
  exact ⟨loss.trans attempts,
    nextPrepared.pair, kept, selected, observed, session, final, installed, target, seals, sameKeeper,
    readyToRepair, right, exactFirst ▸ firstPhase, phase, exactFinal.1, exactFinal.2, second⟩

end Alvoki.Storage.DiskSession
