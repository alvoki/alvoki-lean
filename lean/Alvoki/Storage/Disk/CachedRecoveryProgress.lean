import Alvoki.Storage.Disk.DiskOpenAdmission
import Alvoki.Storage.Disk.RotationAuthorityRetry

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- A successful cached install fixes the checkpoint and WAL selection.
After observed power loss and any finite bounded retries without writes,
the reached layout still admits the same selection. Fresh healthy
admission, reads and repair reports then reinstall the exact same data.
The run map in the fresh reports is the one selected by the first open. -/
theorem CachedRetryInstalled.completesAfterCrashAndRetries
    {files : Type} {directory : DiskDirectory} {input : FilePath}
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
    (healthy : ∀ selected : CanonicalKeeperLayout retry.image history,
      selected.target = layout.target → selected.sealed = layout.sealed → selected.keeper = layout.keeper →
      ∃ observed : MarkedRetryChunkReports files directory selected published,
        Nonempty (OpenAdmissionReports input directory observed.slot)) :
    BoundedReopenTrace directory (· = layout.target) firstFinal retry ∧
      retry.image.directory.active = layout.target.pair ∧
      retry.image.kept = before.image.kept ∧
      ∃ (selected : CanonicalKeeperLayout retry.image history)
        (observed : MarkedRetryChunkReports files directory selected published)
        (admission : OpenAdmissionReports input directory observed.slot)
        (session : SegmentedSession) (final : LockedFileState FileImage) (installed : Installed),
        selected.target = layout.target ∧ selected.sealed = layout.sealed ∧ selected.keeper = layout.keeper ∧
        Prepared retry.image selected.target selected.plan ∧
        observed.runWithAdmission admission = .ok session final ∧
        firstSession.phase = .ready installed ∧ session.phase = .ready installed ∧
        final.image.Ready layout.target ∧ final.owners.Owns directory observed.slot.description ∧
        CachedRetryInstalled (before := retry) observed.reported observed.descriptors observed.slot
          observed.bindings published observed.liveRefs (observed.runWithAdmission admission) := by
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
  obtain ⟨observed, ⟨admission⟩⟩ := healthy selected target seals sameKeeper
  have second := runOpenWithAdmission_markedRetryFromChunks observed admission readyToRepair.keeperPrefix
    readyToRepair.newer nextFollowing (sameManifest ▸ accepted) ordered
  obtain ⟨earlierSession, _, session, final, installed, left, right, firstPhase, phase⟩ :=
    first.sameInstalled second sameManifest (congrArg WalSegment.first sameKeeper.symm)
  have exactFirst := (EStateM.Result.ok.inj (left.symm.trans returned)).1
  have exactFinal : final.image.Ready layout.target ∧ final.owners.Owns directory observed.slot.description := by
    obtain ⟨_, _, _, _, reached, ran, _, description, _, _, _, _, _, held, _, _, _, ready, _⟩ := second
    have same := (EStateM.Result.ok.inj (ran.symm.trans right)).2
    exact ⟨same ▸ target ▸ ready, same ▸ (description.trans observed.inventoryDescription) ▸ held⟩
  have loss : BoundedReopenTrace directory (· = layout.target) firstFinal
      ⟨firstFinal.image.crash pair keeper later, firstFinal.owners.set (directory.file .lock) none⟩ :=
    .powerLoss .empty metadataSurvives keeperSurvives laterSurvives
  exact ⟨loss.trans attempts,
    nextPrepared.pair, kept, selected, observed, admission, session, final, installed, target, seals, sameKeeper,
    readyToRepair, right, exactFirst ▸ firstPhase, phase, exactFinal.1, exactFinal.2, second⟩

end Alvoki.Storage.DiskSession
