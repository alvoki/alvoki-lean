import Alvoki.Storage.Disk.SegmentedDatabaseTrace

namespace Alvoki.Storage

/-- A sealed segment came from a nonempty keeper. The current keeper is
allowed to be empty, and collection can leave gaps between seals. -/
def WalSegmentImage.PositiveSeals (wal : WalSegmentImage) : Prop :=
  ∀ segment ∈ wal.sealed, segment.first < segment.last

theorem WalSegmentImage.PositiveSeals.ofSublist {before after : WalSegmentImage}
    (previous : before.PositiveSeals) (retained : after.sealed.Sublist before.sealed) : after.PositiveSeals :=
  fun segment member => previous segment (retained.subset member)

theorem WalSegmentImage.PositiveSeals.rotated {before : WalSegmentImage}
    (previous : before.PositiveSeals) (active : before.active.first < before.active.last) :
    before.rotated.PositiveSeals := by
  intro segment member
  rcases List.mem_append.mp member with sealed | keeper
  · exact previous segment sealed
  · exact List.mem_singleton.mp keeper ▸ active

theorem WalSegmentRotation.State.positiveSeals_visible (state : State) {wal : WalSegmentImage}
    (positive : wal.PositiveSeals) (active : wal.active.first < wal.active.last) : (state.visible wal).PositiveSeals := by
  unfold State.visible
  split
  · exact positive
  · exact positive.rotated active

namespace DiskSession

open WalSegmentRepair WalSegmentRotation

theorem SegmentedAppendTrace.keepsSealedWal {directory descriptor initial events last}
    (trace : SegmentedAppendTrace directory descriptor initial events last) : last.wal.sealed = initial.wal.sealed := by
  induction trace with
  | empty => rfl
  | append _ _ _ previous => exact previous

theorem SegmentedWriterTrace.keepsSealedWal {directory descriptor initial writes checkpoints last}
    (trace : SegmentedWriterTrace directory descriptor initial writes checkpoints last) :
    last.wal.sealed = initial.wal.sealed := by
  induction trace with
  | empty => rfl
  | appends _ appended previous => exact appended.keepsSealedWal.trans previous
  | checkpoint _ _ _ installed previous =>
    rw [installed.wal]
    exact previous
  | table _ _ previous => exact previous

/-- The ordinary trace preserves positive sealed spans through each
operation and retry, even when earlier successful collections left gaps. -/
theorem SegmentedDatabaseTrace.preservesPositiveSeals {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) (positive : initial.wal.PositiveSeals) :
    last.wal.PositiveSeals := by
  induction trace with
  | start => exact positive
  | writes _ writer ih => exact fun segment member => ih segment (writer.keepsSealedWal ▸ member)
  | rotate prior report selected ih =>
    have current := (prior.preservesRetained ready).1
    change report.wal.PositiveSeals
    rw [report.rotatedRetained current]
    exact ih.rotated (current.rotationInput report.nonempty).nonempty
  | close _ _ _ endpoint ih =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := endpoint.openEffect
    exact ih
  | powerLoss _ _ _ endpoint ih =>
    obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.openEffect
    exact ih
  | appendError _ _ endpoint ih =>
    rw [endpoint.wal]
    exact ih
  | delayedDirectoryAppend _ _ _ _ _ _ _ _ endpoint _ ih =>
    rw [endpoint.wal]
    exact ih
  | delayedKeeperPowerLoss _ _ _ _ _ _ _ endpoint _ _ ih =>
    rw [endpoint.wal]
    exact ih
  | appendPowerLoss _ _ _ endpoint ih =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := endpoint.openEffect
    exact ih
  | markerPowerLoss _ _ _ endpoint ih =>
    rw [endpoint.wal]
    exact ih
  | checkpointError _ _ endpoint ih =>
    rw [endpoint.wal]
    exact ih
  | checkpointPowerLoss _ _ _ endpoint ih =>
    rw [endpoint.wal]
    exact ih
  | rotationError prior report _ _ endpoint ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨_, final, _, _, _, _, _, wal, _⟩ := endpoint.returned
    rw [wal]
    exact final.image.positiveSeals_visible ih (current.rotationInput report.failure.nonempty).nonempty
  | rotationPowerLoss prior report endpoint ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨_, final, _, _, _, _, _, wal, _⟩ := endpoint.reopened.returned
    rw [wal]
    exact final.image.positiveSeals_visible ih (current.rotationInput report.cut.nonempty).nonempty
  | collectionPowerLoss _ prior report _ endpoint ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.opened
    exact ih.ofSublist ((report.reached.projects current.layout).2 report.sealed report.sealedSurvives).sealedSublist
  | collection _ prior report endpoint ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨remaining, result, rfl⟩ := endpoint
    have ran := (WalSealedUnlinkTrace.start (initial := _)).runPaths directory report.offsets
      report.approved report.removeFile report.syncDirectory report.effects
    unfold SegmentedCollectionReport.run SegmentedCollectionReport.runFrom at result
    dsimp only at ran
    rw [result] at ran
    exact ih.ofSublist (ran.2.projects current.layout).1.sealedSublist
  | collectionRetry _ prior failed report result ih =>
    have current := (prior.preservesRetained ready).1
    have reached := (failed.keepsNamespace current).1
    have ran := reached.runPaths directory report.offsets report.approved report.removeFile report.syncDirectory report.effects
    unfold SegmentedCollectionReport.runFrom at result
    dsimp only at ran
    rw [result] at ran
    exact ih.ofSublist (ran.2.projects current.layout).1.sealedSublist
  | collectionReopen _ prior report _ endpoint ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.opened
    have reached := report.attempts.continues (report.failed.keepsNamespace current).1
    exact ih.ofSublist (reached.projects current.layout).1.sealedSublist
  | collectRuns _ _ _ ih => exact ih

/-- Real bootstrap installs an empty keeper and no sealed segments. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.BootstrapReady.positiveSeals_writer
    {after : WalSegmentRotation.State} (bootstrap : BootstrapReady after) (owners : LockOwners) :
    (bootstrap.writerState owners).wal.PositiveSeals := by
  intro segment member
  exact False.elim (List.not_mem_nil member)

end DiskSession
end Alvoki.Storage
