import Alvoki.Storage.Disk.Proofs.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Transfer the proved checkpoint's accepted metadata and WAL read plan to
its reported live image. The active manifest is identical, every physical
crash choice is modeled, and selected indices agree on the actual bytes. -/
theorem CheckpointPowerCut.reopensFromLive {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory writer) (logical publication : Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some logical)
    (live : publication.manifest.active = logical.manifest.active)
    (choices : ∀ binding ∈ publication.manifest.crashImages, binding ∈ logical.manifest.crashImages)
    (agrees : ∀ binding, (binding = publication.manifest.active ∨ binding ∈ publication.manifest.crashImages) →
      SelectedRunsAgree binding publication.durable logical.durable)
    (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry)
    (reads : CheckpointHeldOpen.Reports input directory before retry publication publication) :
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      CheckpointLiveHeldReopened opened session final after := by
  let wal := publication.segmentedCheckpointView before.wal
  let modelWal := logical.segmentedCheckpointView before.wal
  have active : wal.directory.active = modelWal.directory.active :=
    congrArg (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) live
  have modeled (pair : DirectoryPublication.Bindings) (found : wal.Selects pair) :
      modelWal.Selects pair := by
    rcases List.mem_cons.mp found with visible | survived
    · exact List.mem_cons.mpr (.inl (visible.trans active))
    · obtain ⟨binding, included, rfl⟩ := List.mem_map.mp survived
      exact List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨binding, choices binding included, rfl⟩))
  obtain ⟨published, executed, layoutModel, validModel, inputsModel, _⟩ := cut.selectsAcknowledgedHistory ready
  have same := Option.some.inj (executed.symm.trans projected)
  subst published
  have layout : wal.ReadLayout before.history :=
    ⟨layoutModel.ordered, layoutModel.forward, layoutModel.activeEnd, layoutModel.activeBytes⟩
  have valid : wal.Valid before.history := fun pair found => validModel pair (modeled pair found)
  have inputs : ∀ pair, wal.Selects pair →
      publication.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = before.history.length := by
    intro pair found
    obtain ⟨accepted, range, decoded, through⟩ := inputsModel pair (modeled pair found)
    exact ⟨(agrees pair.manifest (Image.selectedManifest found)).acceptsVersioned decoded accepted, range, decoded, through⟩
  obtain ⟨layout, opened, session, final, after, installed, _⟩ :=
    CheckpointHeldOpen.installsAfterRetry ready publication layout valid inputs retry attempts (fun _ => True)
      (fun chosen keeper tail descriptors => by
        obtain ⟨opened⟩ := reads chosen keeper tail descriptors
        exact ⟨opened, trivial⟩)
  exact ⟨layout, opened, session, final, after, installed⟩

end Alvoki.Storage.DiskSession
