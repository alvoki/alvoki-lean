import Alvoki.Storage.Disk.SegmentedCollectionStep

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- A retry executes against the exact namespace returned by the prior
attempt, including the sealed lists still admitted after power loss. -/
def SegmentedCollectionReport.runFrom {directory : DiskDirectory} {before : SegmentedWriterState}
    (report : SegmentedCollectionReport directory before) (reached : WalSealedUnlinkImage) :
    EStateM.Result IO.Error WalSealedUnlinkImage Unit :=
  RunCollection.run report.offsets (WalSealedUnlinkImage.performPaths directory report.removeFile report.syncDirectory)
    reached

/-- A failed pass leaves the writer in a collection-only stretch. Keep the
original writer for the logical state and the last callback result for the
physical namespace. Repeated errors never start from a fresh durable list. -/
inductive SegmentedCollectionErrors (directory : DiskDirectory) (before : SegmentedWriterState) :
    WalSealedUnlinkImage → Prop where
  | first (report : SegmentedCollectionReport directory before)
      (returned : report.run = .error cause reached) : SegmentedCollectionErrors directory before reached
  | retry (previous : SegmentedCollectionErrors directory before prior)
      (report : SegmentedCollectionReport directory before)
      (returned : report.runFrom prior = .error cause reached) : SegmentedCollectionErrors directory before reached

private theorem directorySyncFixed {directory : DirectoryPublication.Image}
    (settled : directory.crashImages = [directory.active]) : directory.syncDirectory = directory := by
  cases directory with
  | mk active crashImages staged =>
    change crashImages = [active] at settled
    subst crashImages
    rfl

private theorem fold_keepsDirectory (actions : List (RunCollection.Step Nat)) (before : WalSealedUnlinkImage)
    (settled : before.visible.directory.syncDirectory = before.visible.directory) :
    (actions.foldl WalSealedUnlinkImage.applyCollectionStep before).visible.directory = before.visible.directory := by
  induction actions generalizing before with
  | nil => rfl
  | cons action rest ih =>
    have same : (before.applyCollectionStep action).visible.directory = before.visible.directory := by
      cases action with
      | unlink first =>
        change (before.unlink first).visible.directory = before.visible.directory
        unfold WalSealedUnlinkImage.unlink
        split <;> rfl
      | syncDirectory => exact settled
    exact (ih (before.applyCollectionStep action) (same.symm ▸ settled)).trans same

private theorem SegmentedCollectionReport.errorCut {directory : DiskDirectory} {before : SegmentedWriterState}
    (report : SegmentedCollectionReport directory before) {prior reached : WalSealedUnlinkImage}
    (trace : WalSealedUnlinkTrace before.wal prior) (settled : prior.visible.directory.syncDirectory = prior.visible.directory)
    {cause : IO.Error} (returned : report.runFrom prior = .error cause reached) :
    WalSealedUnlinkTrace before.wal reached ∧ reached.visible.directory = prior.visible.directory := by
  have executed := trace.runPaths directory report.offsets report.approved report.removeFile report.syncDirectory report.effects
  dsimp only at executed
  unfold SegmentedCollectionReport.runFrom at returned
  rw [returned] at executed
  obtain ⟨cut, reachedAt, exactTrace⟩ := executed
  exact ⟨exactTrace, reachedAt.symm ▸ fold_keepsDirectory ((RunCollection.steps report.offsets).take cut) prior settled⟩

namespace SegmentedCollectionErrors

variable {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState} {reached : WalSealedUnlinkImage}

/-- Until a reported barrier or a power-loss observation takes over,
every result is the exact error prefix, with the same metadata directory
and the sealed crash choices produced by that prefix. -/
theorem keepsNamespace (failed : SegmentedCollectionErrors directory before reached)
    (ready : before.RetainedReady directory descriptor) :
    WalSealedUnlinkTrace before.wal reached ∧ reached.visible.directory = before.wal.directory := by
  have settled := directorySyncFixed ready.walDirectorySettled
  induction failed with
  | first report returned => exact report.errorCut .start settled returned
  | retry _ report returned earlier =>
    obtain ⟨trace, beforeDir⟩ := earlier
    obtain ⟨reached, sameDir⟩ := report.errorCut trace (beforeDir.symm ▸ settled) returned
    exact ⟨reached, sameDir.trans beforeDir⟩

/-- Each physically admitted seal list after a reported error still selects
the original validated reads. The same holds for the visible namespace. -/
theorem keepsReadDescriptors (failed : SegmentedCollectionErrors directory before reached)
    (ready : before.RetainedReady directory descriptor) :
    reached.visible.readDescriptors before.target.range.watermark = before.wal.readDescriptors before.target.range.watermark ∧
      ∀ sealed ∈ reached.crashSealed,
        ({ reached.visible with sealed }).readDescriptors before.target.range.watermark =
          before.wal.readDescriptors before.target.range.watermark := by
  obtain ⟨trace, sameDir⟩ := failed.keepsNamespace ready
  have ⟨visible, allowed⟩ := trace.projects ready.layout
  have selected : reached.visible.Selects before.target.pair := by
    rw [WalSegmentImage.Selects, sameDir, ready.walPair]
    exact List.mem_cons_self ..
  refine ⟨visible.keepsReadDescriptors selected before.target.decoded, ?_⟩
  intro sealed admitted
  exact (allowed sealed admitted).keepsReadDescriptors selected before.target.decoded

/-- A successful retry performs the shared final directory barrier. Only
then can the original held writer install the surviving catalog and leave
the collection-only stretch. Empty retry plans still perform the barrier. -/
theorem settles (failed : SegmentedCollectionErrors directory before reached)
    (ready : before.RetainedReady directory descriptor) (report : SegmentedCollectionReport directory before)
    {remaining : WalSealedUnlinkImage} (returned : report.runFrom reached = .ok () remaining) :
    remaining.crashSealed = [remaining.visible.sealed] ∧
    ∃ next : SegmentedWriterState,
      next.wal = remaining.visible ∧ next.history = before.history ∧ next.installed = before.installed ∧
      next.target = before.target ∧ next.checkpoint = before.checkpoint ∧ next.owners = before.owners ∧
      next.RetainedReady directory descriptor := by
  obtain ⟨trace, sameDir⟩ := failed.keepsNamespace ready
  have executed := trace.runPaths directory report.offsets report.approved report.removeFile report.syncDirectory report.effects
  dsimp only at executed
  unfold SegmentedCollectionReport.runFrom at returned
  rw [returned] at executed
  obtain ⟨complete, finalTrace⟩ := executed
  have settled := directorySyncFixed ready.walDirectorySettled
  have directoryFixed : remaining.visible.directory = before.wal.directory :=
    (complete ▸ fold_keepsDirectory (RunCollection.steps report.offsets) reached (sameDir.symm ▸ settled)).trans sameDir
  have durable : remaining.crashSealed = [remaining.visible.sealed] := by
    rw [complete, RunCollection.steps, List.foldl_append]
    rfl
  have retry := (finalTrace.projects ready.layout).1
  let next := { before with
    wal := remaining.visible
    files := { before.files with kept := (remaining.visible.checkpointReopenFiles remaining.visible.directory none).kept } }
  refine ⟨durable, next, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨{ ready.resumed with ready := {
      selected := ready.resumed.ready.selected
      settled := ready.resumed.ready.settled
      keeper := ready.resumed.ready.keeper
      keeperDurable := ready.resumed.ready.keeperDurable
      pruned := ready.resumed.ready.pruned } },
    retry.readLayout ready.layout, retry.valid ready.valid,
    fun segment member => ready.spans segment (retry.sealedSublist.subset member),
    ready.directoryFiles.trans directoryFixed.symm, rfl,
    ready.active.trans (congrArg WalSegment.first retry.keepsActive).symm, ready.manifestFiles, ready.held⟩

end SegmentedCollectionErrors
end Alvoki.Storage.DiskSession
