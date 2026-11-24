import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.WalSealedUnlinkSurvivors

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem foldUnlinks_directory (offsets : List Nat) (before : WalSealedUnlinkImage) :
    ((offsets.map RunCollection.Step.unlink).foldl WalSealedUnlinkImage.applyCollectionStep before).visible.directory =
      before.visible.directory := by
  induction offsets generalizing before with
  | nil => rfl
  | cons first rest ih =>
    change ((rest.map RunCollection.Step.unlink).foldl WalSealedUnlinkImage.applyCollectionStep
      (before.unlink first)).visible.directory = before.visible.directory
    rw [ih]
    unfold WalSealedUnlinkImage.unlink
    split <;> rfl

private theorem completedCollection (offsets : List Nat) (before : WalSealedUnlinkImage)
    (settled : before.visible.directory.crashImages = [before.visible.directory.active]) :
    let after := (RunCollection.steps offsets).foldl WalSealedUnlinkImage.applyCollectionStep before
    after.visible.directory = before.visible.directory ∧ after.crashSealed = [after.visible.sealed] := by
  let unlinked := (offsets.map RunCollection.Step.unlink).foldl WalSealedUnlinkImage.applyCollectionStep before
  have afterEq : (RunCollection.steps offsets).foldl WalSealedUnlinkImage.applyCollectionStep before =
      unlinked.syncDirectory := by
    rw [RunCollection.steps, List.foldl_append]
    rfl
  dsimp only
  rw [afterEq]
  refine ⟨?_, rfl⟩
  change unlinked.visible.directory.syncDirectory = before.visible.directory
  rw [foldUnlinks_directory]
  cases directory : before.visible.directory
  rw [directory] at settled
  simp only [DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.mk.injEq, true_and, and_true]
  exact settled.symm

/-- Reports for a pass of the shared unlink dispatcher in the held
directory. The inventory planner supplies the approved canonical offsets. -/
structure SegmentedCollectionReport (directory : DiskDirectory) (before : SegmentedWriterState) where
  offsets : List Nat
  approved : ∀ first ∈ offsets, first ∈ before.wal.collectionOffsets
  removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)
  syncDirectory : FilePath → EStateM IO.Error WalSealedUnlinkImage Unit
  effects : WalSealedUnlinkReports directory removeFile syncDirectory

namespace SegmentedCollectionReport

variable {directory : DiskDirectory} {before : SegmentedWriterState}

def run (report : SegmentedCollectionReport directory before) :
    EStateM.Result IO.Error WalSealedUnlinkImage Unit :=
  RunCollection.run report.offsets (WalSealedUnlinkImage.performPaths directory report.removeFile report.syncDirectory)
    (.start before.wal)

private def afterCollection (before : SegmentedWriterState) (remaining : WalSealedUnlinkImage) :
    SegmentedWriterState :=
  { before with
    wal := remaining.visible
    files := { before.files with
      kept := (remaining.visible.checkpointReopenFiles remaining.visible.directory none).kept } }

/-- A successful call installs the exact remaining sealed inventory in the
same writer. The in-memory table and held owner come from the prior state. -/
def Installs (report : SegmentedCollectionReport directory before) (after : SegmentedWriterState) : Prop :=
  ∃ remaining, report.run = .ok () remaining ∧ after = afterCollection before remaining

theorem Installs.unique {report : SegmentedCollectionReport directory before} {left right : SegmentedWriterState}
    (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, leftReturned, rfl⟩ := a
  obtain ⟨_, rightReturned, rfl⟩ := b
  rw [(EStateM.Result.ok.inj (leftReturned.symm.trans rightReturned)).2]

theorem Installs.history {report : SegmentedCollectionReport directory before} {after : SegmentedWriterState}
    (installed : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, rfl⟩ := installed
  rfl

/-- On a successful shared dispatch, the final directory barrier settles
the exact remaining sealed names, including when the unlink list was empty.
The active keeper, metadata, checkpoint and owned installed writer persist. -/
theorem Installs.outcome {report : SegmentedCollectionReport directory before} {after : SegmentedWriterState}
    (installed : report.Installs after) {descriptor : Nat} (ready : before.RetainedReady directory descriptor) :
    after.RetainedReady directory descriptor ∧ after.wal.directory = before.wal.directory ∧
      after.wal.active = before.wal.active ∧ after.installed = before.installed ∧ after.target = before.target ∧
      after.checkpoint = before.checkpoint ∧ after.owners = before.owners ∧
      ∃ remaining, report.run = .ok () remaining ∧ remaining.visible = after.wal ∧
        remaining.crashSealed = [after.wal.sealed] := by
  obtain ⟨remaining, ran, rfl⟩ := installed
  have reached := (WalSealedUnlinkTrace.start (initial := before.wal)).runPaths directory report.offsets
    report.approved report.removeFile report.syncDirectory report.effects
  dsimp only at reached
  have dispatch := ran
  unfold SegmentedCollectionReport.run at dispatch
  rw [dispatch] at reached
  obtain ⟨complete, trace⟩ := reached
  have retry := (trace.projects ready.layout).1
  have ⟨sameDirectory, settled⟩ := complete ▸
    completedCollection report.offsets (.start before.wal) ready.walDirectorySettled
  refine ⟨?_, sameDirectory, retry.keepsActive, rfl, rfl, rfl, rfl, remaining, ran, rfl, settled⟩
  exact ⟨{ ready.resumed with ready := {
      selected := ready.resumed.ready.selected
      settled := ready.resumed.ready.settled
      keeper := ready.resumed.ready.keeper
      keeperDurable := ready.resumed.ready.keeperDurable
      pruned := ready.resumed.ready.pruned } },
    retry.readLayout ready.layout, retry.valid ready.valid,
    fun segment member => ready.spans segment (retry.sealedSublist.subset member),
    ready.directoryFiles.trans sameDirectory.symm, rfl,
    ready.active.trans (congrArg WalSegment.first retry.keepsActive).symm, ready.manifestFiles, ready.held⟩

theorem Installs.preservesRetained {report : SegmentedCollectionReport directory before} {after : SegmentedWriterState}
    (installed : report.Installs after) {descriptor : Nat} (ready : before.RetainedReady directory descriptor) :
    after.RetainedReady directory descriptor :=
  (installed.outcome ready).1

end SegmentedCollectionReport
end Alvoki.Storage.DiskSession
