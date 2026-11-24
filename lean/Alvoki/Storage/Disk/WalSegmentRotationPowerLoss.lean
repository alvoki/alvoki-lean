import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.RotationReopenTrace
import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRotation
open WAL (frameSize)

/-- The successor lookup has returned absence, and only the listed prefix
of the create and sync callbacks has returned success. The next callback can
have applied its effect before a power loss. The cut also covers the interval
after all callbacks have completed and before the rotation returns. -/
structure RotationInFlightCut (directory : DiskDirectory) (before : SegmentedWriterState) where
  read : FilePath → EStateM IO.Error State (Option ByteArray)
  create : FilePath → EStateM IO.Error State Unit
  sync : FilePath → EStateM IO.Error State Unit
  nonempty : before.installed.activeFirst < before.installed.walBytes / frameSize
  lookup : read (directory.file (.walSegment (before.installed.walBytes / frameSize))) (.initial before.wal) =
    .ok none (.initial before.wal)
  reports : EffectReports (performPaths directory (before.installed.walBytes / frameSize) create sync)
  completed : Nat
  within : completed ≤ (steps false).length
  reached : State
  returned : ((steps false).take completed).forM
    (performPaths directory (before.installed.walBytes / frameSize) create sync) (.initial before.wal) =
      .ok () reached
  image : State
  effect : image = reached ∨ ∃ action, (steps false)[completed]? = some action ∧
    reached.step action = some image

namespace RotationInFlightCut

variable {directory : DiskDirectory} {before : SegmentedWriterState}

/-- The observed read fixes the executable schedule and callbacks used by
the in-flight trace. -/
theorem schedule (cut : RotationInFlightCut directory before) :
    runAt directory (before.installed.walBytes / frameSize) cut.read cut.create cut.sync (.initial before.wal) =
      WalSegmentRotation.run false
        (performPaths directory (before.installed.walBytes / frameSize) cut.create cut.sync) (.initial before.wal) := by
  unfold runAt observeSuccessorWith
  simp only [Bind.bind, EStateM.bind, cut.lookup, Pure.pure, EStateM.pure]

private theorem traceOfSteps {wal : WalSegmentImage} {initial reached : State} {actions : List Step}
    (prior : Trace wal initial) (applied : initial.execute actions = some reached) : Trace wal reached := by
  induction actions generalizing initial with
  | nil => cases applied; exact prior
  | cons action rest ih =>
    change (initial.step action >>= fun next => next.execute rest) = some reached at applied
    cases ran : initial.step action with
    | none => rw [ran] at applied; contradiction
    | some next =>
      rw [ran] at applied
      exact ih (.effect prior ran) applied

/-- The completed callbacks and the next primitive's optional effect
determine the modeled state while the caller still awaits rotation. -/
theorem trace (cut : RotationInFlightCut directory before) : Trace before.wal cut.image := by
  have effects := Publication.run_effects_outcome State.step
    (performPaths directory (before.installed.walBytes / frameSize) cut.create cut.sync) (by
      intro action state
      have report := cut.reports action state
      cases ran : performPaths directory (before.installed.walBytes / frameSize)
        cut.create cut.sync action state <;> simpa only [ran] using report)
    ((steps false).take cut.completed) (State.initial before.wal)
  rw [cut.returned] at effects
  have reached := traceOfSteps Trace.start effects
  rcases cut.effect with unchanged | ⟨_, _, applied⟩
  · exact unchanged.symm ▸ reached
  · exact .effect reached applied

def released (_cut : RotationInFlightCut directory before) (pair : DirectoryPublication.Bindings) (present : Bool) :
    LockedFileState State :=
  ⟨⟨.settled pair, if present then .durable else .absent⟩, before.owners.set (directory.file .lock) none⟩

/-- Power loss during rotation starts the existing successor-aware retry
trace. It clears the local lock owner and chooses the successor's survival
before any projection to a fixed keeper. -/
theorem startsRetry (cut : RotationInFlightCut directory before) {pair : DirectoryPublication.Bindings}
    {present : Bool} (metadata : pair ∈ cut.image.metadata.crashImages)
    (survives : cut.image.successor.MaySurvive present) :
    RotationReopenFailures directory before.wal before.history ⟨cut.image, before.owners⟩ (cut.released pair present) :=
  .powerLoss .empty metadata survives

/-- Both admissible successor outcomes preserve the selected checkpoint and
the full acknowledged WAL. The layout is reselected at the power loss. -/
theorem selectsPriorHistory (cut : RotationInFlightCut directory before) {descriptor : Nat}
    (ready : before.Ready directory descriptor) {pair : DirectoryPublication.Bindings}
    {present : Bool} (metadata : pair ∈ cut.image.metadata.crashImages)
    (survives : cut.image.successor.MaySurvive present) :
    let crashed := (cut.released pair present).image
    let wal := crashed.visible before.wal
    let retained := { before.wal with directory := DirectoryPublication.Image.settled pair }
    Trace before.wal crashed ∧ pair = before.target.pair ∧
      wal = (if present then retained.rotated else retained) ∧
      wal.ReadLayout before.history ∧ WalSegment.Chain before.history 0 wal.segments ∧
      WAL.decodeOrdinals (WalSegment.concatenate wal.segments) = .ok before.history := by
  intro crashed wal retained
  have afterLoss : Trace before.wal crashed := .crash cut.trace pair metadata survives
  have rotation := ready.rotationInput cut.nonempty
  have chosen := cut.trace.selectsOriginal (List.mem_cons_of_mem _ metadata)
  have selected : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using chosen
  have canonical := crashed.visibleChain rotation ready.chain
  refine ⟨afterLoss, selected.trans ?_, ?_, crashed.visibleReadLayout rotation ready.layout, canonical, ?_⟩
  · rw [← ready.directoryFiles]
    exact ready.resumed.ready.selected
  · cases present <;> rfl
  · rw [canonical.concatenate_eq, List.drop_zero]
    exact WAL.decodeOrdinals_encode _ ready.resumed.ordered

end RotationInFlightCut

end Alvoki.Storage.DiskSession
