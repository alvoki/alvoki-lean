import Alvoki.Storage.Disk.RotationLockHandoff
import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation
open WAL (frameSize)

theorem SegmentedWriterState.RetainedReady.rotationInput {directory descriptor} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor)
    (nonempty : state.installed.activeFirst < state.installed.walBytes / frameSize) :
    CanRotate state.wal state.history := by
  have endAt : state.installed.walBytes / frameSize = state.history.length := by
    rw [ready.resumed.bytes, WAL.encode_size, Nat.mul_comm,
      Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  refine ⟨?_, ready.layout.activeEnd, ?_⟩
  · rwa [ready.resumed.keeper, ready.active, endAt, ← ready.layout.activeEnd] at nonempty
  · intro segment present
    exact ((List.pairwise_append.mp ready.layout.ordered).2.2 segment present state.wal.active (by simp)).1

namespace SegmentedWriterState

def rotationInstalled (before : SegmentedWriterState) : Installed :=
  { before.installed with activeFirst := before.installed.walBytes / frameSize }

def rotationFiles (before : SegmentedWriterState) (wal : WalSegmentImage) : FileImage :=
  { wal.checkpointReopenFiles wal.directory before.files.keeper.staged with later := before.files.later }

def rotated (before : SegmentedWriterState) (target : Target) : SegmentedWriterState :=
  ⟨before.rotationInstalled, before.wal.rotated, before.history, before.rotationFiles before.wal.rotated,
    before.published, target, before.checkpoint, before.owners⟩

def SelectsRotation (before : SegmentedWriterState) (target : Target) : Prop :=
  target.pair = before.target.pair ∧ target.first = before.rotationInstalled.activeFirst ∧
    target.trimmed = ByteArray.empty

theorem RetainedReady.rotationAtEnd {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) :
    before.rotationInstalled.activeFirst = before.history.length := by
  change before.installed.walBytes / frameSize = before.history.length
  rw [ready.resumed.bytes, WAL.encode_size, Nat.mul_comm, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]

def RetainedReady.rotationTarget {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) : Target :=
  ⟨before.target.pair, before.target.range, before.target.decoded, before.rotationInstalled.activeFirst,
    by simp [ready.rotationAtEnd, ready.resumed.through], ByteArray.empty, by
      rw [ready.rotationAtEnd, ready.resumed.through, Nat.sub_self, Nat.zero_mul]
      rfl⟩

/-- The retained writer math uses the settled rotation layout. It is
shared by both creation and reuse of a checked empty successor. -/
theorem RetainedReady.rotates {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor)
    (nonempty : before.installed.activeFirst < before.installed.walBytes / frameSize)
    {target : Target} (chosen : before.SelectsRotation target) :
    (before.rotated target).RetainedReady directory descriptor := by
  obtain ⟨pair, first, bytes⟩ := chosen
  have range := Option.some.inj (target.decoded.symm.trans (pair ▸ before.target.decoded))
  have rotation := ready.rotationInput nonempty
  have directoryFiles : (before.rotationFiles before.wal.rotated).directory = before.files.directory :=
    ready.directoryFiles.symm
  have durable : (before.rotationFiles before.wal.rotated).Ready target := by
    refine ⟨?_, ?_, ?_, ?_, ready.resumed.ready.pruned⟩
    · rw [directoryFiles, pair]; exact ready.resumed.ready.selected
    · rw [directoryFiles, pair]; exact ready.resumed.ready.settled
    · change some ByteArray.empty = some target.trimmed
      rw [bytes]
    · change [some ByteArray.empty] = [some target.trimmed]
      rw [bytes]
  have contents : target.trimmed = WAL.encode (before.history.drop target.first) := by
    rw [bytes, first, ready.rotationAtEnd, List.drop_length]
    rfl
  have layout := (⟨before.wal.directory, .durable⟩ : WalSegmentRotation.State).visibleReadLayout rotation ready.layout
  have spans : ∀ segment ∈ before.wal.rotated.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize := by
    intro segment present
    rcases List.mem_append.mp present with sealed | keeper
    · exact ready.spans _ sealed
    · obtain rfl := List.mem_singleton.mp keeper
      rw [ready.layout.activeBytes, WAL.encode_size, List.length_drop, ready.layout.activeEnd, Nat.mul_comm]
  have active : target.first = before.wal.rotated.active.first := by
    rw [first, ready.rotationAtEnd]
    exact rotation.atEnd.symm
  refine ⟨⟨durable, (congrArg MarkedWalRange.through range).trans ready.resumed.through, first.symm, ready.resumed.bytes, contents,
    ready.resumed.generation, ?_, ?_, ready.resumed.ordered, ready.resumed.bounds, ready.resumed.canonical⟩,
    layout, rotation.valid_rotated ready.valid, spans, rfl, rfl, active, ?_, ready.held⟩
  · simpa only [rotated, pair] using ready.resumed.selected
  · simpa only [rotated, pair] using ready.resumed.accepted
  · change before.published.manifest = (before.rotationFiles before.wal.rotated).directory.project .manifest
    rw [directoryFiles]
    exact ready.manifestFiles

end SegmentedWriterState

/-- The successful, nonempty branch of native rotation after the active-file
guard. The complete starting layout has no successor at the history end. -/
structure SegmentedRotationReport (directory : DiskDirectory) (before : SegmentedWriterState) where
  read : FilePath → EStateM IO.Error WalSegmentRotation.State (Option ByteArray)
  create : FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  sync : FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  cut : WalSegmentRotation.State
  nonempty : before.installed.activeFirst < before.installed.walBytes / frameSize
  lookup : read (directory.file (.walSegment (before.installed.walBytes / frameSize))) (.initial before.wal) =
    .ok none (.initial before.wal)
  reports : EffectReports (performPaths directory (before.installed.walBytes / frameSize) create sync)
  ran : runAt directory (before.installed.walBytes / frameSize) read create sync (.initial before.wal) =
    .ok () cut

namespace SegmentedRotationReport

variable {directory : DiskDirectory} {before : SegmentedWriterState}

def nextInstalled (_report : SegmentedRotationReport directory before) : Installed :=
  before.rotationInstalled

def wal (report : SegmentedRotationReport directory before) : WalSegmentImage :=
  report.cut.visible before.wal

def files (report : SegmentedRotationReport directory before) : FileImage :=
  before.rotationFiles report.wal

def next (report : SegmentedRotationReport directory before) (target : Target) : SegmentedWriterState :=
  ⟨report.nextInstalled, report.wal, before.history, report.files, before.published, target, before.checkpoint,
    before.owners⟩

/-- Successful rotation retains the selected metadata and moves the active
start to the empty successor. The unchanged pair fixes the WAL range. -/
def Selects (_report : SegmentedRotationReport directory before) (target : Target) : Prop :=
  before.SelectsRotation target

theorem settled (report : SegmentedRotationReport directory before) :
    report.cut = ⟨before.wal.directory.syncDirectory, .durable⟩ := by
  let initial := WalSegmentRotation.State.initial before.wal
  let action := performPaths directory (before.installed.walBytes / frameSize) report.create report.sync
  have ran : WalSegmentRotation.run false action initial = .ok () report.cut := by
    have succeeded := report.ran
    unfold WalSegmentRotation.runAt observeSuccessorWith at succeeded
    simpa only [Bind.bind, EStateM.bind, report.lookup, Pure.pure, EStateM.pure] using succeeded
  have effects := initial.runObserved_effects false action report.reports
  rw [ran] at effects
  have expected : initial.execute (WalSegmentRotation.steps false) =
      some ⟨before.wal.directory.syncDirectory, .durable⟩ := rfl
  exact Option.some.inj (effects.symm.trans expected)

/-- The shared native publication tail returns with the reported durable
successor, updated phase and the original owner. -/
theorem acknowledges (report : SegmentedRotationReport directory before) :
    runPreparedRotation report.nextInstalled
      (runAt directory (before.installed.walBytes / frameSize) report.read report.create report.sync)
      (.ready before.installed, ⟨.initial before.wal, before.owners⟩) =
      .ok () (.ready report.nextInstalled, ⟨report.cut, before.owners⟩) := by
  simp only [runPreparedRotation, publishPrepared, Bind.bind, EStateM.bind, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, report.ran]

theorem rotatedRetained (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) : report.wal = before.wal.rotated := by
  have sameDirectory : before.wal.directory.syncDirectory = before.wal.directory := by
    rw [DirectoryPublication.Image.syncDirectory, ← ready.walDirectorySettled]
  simp [wal, report.settled, sameDirectory, WalSegmentRotation.State.visible]

theorem rotated (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.Ready directory descriptor) : report.wal = before.wal.rotated :=
  report.rotatedRetained ready.toRetained

private theorem selectTarget (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) : ∃ target, report.Selects target := by
  exact ⟨ready.rotationTarget, rfl, rfl, rfl⟩

/-- Successful creation settles precisely the shared rotated writer. -/
theorem preservesRetainedReady (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) {target : Target} (chosen : report.Selects target) :
    (report.next target).RetainedReady directory descriptor := by
  unfold next files
  rw [report.rotatedRetained ready]
  exact ready.rotates report.nonempty chosen

theorem selectedRetainedReady (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) :
    ∃ target, report.Selects target ∧ (report.next target).RetainedReady directory descriptor := by
  obtain ⟨target, chosen⟩ := report.selectTarget ready
  exact ⟨target, chosen, report.preservesRetainedReady ready chosen⟩

/-- The reported successor uses the absolute history end, and no present
sealed descriptor or old keeper bytes are replaced. -/
theorem retainedIdentities (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) :
    report.wal.sealed = before.wal.sealed ++ [before.wal.active] ∧
      report.wal.active = ⟨before.history.length, before.history.length, ByteArray.empty⟩ ∧
      ∀ segment ∈ before.wal.segments,
        directory.file (.walSegment report.wal.active.first) ≠ directory.file (.walSegment segment.first) := by
  rw [report.rotatedRetained ready]
  refine ⟨rfl, by rw [← ready.layout.activeEnd]; rfl, ?_⟩
  intro segment present
  exact (ready.rotationInput report.nonempty).successorDistinct directory present

/-- For a caller that still holds the entire physical chain, keep that
stronger property as well as the retained writer invariant. -/
theorem preservesReady (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.Ready directory descriptor) {target : Target} (chosen : report.Selects target) :
    (report.next target).Ready directory descriptor := by
  have next := report.preservesRetainedReady ready.toRetained chosen
  have chain := report.cut.visibleChain (ready.rotationInput report.nonempty) ready.chain
  exact ⟨next.resumed, next.layout, chain, next.directoryFiles, next.sealedFiles, next.active, next.manifestFiles, next.held⟩

theorem selectedReady (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.Ready directory descriptor) :
    ∃ target, report.Selects target ∧ (report.next target).Ready directory descriptor := by
  obtain ⟨target, chosen⟩ := report.selectTarget ready.toRetained
  exact ⟨target, chosen, report.preservesReady ready chosen⟩

end SegmentedRotationReport

end Alvoki.Storage.DiskSession
