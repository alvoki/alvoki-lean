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
  { before.installed with activeFirst := before.installed.walBytes / frameSize }

def wal (report : SegmentedRotationReport directory before) : WalSegmentImage :=
  report.cut.visible before.wal

def files (report : SegmentedRotationReport directory before) : FileImage :=
  { report.wal.checkpointReopenFiles report.wal.directory before.files.keeper.staged with later := before.files.later }

def next (report : SegmentedRotationReport directory before) (target : Target) : SegmentedWriterState :=
  ⟨report.nextInstalled, report.wal, before.history, report.files, before.published, target, before.checkpoint,
    before.owners⟩

/-- Successful rotation retains the selected metadata and moves the active
start to the empty successor. The unchanged pair fixes the WAL range. -/
def Selects (report : SegmentedRotationReport directory before) (target : Target) : Prop :=
  target.pair = before.target.pair ∧ target.first = report.nextInstalled.activeFirst ∧ target.trimmed = ByteArray.empty

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

private theorem successorAtEnd (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) :
    report.nextInstalled.activeFirst = before.history.length := by
  change before.installed.walBytes / frameSize = before.history.length
  rw [ready.resumed.bytes, WAL.encode_size, Nat.mul_comm,
    Nat.mul_div_cancel _ (by decide : 0 < frameSize)]

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
  have atEnd := report.successorAtEnd ready
  let target : Target := ⟨before.target.pair, before.target.range, before.target.decoded,
    report.nextInstalled.activeFirst, by simp [atEnd, ready.resumed.through], ByteArray.empty, by
      rw [atEnd, ready.resumed.through, Nat.sub_self, Nat.zero_mul]
      rfl⟩
  exact ⟨target, rfl, rfl, rfl⟩

/-- Rotate under the retained writer invariant, with the same logical history
and checkpoint. The old keeper joins the exact surviving sealed inventory
and the empty successor becomes the new keeper. -/
theorem preservesRetainedReady (report : SegmentedRotationReport directory before) {descriptor : Nat}
    (ready : before.RetainedReady directory descriptor) {target : Target} (chosen : report.Selects target) :
    (report.next target).RetainedReady directory descriptor := by
  obtain ⟨pair, first, bytes⟩ := chosen
  have range := Option.some.inj (target.decoded.symm.trans (pair ▸ before.target.decoded))
  have atEnd := report.successorAtEnd ready
  have rotation := ready.rotationInput report.nonempty
  have wal := report.rotatedRetained ready
  have directoryFiles : report.files.directory = before.files.directory := by
    change report.wal.directory = before.files.directory
    rw [wal]
    exact ready.directoryFiles.symm
  have emptyBytes : report.wal.active.bytes = ByteArray.empty := by rw [wal]; rfl
  have durable : report.files.Ready target := by
    refine ⟨?_, ?_, ?_, ?_, ready.resumed.ready.pruned⟩
    · rw [directoryFiles, pair]; exact ready.resumed.ready.selected
    · rw [directoryFiles, pair]; exact ready.resumed.ready.settled
    · change some report.wal.active.bytes = some target.trimmed
      rw [emptyBytes, bytes]
    · change [some report.wal.active.bytes] = [some target.trimmed]
      rw [emptyBytes, bytes]
  have contents : target.trimmed = WAL.encode (before.history.drop target.first) := by
    rw [bytes, first, atEnd, List.drop_length]
    rfl
  have layout := report.cut.visibleReadLayout rotation ready.layout
  have valid : report.wal.Valid before.history := wal.symm ▸ rotation.valid_rotated ready.valid
  have spans : ∀ segment ∈ report.wal.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize := by
    intro segment present
    rw [wal] at present
    rcases List.mem_append.mp present with sealed | keeper
    · exact ready.spans _ sealed
    · obtain rfl := List.mem_singleton.mp keeper
      rw [ready.layout.activeBytes, WAL.encode_size, List.length_drop, ready.layout.activeEnd, Nat.mul_comm]
  have active : target.first = report.wal.active.first := by
    rw [first, atEnd, wal]
    exact rotation.atEnd.symm
  refine ⟨⟨durable, (congrArg MarkedWalRange.through range).trans ready.resumed.through, first.symm, ready.resumed.bytes, contents,
    ready.resumed.generation, ?_, ?_, ready.resumed.ordered, ready.resumed.bounds, ready.resumed.canonical⟩,
    layout, valid, spans, rfl, rfl, active, ?_, ready.held⟩
  · simpa only [next, pair] using ready.resumed.selected
  · simpa only [next, pair] using ready.resumed.accepted
  · change before.published.manifest = report.files.directory.project .manifest
    rw [directoryFiles]
    exact ready.manifestFiles

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
