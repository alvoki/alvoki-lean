import Alvoki.Storage.Disk.Proofs.WAL.WalBatchMarkerPowerLoss
import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- A batch reached an in-flight marker callback with the writer still
holding the lock. The report records the completed prefix and the files
chosen by machine power loss. -/
structure SegmentedBatchMarkerPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer : Nat) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  cut : MarkerInterruption
  appendCrashTails : List ByteArray
  activeMetadata : FilePath → Except IO.Error IO.FS.Metadata
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  pair : DirectoryPublication.Bindings
  keeper : ByteArray

namespace SegmentedBatchMarkerPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}

def nextBytes (report : SegmentedBatchMarkerPowerLossReport directory before writer) : Nat :=
  before.installed.walBytes + WAL.frameSize * report.rows.length

def reached (report : SegmentedBatchMarkerPowerLossReport directory before writer) : WriteFiles :=
  report.cut.reachedBatch before.history report.batch report.appendCrashTails (before.wal.directory.staged .walBoundary)

/-- Project the in-flight marker effect while preserving the prior manifest,
sealed WAL, and unrelated scratch. -/
def physical (report : SegmentedBatchMarkerPowerLossReport directory before writer) : FileImage :=
  let marker := WAL.Boundary.encode (WAL.encode (before.history ++ report.batch)).size.toUInt64
  let actual := report.cut.interrupt marker report.reached
  let observed := actual.reopenImage (before.history.drop before.wal.active.first)
    before.wal.directory.active.manifest (before.wal.directory.staged .manifest) before.files.keeper.staged
  before.wal.appendReopenFiles observed before.files.keeper.staged

def inFlight (report : SegmentedBatchMarkerPowerLossReport directory before writer) : LockedFileState FileImage :=
  ⟨report.physical, before.owners⟩

def crashed (report : SegmentedBatchMarkerPowerLossReport directory before writer) : LockedFileState FileImage :=
  ⟨report.physical.crash report.pair (some report.keeper) [], before.owners.set (directory.file .lock) none⟩

def modeled (report : SegmentedBatchMarkerPowerLossReport directory before writer) : LockedFileState FileImage :=
  let scratch := before.wal.directory.staged .walBoundary
  let cut := writeFilesAfter (runBatchEffects before.history report.batch
    (report.cut.writeEffects report.appendCrashTails scratch) scratch)
  ⟨before.wal.appendReopenFiles
    (cut.reopenSegment before.wal.active.first before.history before.wal.directory.active.manifest)
    before.files.keeper.staged, before.owners⟩

/-- The operation reached marker publication. Machine power loss adds
survivor observations, while process exit keeps the live file image. -/
structure Reached (report : SegmentedBatchMarkerPowerLossReport directory before writer) : Prop where
  prepared : prepareBatch before.installed.table report.rows = some (report.batch, report.table)
  nonempty : report.rows ≠ []
  fits : report.nextBytes < UInt64.size
  activeGuard : ∃ metadata,
    report.activeMetadata (directory.file (.walSegment before.installed.activeFirst)) = .ok metadata ∧
    metadata.type = .file ∧ metadata.numLinks = 1 ∧
    metadata.byteSize.toNat = before.installed.walBytes - before.installed.activeFirst * WAL.frameSize
  reachedPrefix : commit (report.append (directory.file (.walSegment before.installed.activeFirst))
      (WAL.encodeBatch report.batch))
      ((Publication.steps.take report.cut.index).forM
        (performMarkerAt directory before.installed.activeFirst report.nextBytes report.stage report.sync report.rename))
      (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) = .ok () report.reached

structure Valid (report : SegmentedBatchMarkerPowerLossReport directory before writer) : Prop extends Reached report where
  pairSurvives : report.pair ∈ report.physical.directory.crashImages
  keeperSurvives : some report.keeper ∈ report.physical.keeper.crashImages

theorem Reached.preparedHistory {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Reached) (ready : before.RetainedReady directory writer) :
    (WAL.encode (before.history ++ report.batch)).size = report.nextBytes ∧
      (WAL.encode (before.history ++ report.batch)).size < UInt64.size ∧
      WAL.OrdinalsFrom 1 (before.history ++ report.batch) := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨_, ordinals, _, size⟩ := prepareBatch_extends_history ready.resumed.ordered count observed.prepared
  have exactSize : (WAL.encode (before.history ++ report.batch)).size = report.nextBytes := by
    rw [size, nextBytes, ready.resumed.bytes]
  exact ⟨exactSize, exactSize.symm ▸ observed.fits, ordinals⟩

theorem Valid.preparedHistory {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    (WAL.encode (before.history ++ report.batch)).size = report.nextBytes ∧
      (WAL.encode (before.history ++ report.batch)).size < UInt64.size ∧
      WAL.OrdinalsFrom 1 (before.history ++ report.batch) :=
  observed.toReached.preparedHistory ready

/-- The reported finished callbacks reach the exact keeper path and
whole-batch byte count while the writer owns the lock. The action at the
next schedule index is the interrupted callback. -/
theorem Valid.reachesInterruption {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    report.inFlight.owners.Owns directory writer ∧
      Publication.steps[report.cut.index]? = some report.cut.action ∧
      commit (report.append (directory.file (.walSegment before.wal.active.first)) (WAL.encodeBatch report.batch))
        ((Publication.steps.take report.cut.index).forM (performMarkerAt directory before.wal.active.first
          (WAL.encode (before.history ++ report.batch)).size report.stage report.sync report.rename))
        (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) = .ok () report.reached := by
  have sameKeeper := ready.resumed.keeper.trans ready.active
  have sameCount := (observed.preparedHistory ready).1
  refine ⟨ready.held, report.cut.actionAt, ?_⟩
  simpa only [sameKeeper, ← sameCount] using observed.reachedPrefix

theorem Valid.powerLoss {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Valid) :
    BoundedReopenTrace directory (BatchRetryTarget before.history report.batch before.wal.active.first)
      report.inFlight report.crashed :=
  .powerLoss .empty observed.pairSurvives observed.keeperSurvives (List.mem_singleton_self _)

/-- The physical cut and the batch interpreter agree on the live and
surviving bindings and keeper bytes. Their staging fields can differ. -/
theorem physicalProjection (report : SegmentedBatchMarkerPowerLossReport directory before writer) :
    let scratch := before.wal.directory.staged .walBoundary
    let effects := report.cut.writeEffects report.appendCrashTails scratch
    let modeled := writeFilesAfter (runBatchEffects before.history report.batch effects scratch)
    BatchCutProjection report.physical
      (modeled.reopenSegment before.wal.active.first before.history before.wal.directory.active.manifest) := by
  intro scratch effects modeled
  obtain ⟨visible, tails, active, markers⟩ :=
    report.cut.matchesBatchEffects before.history report.batch report.appendCrashTails scratch
  let bindMarker := DirectoryPublication.Bindings.mk before.wal.directory.active.manifest
  let includePrefix := fun tail => some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)
  exact ⟨congrArg bindMarker active, congrArg (List.map bindMarker) markers,
    congrArg includePrefix visible, congrArg (List.map includePrefix) tails, ⟨rfl, rfl⟩⟩

/-- The physical cut supplies the same surviving state to the existing
batch retry interpreter. Later retries start at the actual crashed image. -/
theorem Valid.modeledRetries {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Valid) {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history report.batch before.wal.active.first)
      report.crashed retry) :
    BoundedReopenTrace directory (BatchRetryTarget before.history report.batch before.wal.active.first)
      report.modeled retry := by
  have markers := report.physicalProjection.metadata
  have keepers := report.physicalProjection.keeperChoices
  have poweredOff : BoundedReopenTrace directory (BatchRetryTarget before.history report.batch before.wal.active.first)
      report.modeled report.crashed :=
    .powerLoss .empty (markers ▸ observed.pairSurvives) (keepers ▸ observed.keeperSurvives) (List.mem_singleton_self _)
  exact poweredOff.trans attempts

/-- The actual surviving marker and keeper select exactly the prior
history or the entire submitted batch appended to it. -/
theorem Valid.selectsWholeBatch {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ history, (history = before.history ∨ history = before.history ++ report.batch) ∧
      report.crashed.image.directory.active.manifest = before.wal.directory.active.manifest ∧
      report.crashed.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      selectRetained before.wal.active.first (WAL.encode history).size.toUInt64 report.keeper =
        .ok (WAL.encode (history.drop before.wal.active.first)) := by
  have starts : before.wal.active.first ≤ before.history.length := by
    rw [← ready.layout.activeEnd]
    exact ready.layout.forward before.wal.active (List.mem_append_right _ (by simp))
  have markers := report.physicalProjection.metadata
  have keepers := report.physicalProjection.keeperChoices
  exact selectSegment_atReportedBatchCut starts (observed.preparedHistory ready).2.1
    (report.cut.writeEffects report.appendCrashTails (before.wal.directory.staged .walBoundary))
    before.wal.directory.active.manifest (before.wal.directory.staged .walBoundary) report.pair report.keeper
    (List.mem_cons_of_mem _ (markers ▸ observed.pairSurvives))
    (List.mem_cons_of_mem _ (keepers ▸ observed.keeperSurvives))

end SegmentedBatchMarkerPowerLossReport
end Alvoki.Storage.DiskSession
