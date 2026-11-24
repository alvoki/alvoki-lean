import Alvoki.Storage.Disk.AppendCutSession
import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- The fixed active segment can support either the old history or that
history with the one submitted frame. The marker determines which. -/
def AppendRetryTarget (history : List WAL.Write) (event : WAL.Write) (first : Nat) (target : Target) : Prop :=
  target.first = first ∧ ∃ selected, (selected = history ∨ selected = history ++ [event]) ∧
    target.range.through = selected.length ∧ target.trimmed = WAL.encode (selected.drop first)

theorem AppendRetryTarget.unique {history : List WAL.Write} {event : WAL.Write} {first : Nat}
    {left right : Target} (a : AppendRetryTarget history event first left)
    (b : AppendRetryTarget history event first right) (pair : left.pair = right.pair) : left = right := by
  obtain ⟨leftStart, l, oldLeft, throughLeft, bytesLeft⟩ := a
  obtain ⟨rightStart, r, oldRight, throughRight, bytesRight⟩ := b
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  have length : l.length = r.length := throughLeft.symm.trans (congrArg MarkedWalRange.through range) |>.trans throughRight
  have historyEq : l = r := by
    rcases oldLeft with rfl | rfl <;> rcases oldRight with rfl | rfl
    · rfl
    · simp only [List.length_append, List.length_singleton] at length
      omega
    · simp only [List.length_append, List.length_singleton] at length
      omega
    · rfl
  have sameStart := leftStart.trans rightStart.symm
  rw [historyEq] at bytesLeft
  have sameBytes := bytesLeft.trans bytesRight.symm
  cases left
  cases right
  cases pair
  cases range
  cases sameStart
  cases sameBytes
  rfl

private theorem appendObservation {before : WalSegmentImage} {cut : ReopenImage}
    {scratch : Option (ByteArray × Bool)} {current : FileImage}
    (observed : BeforeReopenBarrier (before.appendReopenFiles cut scratch) current) :
    ∃ seen observedScratch, AppendReopenObservation cut seen ∧
      current = before.appendReopenFiles seen observedScratch := by
  cases observed with
  | live => exact ⟨cut, scratch, .live, rfl⟩
  | crash pair keeper later metadata payload names =>
    have empty : later = [] := List.mem_singleton.mp names
    subst later
    exact ⟨.crash pair keeper, none, .crash pair keeper metadata payload, rfl⟩

private def AppendRetryLayout (before : WalSegmentImage) (history : List WAL.Write)
    (event : WAL.Write) (watermark : Nat) (current : FileImage) : Prop :=
  ∃ selectedHistory, (selectedHistory = history ∨ selectedHistory = history ++ [event]) ∧
    current.directory.active.manifest = before.directory.active.manifest ∧
    current.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selectedHistory).size.toUInt64) ∧
    ∃ wal : WalSegmentImage, wal.ReadLayout selectedHistory ∧ WalSegment.Chain selectedHistory 0 wal.segments ∧
    ∃ selected : CanonicalKeeperLayout current selectedHistory,
      selected.range.watermark = watermark ∧ selected.keeper = wal.active ∧
      selected.target.first = before.active.first ∧
      selected.sealed ++ [selected.keeper] = wal.readDescriptors watermark ∧
      selectWalSegmentReads (wal.segments.map WalSegment.first) watermark =
        some (selected.first, (wal.readDescriptors watermark).map WalSegment.first) ∧
      Prepared current selected.target selected.plan ∧ current.later.visible = []

/-- At the end of a finite failed-open prefix, recover the exact current
keeper layout under the original append's old-or-new marker rule. -/
private theorem appendRetryLayout {before : WalSegmentImage} {history : List WAL.Write}
    (layout : before.ReadLayout history) (chain : WalSegment.Chain history 0 before.segments)
    {watermark : Nat} (covered : watermark ≤ history.length)
    (event : WAL.Write) (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    (effects : WriteEffects) (markerScratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark before.directory.active.manifest = some watermark)
    {scratch : Option (ByteArray × Bool)} {current : FileImage} :
    let cut := (writeFilesAfter (runWriteEffects history event effects markerScratch)).reopenSegment
      before.active.first history before.directory.active.manifest
    ReopenLineage (before.appendReopenFiles cut scratch) (AppendRetryTarget history event before.active.first) current →
    AppendRetryLayout before history event watermark current := by
  intro cut lineage
  have readChoice {image : FileImage} (observed : BeforeReopenBarrier (before.appendReopenFiles cut scratch) image) :
      AppendRetryLayout before history event watermark image := by
    obtain ⟨seen, observedScratch, admitted, rfl⟩ := appendObservation observed
    obtain ⟨selectedHistory, allowed, manifest, marker, canonical, whole, selected, range, keeper, descriptors,
      offsets, _, keeperChoices, keptPrefix, later⟩ := layout.afterAppendCut chain covered event fits effects
        before.directory.active.manifest markerScratch checkpoint seen observedScratch admitted
    refine ⟨selectedHistory, allowed, manifest, marker, _, canonical, whole, selected,
      congrArg MarkedWalRange.watermark range, keeper, ?_, descriptors, offsets,
      selected.prepared keeperChoices keptPrefix later, rfl⟩
    change selected.keeper.first = before.active.first
    rw [keeper]
    rfl
  cases lineage with
  | before original => exact readChoice original
  | repairing original admitted prepared trace =>
    obtain ⟨selectedHistory, allowed, manifest, marker, wal, canonical, whole, selected, watermark, keeper, first,
      descriptors, offsets, sourcePrepared, empty⟩ := readChoice original
    have canonicalTarget : AppendRetryTarget history event before.active.first selected.target :=
      ⟨first, selectedHistory, allowed, selected.through, first ▸ selected.chain.keeperBytes⟩
    have same := AppendRetryTarget.unique admitted canonicalTarget (prepared.pair.symm.trans sourcePrepared.pair)
    rw [same] at trace
    obtain ⟨retry, target, range, start, sealed, nextKeeper, _, prepared⟩ :=
      trace.canonicalRetryLayout selected sourcePrepared
    have pair := (trace.valid sourcePrepared.pair sourcePrepared.keeperPrefix sourcePrepared.newer).selected.trans
      sourcePrepared.pair.symm
    refine ⟨selectedHistory, allowed, ?_, ?_, wal, canonical, whole, retry,
      (congrArg MarkedWalRange.watermark range).trans watermark, nextKeeper.trans keeper,
      (congrArg Target.first target).trans first, ?_, ?_, target.symm ▸ prepared, trace.emptyLater empty⟩
    · exact (congrArg DirectoryPublication.Bindings.manifest pair).trans manifest
    · exact (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker
    · rw [sealed, nextKeeper]; exact descriptors
    · rw [start]; exact offsets

/-- Start with the exact files left by the reported append error and the
ownership map after close or the last observed reference drop. A finite
sequence of bounded open failures, observed reference drops, and power
losses then determines the current marker and canonical keeper layout.
From those current files the next healthy open installs the exact table. -/
theorem BoundedReopenTrace.installsAfterAppendError {directory : DiskDirectory} {owners : LockOwners}
    {writerDescriptor : Nat} (ownership : owners.Owns directory writerDescriptor)
    {installed : Installed} {before : WalSegmentImage} {history : List WAL.Write}
    {published : CheckpointPublication.Image} {watermark : Nat}
    (ready : AppendCutWriter installed before history published watermark)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {table : PackedTable}
    (prepared : prepareWrite installed.table key value = some (event, table))
    (fits : installed.walBytes + frameSize < UInt64.size) (effects : WriteEffects)
    (append stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (commitSync : Array FilePath → EStateM IO.Error WriteFiles Unit)
    (commitRename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit)
    (reports : AppendCommitReports directory installed.activeFirst history event (installed.walBytes + frameSize)
      effects (before.directory.staged .walBoundary) append stage commitSync commitRename)
    {cause : IO.Error} {failed : WriteFiles}
    (commitFailed : commitAt directory installed.activeFirst event (installed.walBytes + frameSize)
      append stage commitSync commitRename (WriteFiles.initial history (before.directory.staged .walBoundary)) =
      .error cause failed)
    (scratch : Option (ByteArray × Bool)) {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget history event before.active.first)
      ⟨before.appendReopenFiles (failed.reopenSegment before.active.first history before.directory.active.manifest) scratch,
        owners.set (directory.file .lock) none⟩ retry)
    {descriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let initial := WriteFiles.initial history (before.directory.staged .walBoundary)
    let next := { installed with table, walBytes := installed.walBytes + frameSize }
    let commit := commitAt directory installed.activeFirst event next.walBytes append stage commitSync commitRename
    let poisoned : Phase Installed × LockedFileState WriteFiles := (.poisoned, ⟨failed, owners⟩)
    let released : LockedFileState WriteFiles := ⟨failed, owners.set (directory.file .lock) none⟩
    runPreparedWrite next event.sequence commit (.ready installed, ⟨initial, owners⟩) = .error (.commitUnknown cause) poisoned ∧
    runCloseWithFiles directory writerDescriptor .success poisoned = .ok () (.closed, released) ∧
    (∀ (references : HeldLockReferences writerDescriptor) (drops : List LockReferenceDrop),
      references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) ∧
    retry.image.kept = (before.appendReopenFiles
      (failed.reopenSegment before.active.first history before.directory.active.manifest) scratch).kept ∧
    ∃ selectedHistory, (selectedHistory = history ∨ selectedHistory = history ++ [event]) ∧
      retry.image.directory.active.manifest = before.directory.active.manifest ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selectedHistory).size.toUInt64) ∧
      ∃ wal : WalSegmentImage, wal.ReadLayout selectedHistory ∧ WalSegment.Chain selectedHistory 0 wal.segments ∧
      ∃ selected : CanonicalKeeperLayout retry.image selectedHistory,
        selected.target.first = installed.activeFirst ∧
        ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
            wal retry.image.directory.active selected.range.watermark published.durable selected.tail,
          sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
          (∀ action prior next,
            ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
            prior.effect selected.target action = some next →
            performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
          AppendCutReady directory descriptor liveRefs selectedHistory published retry.image selected.target
            installed.generation (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
              (raw.reopen removeFile write sync renameFile) retry) := by
  intro initial next commit poisoned released
  obtain ⟨unknown, closed, dropped, _⟩ := runPreparedWrite_failure_handoff
    (before := ⟨initial, owners⟩) installed next event.sequence commitFailed ownership
  obtain ⟨model, refined, represented⟩ := ready.canonical
  have committed : history.length = installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨_, _, extended, _, size⟩ := prepareWrite_extends_history ready.ordered committed prepared
  have byteCount : installed.walBytes + frameSize = (WAL.encode (history ++ [event])).size := by
    rw [ready.count, size]
  have modeled := reports.run byteCount
  rw [forgetError, commitFailed] at modeled
  have exactError : writeFilesAfter (runWriteEffects history event effects
      (before.directory.staged .walBoundary)) = failed := by rw [← modeled]; rfl
  have lineage := attempts.lineage (fun a b pair => AppendRetryTarget.unique a b pair)
  refine ⟨unknown, closed, dropped, lineage.keepsSealed, ?_⟩
  obtain ⟨strict, covered, _⟩ := DirectoryPublication.Bindings.walRange_accounting ready.range
  have allFit := byteCount ▸ fits
  obtain ⟨selectedHistory, allowed, manifest, marker, wal, layout, chain, selected, range, keeper, first,
    descriptors, offsets, selectedPrepared, empty⟩ := appendRetryLayout ready.layout ready.chain covered event allFit
      effects (before.directory.staged .walBoundary) strict (by rw [exactError]; exact lineage)
  have accepted : published.AcceptsVersioned selectedHistory.length.toUInt64 (CheckpointRepresentsPrefix selectedHistory)
      retry.image.directory.active.manifest := by
    rw [manifest]
    rcases allowed with rfl | rfl
    · exact ready.checkpoint
    · exact published.acceptsVersioned_extend_history ready.checkpoint allFit
  have consecutive : WAL.OrdinalsFrom 1 selectedHistory := by
    rcases allowed with rfl | rfl
    · exact ready.ordered
    · exact extended
  refine ⟨selectedHistory, allowed, manifest, marker, wal, layout, chain, selected, first.trans ready.first.symm, ?_⟩
  intro raw settles healthy
  exact runOpenWithInstallation_appendLayout layout consecutive selected keeper (range.symm ▸ descriptors)
    (range.symm ▸ offsets) selectedPrepared empty accepted (manifest.symm ▸ ready.generation) raw
    liveRefs fresh acquisition unlock removeFile write sync renameFile settles healthy

end Alvoki.Storage.DiskSession
