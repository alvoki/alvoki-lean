import Alvoki.Storage.Disk.WalSegmentBoundedRetry
import Alvoki.Storage.Disk.WalSegmentCachedRetryReads

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The read-only preparation used by the cached worker. The state can
carry other reached filesystem observations alongside the WAL image. -/
def CachedRetryReadReports.prepare {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} (reported : CachedRetryReadReports directory layout)
    (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray) {state : Type} :
    EStateM IO.Error state (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (liftExcept (reported.inventory.reports.readOptional (directory.file .manifest)))
      (fun path => liftExcept (checkpointRunSizeReport reported.inventory.reports path))
      (fun path size => liftExcept (readRunPrefix path size)))
    (fun path => liftExcept (reported.inventory.reports.readOptional path))
    (fun watermark length => readSelectedWithCachedExtents directory watermark length
      (fun path => liftExcept (reported.list path))
      (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (reported.readSeal path size))
      (fun path size physical => liftExcept (reported.readKeeper path size physical)))

/-- Exact held reports yield the bounded plan and the table replayed from
the selected checkpoint. Preparation leaves the reached state unchanged. -/
theorem CachedRetryReadReports.prepares {state : Type} {directory : DiskDirectory} {image : FileImage}
    {history : List WAL.Write} {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout) (initial : state)
    (laterValid : image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sizes : SizedCheckpointRunReports directory reported.inventory.reports image.directory.active.manifest
      published.durable)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) = .ok image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) = .ok image.directory.active.walBoundary) :
    ∃ opened checkpoint model,
      reported.prepare sizes.readPrefix initial = .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) initial ∧
      SelectedIntegrityCheckpoint published.durable image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      opened.generation = (checkpoint.getD (.empty, 0)).2 ∧
      opened.walBytes.toNat = history.length * frameSize ∧ opened.keeper = layout.keeper.first ∧
      opened.table.committed.toNat = history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
      RepresentsWalHistory history model ∧ opened.table.pins.active = [] := by
  obtain ⟨watermark, _, marker, count, visibleMarker, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, table, model, selected, reference, committed, rows, refines, represents, fresh⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  have clock := Option.some.inj (selected.watermark.symm.trans watermark)
  have checkpointSeen := sizes.readExact selected manifestRead initial
  have markerSeen : (liftExcept (reported.inventory.reports.readOptional (directory.file .walBoundary)) :
      EStateM IO.Error state _) initial = .ok (some marker) initial := by rw [markerRead, visibleMarker]; rfl
  have countSeen : (liftExcept ((WAL.Boundary.decode marker).mapError IO.userError) :
      EStateM IO.Error state _) initial = .ok count initial := by rw [decoded]; rfl
  have later : ∀ start ∈ image.later.visible, layout.range.through < start := laterValid _ List.mem_cons_self
  have walSeen := reported.readSelected following later absolute initial
  let files := layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
    [(layout.keeper.first, layout.keeper.bytes)]
  have replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files =
      .ok (WAL.encode (history.drop layout.first), table) := by
    simpa only [files, ByteArray.append_empty] using layout.chain.replaysMarked ByteArray.empty
      (layout.through ▸ absolute) (clock.symm ▸ layout.covers) ordered reference
  have tableSeen : (liftExcept ((recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files).mapError
      IO.userError) : EStateM IO.Error state _) initial = .ok (WAL.encode (history.drop layout.first), table) initial := by
    rw [replayed]
    rfl
  have keeperSeen : files.getLast? = some (layout.keeper.first, layout.keeper.bytes) := by simp [files]
  have counted : count.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  let opened : Reopened := ⟨table, (checkpoint.getD (.empty, 0)).2, count, layout.keeper.first⟩
  refine ⟨opened, checkpoint, model, ?_, selected, reference, rfl, layout.through ▸ absolute, rfl,
    committed, rows, refines, represents, fresh⟩
  dsimp only [files] at tableSeen keeperSeen
  simp only [CachedRetryReadReports.prepare, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind,
    checkpointSeen, markerSeen, countSeen, clock, walSeen, tableSeen, keeperSeen, counted, Pure.pure, EStateM.pure]
  rfl

/-- With admissible keeper and later-name survivors, the cached marked
worker reconstructs the exact checkpoint and selected WAL before repair.
The callback contract covers the authorization barrier and only the
effects reached along the selected prune/replacement or aligned route. -/
theorem CachedRetryReadReports.completes {directory : DiskDirectory} {retry : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout retry history} (reported : CachedRetryReadReports directory layout)
    (keeperValid : retry.keeper.Valid layout.target.Accepts)
    (laterValid : retry.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sizes : SizedCheckpointRunReports directory reported.inventory.reports retry.directory.active.manifest
      published.durable)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok retry.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) =
      .ok retry.directory.active.walBoundary)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] retry = .ok () retry.syncDirectory)
    (healthy : ∀ action before next, ReachesAction layout.target retry.syncDirectory layout.plan.finishActions action before →
      before.effect layout.target action = some next →
      performPaths directory layout.plan removeFile throw write sync renameFile action before = .ok () next) :
    ∃ opened after checkpoint model, after.Ready layout.target ∧ EffectTrace layout.target retry after ∧
      reopenMarkedBoundedWithCachedExtents directory
        (fun path => liftExcept (reported.inventory.reports.readOptional path))
        (fun path => liftExcept (checkpointRunSizeReport reported.inventory.reports path))
        (fun path size => liftExcept (sizes.readPrefix path size))
        (fun path => liftExcept (reported.list path))
        (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
        (fun path size => liftExcept (reported.readSeal path size))
        (fun path size physical => liftExcept (reported.readKeeper path size physical))
        removeFile write sync renameFile retry = .ok opened after ∧
      SelectedIntegrityCheckpoint published.durable retry.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      opened.generation = (checkpoint.getD (.empty, 0)).2 ∧
      opened.walBytes.toNat = history.length * frameSize ∧ opened.keeper = layout.keeper.first ∧
      opened.table.committed.toNat = history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
      RepresentsWalHistory history model ∧ opened.table.pins.active = [] := by
  obtain ⟨opened, checkpoint, model, preparedRead, selected, reference, generation, bytes, keeper,
    committed, rows, refines, represents, fresh⟩ :=
    reported.prepares retry laterValid following accepted ordered sizes manifestRead markerRead
  have prepared : Prepared retry layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  obtain ⟨after, finished, ready, trace⟩ :=
    finishMarkedOpen_completes prepared directory removeFile write sync renameFile settles healthy
  have bounded : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      removeFile write sync renameFile retry = .ok () after := by
    rw [layout.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full _ _ prepared.valid]
    exact finished
  refine ⟨opened, after, checkpoint, model, ready, trace, ?_, selected, reference, generation, bytes,
    keeper, committed, rows, refines, represents, fresh⟩
  change EStateM.bind (reported.prepare sizes.readPrefix)
      (fun (plan, prepared, size) => do
        finishBoundedMarkedOpen directory plan size removeFile write sync renameFile
        return prepared) retry = _
  simp only [EStateM.bind, preparedRead, Bind.bind, bounded, Pure.pure, EStateM.pure]

/-- After healthy repair, every admitted power loss keeps the same
checkpoint binding and selected segments, with an aligned keeper and no
names left to prune. The resulting layout can feed the next cached reopen. -/
theorem EffectTrace.durableCrashLayout {initial after : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout initial history} (trace : EffectTrace layout.target initial after)
    (prepared : Prepared initial layout.target layout.plan) (ready : after.Ready layout.target)
    {pair : DirectoryPublication.Bindings} {keeper : Option ByteArray} {later : List Nat}
    (metadataSurvives : pair ∈ after.directory.crashImages)
    (keeperSurvives : keeper ∈ after.keeper.crashImages)
    (laterSurvives : later ∈ after.later.crashImages) :
    let crashed := after.crash pair keeper later
    ∃ retry : CanonicalKeeperLayout crashed history,
      retry.target = layout.target ∧ retry.sealed = layout.sealed ∧ retry.keeper = layout.keeper ∧
      crashed.kept = initial.kept ∧ retry.tail = ByteArray.empty ∧ crashed.Ready retry.target := by
  intro crashed
  have continued : EffectTrace layout.target initial crashed :=
    .crash trace metadataSurvives keeperSurvives laterSurvives
  obtain ⟨retry, target, _, _, sealed, sameKeeper, kept, _⟩ :=
    continued.canonicalRetryLayout layout prepared
  have samePair : pair = layout.target.pair := by simpa [ready.settled] using metadataSurvives
  have sameBytes : keeper = some layout.target.trimmed := by simpa [ready.keeperDurable] using keeperSurvives
  have sameLater : later = [] := by simpa [ready.pruned.2] using laterSurvives
  have exactSize : retry.keeper.bytes ++ retry.tail = retry.keeper.bytes := by
    have contents : keeper = some (retry.keeper.bytes ++ retry.tail) := retry.visible
    have trimmed : layout.target.trimmed = retry.keeper.bytes := by rw [sameKeeper]; rfl
    rw [sameBytes, trimmed] at contents
    exact (Option.some.inj contents).symm
  have noTail : retry.tail = ByteArray.empty := by
    apply (ByteArray.append_right_inj retry.keeper.bytes).mp
    simpa only [ByteArray.append_empty] using exactSize
  refine ⟨retry, target, sealed, sameKeeper, kept, noTail, ?_⟩
  rw [target]
  subst pair keeper later
  exact ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

end Alvoki.Storage.WalSegmentRepair
