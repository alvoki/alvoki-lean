import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.SegmentedRetainedWriter

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Assemble the retained writer from the replay and the reached held
file image. Only the live directory pair remains after settlement. -/
theorem SegmentedWriterState.ofReopenRetained
    {directory : DiskDirectory} {descriptor : Nat} {installed : Installed}
    {wal : WalSegmentImage} {history : List WAL.Write} {published : CheckpointPublication.Image}
    {target : Target} {checkpoint : Option (PackedTable × UInt64)} {final : LockedFileState FileImage}
    (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (visible : wal.directory.active = target.pair) (keeper : target.first = wal.active.first)
    (sealed : final.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    (held : final.owners.Owns directory descriptor) :
    let writer := SegmentedWriterState.ofReopen installed wal history published target checkpoint final
    ResumedAppendReady writer.installed writer.files writer.target writer.history writer.published writer.checkpoint →
      writer.RetainedReady directory descriptor := by
  intro writer resumed
  have retained : writer.wal.Valid writer.history := by
    intro pair chosen
    change pair ∈ final.image.directory.active :: final.image.directory.crashImages at chosen
    have directoryReady : final.image.Ready target := resumed.ready
    have same : pair = target.pair := by
      simpa [directoryReady.selected, directoryReady.settled] using chosen
    subst pair
    apply valid target.pair
    rw [← visible]
    exact List.mem_cons_self ..
  exact ⟨resumed, ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩,
    retained, spans, rfl, sealed, keeper, rfl, held⟩

/-- A held reopen installs the ordinary writer state from the retained
layout. Settling the directory keeps the selected validated WAL suffix. -/
theorem AppendCutReady.writerRetained {directory descriptor liveRefs history published initial target generation result}
    (opened : AppendCutReady directory descriptor liveRefs history published initial target generation result)
    {wal : WalSegmentImage} (layout : wal.ReadLayout history) (valid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (visible : wal.directory.active = target.pair) (keeper : target.first = wal.active.first)
    (sealed : initial.kept = (wal.checkpointReopenFiles wal.directory none).kept) :
    ∃ session final, ∃ writer : SegmentedWriterState,
      result = .ok session final ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready writer.installed ∧ writer.files = final.image ∧ writer.owners = final.owners ∧
      writer.wal = { wal with directory := final.image.directory } ∧ writer.target = target ∧
      writer.history = history ∧ writer.installed.generation = generation ∧
      writer.published.durable = published.durable ∧
      writer.RetainedReady directory descriptor := by
  obtain ⟨through, trimmed, accepted, ordered, checkpoint, table, model, session, final, returned, selected,
    gen, _, path, lock, phase, durable, kept, held, _, bounds, refines, represents, _, _, _, _⟩ := opened
  let installed : Installed := ⟨table, generation, (WAL.encode history).size, target.first⟩
  let writer := SegmentedWriterState.ofReopen installed wal history published target checkpoint final
  have resumed : ResumedAppendReady writer.installed writer.files writer.target writer.history
      writer.published writer.checkpoint :=
    ⟨durable, through, rfl, rfl, trimmed, gen, selected, accepted, ordered, bounds, ⟨model, refines, represents⟩⟩
  exact ⟨session, final, writer, returned, path, lock, phase, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    SegmentedWriterState.ofReopenRetained layout valid spans visible keeper (kept.trans sealed) held resumed⟩

/-- After covered collection, the healthy locked inventory feeds the
native bounded reader. The keeper is still aligned, so only the directory
and keeper barriers are reached before the retained writer is installed. -/
theorem SegmentedWriterState.RetainedReady.openAfterCollection {directory descriptor state after}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after)
    {owners : LockOwners} {readerDescriptor nextRef : Nat}
    (raw : HealthyBoundedWalReports directory (owners.set (directory.file .lock) (some readerDescriptor))
      readerDescriptor after after.directory.active state.target.range.watermark state.published.durable ByteArray.empty)
    (scratch : Option (ByteArray × Bool)) (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let files := after.checkpointReopenFiles after.directory scratch
    sync #[directory.path] files = .ok () files.syncDirectory →
    sync #[directory.file (.walSegment after.active.first)] files.syncDirectory =
      .ok () files.syncDirectory.syncKeeper →
    ∃ session final, ∃ writer : SegmentedWriterState,
      runOpenWithInstallation directory readerDescriptor nextRef (.ok true) unlock
        (raw.reopen removeFile write sync renameFile) ⟨files, owners⟩ = .ok session final ∧
      session.directory = directory ∧ session.descriptor = readerDescriptor ∧ session.phase = .ready writer.installed ∧
      writer.files = final.image ∧ writer.owners = final.owners ∧
      writer.wal = { after with directory := final.image.directory } ∧ writer.target.pair = state.target.pair ∧
      writer.history = state.history ∧ writer.installed.generation = state.installed.generation ∧
      writer.published.durable = state.published.durable ∧
      writer.RetainedReady directory readerDescriptor := by
  intro files syncDirectory syncKeeper
  have pair := (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have decoded : after.directory.active.walRange = some state.target.range := pair.symm ▸ state.target.decoded
  have layout := retry.readLayout ready.layout
  have valid := retry.valid ready.valid
  obtain ⟨selected, range, keeper, tail, descriptors, offsets, _, choices, keeperPrefix, later⟩ :=
    layout.checkpointReopenLayout valid .visible decoded ready.resumed.through scratch
  have prepared := selected.prepared choices keeperPrefix (range.symm ▸ later)
  have fast : selected.plan.alignedWithoutPrune = true := by
    have size : selected.plan.keeperBytes.size = selected.plan.keeperSize := by
      change (selected.keeper.bytes ++ selected.tail).size = _
      rw [tail, ByteArray.append_empty]
      exact selected.target.trimmedSize
    have empty : selected.plan.newer = [] := rfl
    simp [Plan.alignedWithoutPrune, prepared.valid, size, empty]
  have healthy := finishActions_aligned_success (target := selected.target)
    (directory := directory) (sync := sync) (initial := files.syncDirectory) fast removeFile write renameFile
    (by simpa only [CanonicalKeeperLayout.plan, keeper] using syncKeeper)
  -- The plan proves the expected watermark and empty tail. Keep the same
  -- observed read callbacks when carrying those facts into the worker.
  let reports : HealthyBoundedWalReports directory (owners.set (directory.file .lock) (some readerDescriptor))
      readerDescriptor after files.directory.active selected.range.watermark state.published.durable selected.tail :=
    ⟨raw.list, raw.entries, raw.listing, raw.reports, raw.readPrefix, raw.held, raw.unique, raw.names, raw.regular,
      raw.manifest, raw.marker, raw.runs, by rw [range]; exact raw.sealed, by rw [tail]; exact raw.keeper⟩
  have accepted : state.published.AcceptsVersioned state.history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix state.history) after.directory.active.manifest := by
    rw [pair]
    exact ready.resumed.accepted
  have generation : ((after.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok state.installed.generation := by
    rw [pair]
    exact ready.resumed.generationRead
  have watermark := congrArg MarkedWalRange.watermark range
  have opened := runOpenWithInstallation_appendLayout layout ready.resumed.ordered selected keeper
    (watermark.symm ▸ descriptors) (watermark.symm ▸ offsets) prepared rfl accepted generation reports
    liveRefs fresh acquisition unlock removeFile write sync renameFile syncDirectory healthy
  obtain ⟨session, final, writer, returned, path, lock, phase, image, owners, wal, target, history, gen, durable, next⟩ :=
    opened.writerRetained layout valid (fun _ member => ready.spans _ (retry.sealedSublist.subset member))
      rfl (congrArg WalSegment.first keeper) rfl
  have samePair : writer.target.pair = state.target.pair := by
    rw [target]
    exact pair
  exact ⟨session, final, writer, returned, path, lock, phase, image, owners, wal, samePair, history, gen, durable, next⟩

end Alvoki.Storage.DiskSession
