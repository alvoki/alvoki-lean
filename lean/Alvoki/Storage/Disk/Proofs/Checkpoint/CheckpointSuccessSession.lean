import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointLockHandoff
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCheckpointRetained
import Alvoki.Storage.Disk.Proofs.Append.ReopenedSegmentAppend

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WalSegmentRepair (FileImage Target)
open Manifest (IntegrityCheckpoint)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The actual checkpoint file dispatch, when all reported operations
succeed, installs the flushed table and publishes the exact strict manifest
and durable run map for the new generation. Its available segments and
lock ownership survive publication unchanged. The new checkpoint covers
the history even when earlier covered segments have been collected. -/
theorem runPreparedCheckpoint_segmentedSuccess {directory : DiskDirectory} {owners : LockOwners}
    {before : WalSegmentImage} {history : List WAL.Write}
    (layout : before.ReadLayout history)
    (marker : before.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (walFits : (WAL.encode history).size < UInt64.size)
    (initial : CheckpointPublication.Image) {installed : Installed} {checkpoint : PackedTable}
    {model : Sequential.SnapshotTable UInt64}
    (refines : installed.table.Refines model) (represents : RepresentsWalHistory history model)
    (rowBounds : installed.table.RowBounds)
    (flushed : (flushForCheckpoint installed.table id : Except String PackedTable) = .ok checkpoint)
    (generationFits : installed.generation.toNat + 1 < UInt64.size)
    (runCountFits : checkpoint.runs.length < UInt64.size)
    (runBytesFit : ∀ bytes ∈ checkpoint.runs.map (·.run.bytes), bytes.size < UInt64.size)
    (checkpointWrite checkpointStage : FilePath → ByteArray → EStateM IO.Error Nat Unit)
    (checkpointSync : Array FilePath → EStateM IO.Error Nat Unit)
    (checkpointRename : FilePath → FilePath → EStateM IO.Error Nat Unit)
    (report : Step → StepReport) {manifest : ByteArray} {cut : Nat} :
    let generation := (installed.generation.toNat + 1).toUInt64
    let runs := checkpoint.runs.map (·.run.bytes)
    let header := checkpointHeader checkpoint generation
    let metadata := IntegrityCheckpoint.fromRuns header runs
    let plan := VersionedRunSet.integrity ⟨header, runs⟩
    let perform := performCheckpointFileStep directory generation checkpoint.runs.toArray
      (directory.file .stagedManifest) manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      checkpointWrite checkpointStage checkpointSync checkpointRename
    let prepared := { installed with table := checkpoint, generation := generation }
    encodeCheckpointIntegrityManifest checkpoint generation = .ok manifest →
    ReachedFileReports report perform (steps checkpoint.runs.length) 0 →
    CheckpointPublication.run checkpoint.runs.toArray.size perform 0 = .ok () cut →
    runPreparedCheckpoint prepared perform (.ready installed, ⟨0, owners⟩) = .ok () (.ready prepared, ⟨cut, owners⟩) ∧
    generation.toNat = installed.generation.toNat + 1 ∧
    manifest = metadata.encode ∧ IntegrityCheckpoint.decode manifest = .ok metadata ∧
    ∃ published base, initial.executeVersioned plan cut = some published ∧
      published.manifest = .settled (some manifest) ∧
      (∀ index, published.durable generation index = runs[index]?) ∧
      (∀ other, other ≠ generation → ∀ index, published.durable other index = initial.durable other index) ∧
      let wal := published.segmentedCheckpointView before
      wal.directory.active = ⟨some manifest, before.directory.active.walBoundary⟩ ∧
      wal.directory.crashImages = [wal.directory.active] ∧
      published.manifest = wal.directory.project .manifest ∧
      wal.directory.active.walRange = some ⟨history.length, history.length⟩ ∧
      wal.sealed = before.sealed ∧ wal.active = before.active ∧
      wal.ReadLayout history ∧ wal.Valid history ∧ wal.readDescriptors history.length = [before.active] ∧
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
        wal.directory.active.manifest ∧
      SelectedIntegrityCheckpoint published.durable wal.directory.active.manifest (some (base, generation)) ∧
      base.SameData checkpoint ∧ checkpoint.committed.toNat = history.length ∧ checkpoint.RowBounds ∧
      ∃ afterModel, checkpoint.Refines afterModel ∧ RepresentsWalHistory history afterModel := by
  intro generation runs header metadata plan perform prepared encoded observed succeeded
  have complete : CheckpointPublication.run checkpoint.runs.length perform 0 = .ok () cut := by
    simpa only [List.size_toArray] using succeeded
  have ready : runPreparedCheckpoint prepared perform (.ready installed, ⟨0, owners⟩) =
      .ok () (.ready prepared, ⟨cut, owners⟩) := by
    simp only [runPreparedCheckpoint, runCheckpointActions, Bind.bind, EStateM.bind, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, prepared, complete]
  have exactManifest : manifest = metadata.encode :=
    Except.ok.inj (encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation runBytesFit))
  obtain ⟨afterModel, written, refined, represented⟩ := WrittenCheckpoint.of_flushForCheckpoint_history
    flushed refines represents rowBounds runCountFits generation
  have count : metadata.header.runCount.toNat = runs.length := by
    simpa [metadata, IntegrityCheckpoint.fromRuns, runs, header, List.length_map] using written.count.symm
  have stamps : metadata.runs.length = metadata.header.runCount.toNat := by
    simpa [metadata, IntegrityCheckpoint.fromRuns] using count.symm
  have decoded : IntegrityCheckpoint.decode manifest = .ok metadata := by
    rw [exactManifest]
    exact IntegrityCheckpoint.decode_encode metadata written.validFloor stamps
  have acknowledged : checkpoint.committed.toNat = history.length := by
    have flushedClock := (WrittenCheckpoint.of_flushForCheckpoint flushed refines runCountFits
      rowBounds.runs rowBounds.memory generation).2.1
    rw [flushedClock, refines.committed, represents.committed_count]
  have watermark : metadata.header.committed.toNat = history.length := written.watermark ▸ acknowledged
  have historyFits : history.length < UInt64.size := by
    have bound := walFits
    rw [WAL.encode_size] at bound
    simp only [WAL.frameSize] at bound
    omega
  have covered : metadata.header.committed ≤ history.length.toUInt64 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [watermark, UInt64.toNat_ofNat_of_lt' historyFits]
    exact Nat.le_refl _
  have checks : metadata.validateRuns runs = true :=
    IntegrityCheckpoint.validateRuns_fromRuns header runs count.symm runBytesFit
  have dispatchCount : plan.files.length = checkpoint.runs.length := by simp [plan, runs, VersionedRunSet.integrity]
  rw [← dispatchCount] at observed complete
  obtain ⟨exactCut, effects, actual, _⟩ := initial.runVersionedWithObservedSuccess plan report perform observed complete
  obtain ⟨published, modeled, settled, durable, preserved⟩ := checkpointVersioned_complete initial plan
  have exactEffects : effects = published := Option.some.inj ((exactCut ▸ actual).symm.trans modeled)
  subst effects
  have settled : published.manifest = .settled (some manifest) := by
    change published.manifest = .settled (some metadata.encode) at settled
    simpa only [exactManifest] using settled
  obtain ⟨active, crashes, projected, range, layout, valid, keeperRead⟩ :=
    published.segmentedCheckpointView_settledRetained layout marker walFits settled decoded watermark
  have acceptedRuns : AcceptsRunSet published.durable history.length.toUInt64
      (fun candidate files => CheckpointRepresentsPrefix history candidate files ∧ metadata.validateRuns files = true)
      metadata.header runs :=
    ⟨⟨⟨checkpoint, afterModel, written, refined, represented⟩, checks⟩, covered, count, fun index _ => durable index⟩
  have accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      (some manifest) := (Image.acceptsVersioned_integrity_iff decoded).mpr ⟨runs, acceptedRuns⟩
  obtain ⟨base, loaded, sameData⟩ := written.loads
  have loadedStrict : loadIntegrityRunSet metadata runs = .ok base :=
    loadIntegrityRunSet_iff.mpr ⟨checks, loaded⟩
  have selected : SelectedIntegrityCheckpoint published.durable (some manifest) (some (base, generation)) :=
    .present decoded acceptedRuns.ordered loadedStrict
  refine ⟨ready, UInt64.toNat_ofNat_of_lt' generationFits, exactManifest, decoded, published, base, actual, settled,
    durable, preserved, active, crashes, projected, range, rfl, rfl, layout, valid, keeperRead, ?_, ?_, sameData,
    acknowledged, written.rowBounds, afterModel, refined, ?_⟩
  · rw [active]
    exact accepted
  · rw [active]
    exact selected
  · simpa only [acknowledged, List.take_length] using represented

/-- Retarget the ready writer to the new, settled checkpoint. The keeper
payload, full sealed map, and lack of newer WAL files are maintained
from the previous ready state. The new checkpoint is loaded from its
exact run files, while the writer keeps its live flushed table. -/
theorem ResumedAppendReady.afterCheckpointPublication
    {installed : Installed} {files : FileImage} {target : Target}
    {history : List WAL.Write} {initial : CheckpointPublication.Image} {initialBase : Option (PackedTable × UInt64)}
    (before : ResumedAppendReady installed files target history initial initialBase)
    {published : CheckpointPublication.Image} {directory : DirectoryPublication.Image}
    (settled : directory.crashImages = [directory.active])
    (range : directory.active.walRange = some ⟨history.length, history.length⟩)
    {checkpoint base : PackedTable} {generation : UInt64}
    (selected : SelectedIntegrityCheckpoint published.durable directory.active.manifest (some (base, generation)))
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      directory.active.manifest)
    (bounds : checkpoint.RowBounds)
    (canonical : ∃ model, checkpoint.Refines model ∧ RepresentsWalHistory history model) :
    let prepared := { installed with table := checkpoint, generation := generation }
    let after := { files with directory := directory }
    ∃ nextTarget : Target, nextTarget.first = target.first ∧
      ResumedAppendReady prepared after nextTarget history published (some (base, generation)) := by
  intro prepared after
  let nextTarget : Target := {
    pair := directory.active
    range := ⟨history.length, history.length⟩
    decoded := range
    first := target.first
    firstCovered := before.through ▸ target.firstCovered
    trimmed := target.trimmed
    trimmedSize := before.through ▸ target.trimmedSize
  }
  exact ⟨nextTarget, rfl,
    ⟨⟨rfl, settled, before.ready.keeper, before.ready.keeperDurable, before.ready.pruned⟩,
      rfl, before.keeper, before.bytes, before.contents, rfl, selected, accepted, before.ordered, bounds, canonical⟩⟩

end Alvoki.Storage.DiskSession
