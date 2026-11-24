import Alvoki.Storage.Disk.CheckpointSuccessSession
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WalSegmentRepair (Target)

/-- The checkpoint preparation and concrete effects reported for one
segmented writer operation. -/
structure SegmentedCheckpointReport (directory : DiskDirectory) (before : SegmentedWriterState) where
  table : PackedTable
  manifest : ByteArray
  writeRun : FilePath → ByteArray → EStateM IO.Error Nat Unit
  writeStage : FilePath → ByteArray → EStateM IO.Error Nat Unit
  sync : Array FilePath → EStateM IO.Error Nat Unit
  renameFile : FilePath → FilePath → EStateM IO.Error Nat Unit
  report : CheckpointPublication.Step → StepReport
  cut : Nat

namespace SegmentedCheckpointReport

variable {directory : DiskDirectory} {before : SegmentedWriterState}

def generation (before : SegmentedWriterState) : UInt64 := (before.installed.generation.toNat + 1).toUInt64

def plan (attempt : SegmentedCheckpointReport directory before) : VersionedRunSet :=
  VersionedRunSet.integrity ⟨checkpointHeader attempt.table (generation before), attempt.table.runs.map (·.run.bytes)⟩

def prepared (attempt : SegmentedCheckpointReport directory before) : Installed :=
  { before.installed with table := attempt.table, generation := generation before }

def perform (attempt : SegmentedCheckpointReport directory before) :
    CheckpointPublication.Step → EStateM IO.Error Nat Unit :=
  performCheckpointFileStep directory (generation before) attempt.table.runs.toArray
    (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    attempt.writeRun attempt.writeStage attempt.sync attempt.renameFile

/-- The native preparation guards and successful execution of the reported
file calls, with an observation for every reached step. -/
structure Valid (attempt : SegmentedCheckpointReport directory before) : Prop where
  flushed : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok attempt.table
  generationFits : before.installed.generation.toNat + 1 < UInt64.size
  runCountFits : attempt.table.runs.length < UInt64.size
  encoded : encodeCheckpointIntegrityManifest attempt.table (generation before) = .ok attempt.manifest
  reached : ReachedFileReports attempt.report attempt.perform (CheckpointPublication.steps attempt.table.runs.length) 0
  succeeded : CheckpointPublication.run attempt.table.runs.length attempt.perform 0 = .ok () attempt.cut

/-- The installed endpoint of this execution, including the recovered
checkpoint projection and the exact file and session effects. -/
structure Installs (attempt : SegmentedCheckpointReport directory before) (after : SegmentedWriterState) : Prop where
  readyEffect : runPreparedCheckpoint attempt.prepared attempt.perform
    (.ready before.installed, ⟨0, before.owners⟩) = .ok () (.ready after.installed, ⟨attempt.cut, after.owners⟩)
  publication : before.published.executeVersioned attempt.plan attempt.cut = some after.published
  settled : after.published.manifest = .settled (some attempt.manifest)
  runs : ∀ index, after.published.durable (generation before) index = attempt.plan.files[index]?
  otherRuns : ∀ generation, generation ≠ after.installed.generation →
    ∀ index, after.published.durable generation index = before.published.durable generation index
  installed : after.installed = attempt.prepared
  history : after.history = before.history
  wal : after.wal = after.published.segmentedCheckpointView before.wal
  files : after.files = { before.files with directory := after.wal.directory }
  targetPair : after.target.pair = after.wal.directory.active
  targetFirst : after.target.first = before.target.first
  targetBytes : after.target.trimmed = before.target.trimmed
  checkpoint : SelectedIntegrityCheckpoint after.published.durable after.wal.directory.active.manifest after.checkpoint
  owners : after.owners = before.owners
  decodedManifest : Manifest.IntegrityCheckpoint.decode attempt.manifest = .ok
    (Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader attempt.table (generation before)) attempt.plan.files)
  restored : ∃ base, after.checkpoint = some (base, generation before) ∧
    base.SameData attempt.table ∧ base.committed.toNat = after.history.length

/-- Successful checkpointing keeps the available WAL inventory and its
held lock. Its exact new manifest covers the full history, making the
installed active segment the sole WAL read on recovery. -/
theorem installsRetained (attempt : SegmentedCheckpointReport directory before) (observed : attempt.Valid)
    (ready : before.RetainedReady directory descriptor) :
    ∃ after, attempt.Installs after ∧ after.RetainedReady directory descriptor ∧
      after.wal.readDescriptors after.history.length = [after.wal.active] := by
  obtain ⟨model, refines, represents⟩ := ready.resumed.canonical
  obtain ⟨_, _, _, count, _, _, counted⟩ := DirectoryPublication.Bindings.walRange_accounting before.target.decoded
  have bytes : (WAL.encode before.history).size = count.toNat := by
    rw [counted, ready.resumed.through, WAL.encode_size, Nat.mul_comm]
  have marker := congrArg Publication.Image.active ready.resumed.markerImage
  change before.files.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) at marker
  rw [ready.directoryFiles] at marker
  have walFits : (WAL.encode before.history).size < UInt64.size := bytes.symm ▸ count.toNat_lt_size
  have runBytesFit : ∀ bytes ∈ attempt.table.runs.map (·.run.bytes), bytes.size < UInt64.size := by
    by_cases bounded : (attempt.table.runs.map (·.run.bytes)).all
        (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact fun bytes member => of_decide_eq_true (List.all_eq_true.mp bounded bytes member)
    · have encoded := observed.encoded
      simp [encodeCheckpointIntegrityManifest, bounded, Bind.bind, Except.bind] at encoded
  have complete : CheckpointPublication.run attempt.table.runs.toArray.size attempt.perform 0 = .ok () attempt.cut := by
    simpa only [List.size_toArray] using observed.succeeded
  obtain ⟨readyEffect, _, _, decodedManifest, published, base, publication, settled, runs, others,
    _, crashes, projected, range, _, _, nextLayout, valid, keeperRead, accepted, selected, sameData, committed, bounds, canonical⟩ :=
    runPreparedCheckpoint_segmentedSuccess (directory := directory) (owners := before.owners)
      ready.layout marker walFits before.published refines represents ready.resumed.bounds
      observed.flushed observed.generationFits observed.runCountFits runBytesFit
      attempt.writeRun attempt.writeStage attempt.sync attempt.renameFile attempt.report
      observed.encoded observed.reached complete
  let wal := published.segmentedCheckpointView before.wal
  obtain ⟨target, keeper, resumed⟩ := ready.resumed.afterCheckpointPublication crashes range selected accepted bounds canonical
  let after : SegmentedWriterState := {
    installed := attempt.prepared
    wal := wal
    history := before.history
    files := { before.files with directory := wal.directory }
    published := published
    target := target
    checkpoint := some (base, generation before)
    owners := before.owners
  }
  have exactKeeper : target.trimmed = before.target.trimmed := by
    rw [resumed.contents, keeper, ready.resumed.contents]
  have restored : base.committed.toNat = after.history.length := by
    rw [sameData.committed]
    exact committed
  refine ⟨after, ⟨readyEffect, publication, settled, runs, others, rfl, rfl, rfl, rfl,
    resumed.ready.selected.symm, keeper, exactKeeper, selected, rfl, decodedManifest, base, rfl, sameData, restored⟩,
    ⟨resumed, nextLayout, valid, ready.spans, rfl, ready.sealedFiles, keeper.trans ready.active, projected, ready.held⟩,
    keeperRead⟩

/-- The existing full-history writer retains its stronger inventory
witness across the same successful checkpoint. -/
theorem installs (attempt : SegmentedCheckpointReport directory before) (observed : attempt.Valid)
    (ready : before.Ready directory descriptor) :
    ∃ after, attempt.Installs after ∧ after.Ready directory descriptor := by
  obtain ⟨after, installed, retained, _⟩ := attempt.installsRetained observed ready.toRetained
  have chain : WalSegment.Chain after.history 0 after.wal.segments := by
    rw [installed.history, installed.wal]
    exact ready.chain
  exact ⟨after, installed, ⟨retained.resumed, retained.layout, chain, retained.directoryFiles, retained.sealedFiles,
    retained.active, retained.manifestFiles, retained.held⟩⟩

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair) (first : left.first = right.first)
    (bytes : left.trimmed = right.trimmed) : left = right := by
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases bytes
  rfl

private theorem sameCheckpoint {durable binding left right}
    (a : SelectedIntegrityCheckpoint durable binding left) (b : SelectedIntegrityCheckpoint durable binding right) :
    left = right := by
  cases a with
  | absent => cases b; rfl
  | present decode stored loaded =>
    cases b with
    | present otherDecode otherStored otherLoaded =>
      cases Except.ok.inj (decode.symm.trans otherDecode)
      cases Option.some.inj (stored.symm.trans otherStored)
      cases Except.ok.inj (loaded.symm.trans otherLoaded)
      rfl

theorem Installs.unique {attempt : SegmentedCheckpointReport directory before} {left right : SegmentedWriterState}
    (a : attempt.Installs left) (b : attempt.Installs right) : left = right := by
  have published := Option.some.inj (a.publication.symm.trans b.publication)
  have wal : left.wal = right.wal := by rw [a.wal, b.wal, published]
  have files : left.files = right.files := by rw [a.files, b.files, wal]
  have pair : left.target.pair = right.target.pair := by rw [a.targetPair, b.targetPair, wal]
  have target := sameTarget pair (a.targetFirst.trans b.targetFirst.symm) (a.targetBytes.trans b.targetBytes.symm)
  have selected := a.checkpoint
  rw [published, wal] at selected
  have checkpoint := sameCheckpoint selected b.checkpoint
  have installed := a.installed.trans b.installed.symm
  have history := a.history.trans b.history.symm
  have owners := a.owners.trans b.owners.symm
  cases left
  cases right
  cases installed
  cases wal
  cases history
  cases files
  cases published
  cases target
  cases checkpoint
  cases owners
  rfl

/-- A raw checkpoint endpoint determined by the reached reports inherits
the ready invariant of the writer that executed it. -/
theorem Installs.preservesReady {attempt : SegmentedCheckpointReport directory before} {after : SegmentedWriterState}
    (endpoint : attempt.Installs after) (observed : attempt.Valid) (ready : before.Ready directory descriptor) :
    after.Ready directory descriptor := by
  obtain ⟨next, exactEffect, nextReady⟩ := attempt.installs observed ready
  exact (exactEffect.unique endpoint) ▸ nextReady

theorem Installs.preservesRetained {attempt : SegmentedCheckpointReport directory before} {after : SegmentedWriterState}
    (endpoint : attempt.Installs after) (observed : attempt.Valid) (ready : before.RetainedReady directory descriptor) :
    after.RetainedReady directory descriptor ∧ after.wal.readDescriptors after.history.length = [after.wal.active] := by
  obtain ⟨next, exactEffect, nextReady, keeper⟩ := attempt.installsRetained observed ready
  exact (exactEffect.unique endpoint) ▸ ⟨nextReady, keeper⟩

end SegmentedCheckpointReport

end Alvoki.Storage.DiskSession
