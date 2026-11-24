import Alvoki.Storage.Disk.SegmentedCheckpointStep
import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.WalSegmentCheckpointRetryLayout
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair CheckpointPublication
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The checkpoint has passed preparation and issued its current file
operation. The earlier callbacks returned successfully. The physical
observation records whether the current operation's modeled effect took
place before power loss. The current operation has no returned outcome. -/
structure CheckpointPowerCut (directory : DiskDirectory) (before : SegmentedWriterState) where
  checkpoint : SegmentedCheckpointReport directory before
  flushed : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok checkpoint.table
  generationFits : before.installed.generation.toNat + 1 < UInt64.size
  runCountFits : checkpoint.table.runs.length < UInt64.size
  encoded : encodeCheckpointIntegrityManifest checkpoint.table (SegmentedCheckpointReport.generation before) =
    .ok checkpoint.manifest
  completed : List CheckpointPublication.Step
  current : CheckpointPublication.Step
  remaining : List CheckpointPublication.Step
  schedule : CheckpointPublication.steps checkpoint.table.runs.length = completed ++ current :: remaining
  observed : ReachedFileReports checkpoint.report checkpoint.perform completed 0
  state : Nat
  returned : (completed.forM checkpoint.perform) 0 = .ok () state
  tookEffect : Bool
  atCut : checkpoint.cut = state + (if tookEffect then 1 else 0)

namespace CheckpointPowerCut

variable {directory : DiskDirectory} {before : SegmentedWriterState}

/-- Only the current, already-issued primitive can add to the returned prefix. -/
theorem reachedCount (cut : CheckpointPowerCut directory before) :
    cut.checkpoint.cut = cut.completed.length + (if cut.tookEffect then 1 else 0) ∧
    cut.checkpoint.cut ≤ (CheckpointPublication.steps cut.checkpoint.table.runs.length).length := by
  have count : cut.state = cut.completed.length := by
    simpa only [Nat.zero_add] using cut.observed.success_length cut.returned
  have exactCut := cut.atCut
  rw [count] at exactCut
  refine ⟨exactCut, ?_⟩
  rw [exactCut, cut.schedule, List.length_append, List.length_cons]
  split <;> omega

/-- The publication projection changes directory metadata. It carries
the existing keeper, every sealed file, and later-name inventory. -/
def physical (before : SegmentedWriterState) (published : CheckpointPublication.Image) : FileImage :=
  { before.files with directory := (published.segmentedCheckpointView before.wal).directory }

/-- The operation's physical cut starts with the writer's exact WAL files. -/
theorem physical_eq (published : CheckpointPublication.Image)
    (ready : before.RetainedReady directory descriptor) :
    let wal := published.segmentedCheckpointView before.wal
    physical before published = wal.checkpointReopenFiles wal.directory before.files.keeper.staged := by
  intro wal
  have bytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have visible := ready.resumed.ready.keeper
  have stable := ready.resumed.ready.keeperDurable
  rw [bytes] at visible stable
  have keeper : before.files.keeper =
      { Publication.Image.settled (some before.wal.active.bytes) with staged := before.files.keeper.staged } := by
    change before.files.keeper =
      ⟨some before.wal.active.bytes, [some before.wal.active.bytes], before.files.keeper.staged⟩
    rw [← stable, ← visible]
  obtain ⟨visible, stable⟩ := ready.resumed.ready.pruned
  have later : before.files.later = .settled [] := by
    change before.files.later = ⟨[], [[]]⟩
    rw [← stable, ← visible]
  change (⟨wal.directory, before.files.kept, before.files.keeper, before.files.later⟩ : FileImage) =
    ⟨wal.directory, (before.wal.checkpointReopenFiles before.wal.directory none).kept,
      { Publication.Image.settled (some before.wal.active.bytes) with staged := before.files.keeper.staged },
      .settled []⟩
  rw [ready.sealedFiles, keeper, later]

theorem selectedGeneration {durable binding checkpoint}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint) :
    ((binding.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok (checkpoint.getD (.empty, 0)).2 := by
  cases selected with
  | absent => rfl
  | present decoded _ _ => rw [Option.mapM, decoded]; rfl

/-- The manifest selected by the retained writer cannot refer to the next in-range generation. -/
theorem freshGeneration (ready : before.RetainedReady directory descriptor)
    (fits : before.installed.generation.toNat + 1 < UInt64.size) :
    before.published.UnreachableVersioned (SegmentedCheckpointReport.generation before) := by
  have visible : before.published.manifest.active = before.target.pair.manifest := by
    rw [ready.manifestFiles]
    exact congrArg DirectoryPublication.Bindings.manifest ready.resumed.ready.selected
  have settled : before.published.manifest.crashImages = [before.published.manifest.active] := by
    simp [ready.manifestFiles, DirectoryPublication.Image.project, ready.resumed.ready.settled,
      ready.resumed.ready.selected]
  have loaded : (before.published.manifest.active = none ∧ before.installed.generation = 0) ∨
      ∃ bytes selected, before.published.manifest.active = some bytes ∧
        Manifest.VersionedCheckpoint.decode bytes = .ok selected ∧
        before.installed.generation = selected.header.generation := by
    have generation := CheckpointPowerCut.selectedGeneration ready.resumed.selected
    rw [← ready.resumed.generation, ← visible] at generation
    cases binding : before.published.manifest.active with
    | none =>
      rw [binding] at generation
      exact .inl ⟨rfl, (Except.ok.inj generation).symm⟩
    | some bytes =>
      rw [binding, Option.mapM] at generation
      cases strict : Manifest.IntegrityCheckpoint.decode bytes with
      | error cause => simp [strict, Functor.map, Except.map] at generation
      | ok manifest =>
        rw [strict] at generation
        exact .inr ⟨bytes, .integrity manifest, rfl, Manifest.VersionedCheckpoint.decode_integrity strict,
          (Except.ok.inj generation).symm⟩
  intro bytes chosen manifest decoded
  exact before.published.nextVersionedGeneration_unreachable_after_reopen before.installed.generation loaded fits
    bytes (by simpa only [CheckpointPublication.Image.settleVisible, Publication.Image.settled, ← settled] using chosen)
    manifest decoded

/-- A power loss during the actual checkpoint schedule ends the writer's
lock lifetime. Each surviving manifest selects its exact ordered durable
runs, and the same acknowledged WAL replays from that checkpoint. The
result also gives the first step of the ordinary bounded reopen trace. -/
theorem selectsAcknowledgedHistory (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory descriptor) :
    ∃ published, before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published ∧
      let wal := published.segmentedCheckpointView before.wal
      wal.ReadLayout before.history ∧ wal.Valid before.history ∧
      (∀ pair, wal.Selects pair →
        published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
          pair.manifest ∧ ∃ range, pair.walRange = some range ∧ range.through = before.history.length) ∧
      ∀ {pair}, pair ∈ wal.directory.crashImages →
        let files := physical before published
        let crashed := files.crash pair (some before.wal.active.bytes) []
        BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
          ⟨files, before.owners⟩ ⟨crashed, before.owners.set (directory.file .lock) none⟩ ∧
        crashed.directory.active.walBoundary = before.wal.directory.active.walBoundary ∧
        crashed.kept = before.files.kept ∧
        published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
          pair.manifest ∧
        ∃ range, pair.walRange = some range ∧ range.through = before.history.length ∧
          ∃ checkpoint table model, SelectedIntegrityCheckpoint published.durable pair.manifest checkpoint ∧
            (((checkpoint.getD (.empty, 0)).2 = before.installed.generation ∧
                pair.manifest = before.wal.directory.active.manifest) ∨
              ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation before ∧
                pair.manifest = some cut.checkpoint.manifest)) ∧
            recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok table ∧
            table.committed.toNat = before.history.length ∧ table.Refines model ∧
            RepresentsWalHistory before.history model := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have marker := congrArg Publication.Image.active ready.resumed.markerImage
  change before.files.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) at marker
  rw [ready.directoryFiles] at marker
  have priorGeneration := selectedGeneration ready.resumed.selected
  rw [← ready.resumed.generation, ← ready.walPair] at priorGeneration
  have projected : before.published.manifest = before.wal.directory.project .manifest := by
    rw [← ready.directoryFiles]
    exact ready.manifestFiles
  have strict (bytes : ByteArray) (binding : before.wal.directory.active.manifest = some bytes) :
      ∃ manifest, Manifest.IntegrityCheckpoint.decode bytes = .ok manifest := by
    have generation := priorGeneration
    rw [binding] at generation
    cases decoded : Manifest.IntegrityCheckpoint.decode bytes with
    | error cause => simp [decoded, Option.mapM, Functor.map, Except.map] at generation
    | ok parsed => exact ⟨parsed, rfl⟩
  obtain ⟨_, _, _, count, _, _, counted⟩ := DirectoryPublication.Bindings.walRange_accounting before.target.decoded
  have bytes : (WAL.encode before.history).size = count.toNat := by
    rw [counted, ready.resumed.through, WAL.encode_size, Nat.mul_comm]
  have walFits : (WAL.encode before.history).size < UInt64.size := bytes.symm ▸ count.toNat_lt_size
  have runBytesFit : ∀ bytes ∈ cut.checkpoint.table.runs.map (·.run.bytes), bytes.size < UInt64.size := by
    by_cases bounded : (cut.checkpoint.table.runs.map (·.run.bytes)).all
        (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact fun bytes member => of_decide_eq_true (List.all_eq_true.mp bounded bytes member)
    · have encoded := cut.encoded
      simp [encodeCheckpointIntegrityManifest, bounded, Bind.bind, Except.bind] at encoded
  let generation := SegmentedCheckpointReport.generation before
  let metadata := Manifest.IntegrityCheckpoint.fromRuns
    (checkpointHeader cut.checkpoint.table generation) (cut.checkpoint.table.runs.map (·.run.bytes))
  have written := (WrittenCheckpoint.of_flushForCheckpoint cut.flushed refined cut.runCountFits
    ready.resumed.bounds.runs ready.resumed.bounds.memory generation).1
  have exactManifest : cut.checkpoint.manifest = metadata.encode :=
    Except.ok.inj (cut.encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation runBytesFit))
  have decodedNew : Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata := by
    rw [exactManifest]
    exact Manifest.IntegrityCheckpoint.decode_encode metadata written.validFloor
      (by simpa [metadata, Manifest.IntegrityCheckpoint.fromRuns] using written.count)
  obtain ⟨published, executed⟩ := before.published.executeVersioned_exists cut.checkpoint.plan
    (cut.completed.length + (if cut.tookEffect then 1 else 0))
  rw [← cut.reachedCount.1] at executed
  obtain ⟨layout, valid, inputs⟩ := segmentedCheckpoint_cut ready.layout ready.valid ready.walDirectorySettled
    marker walFits projected (ready.walPair.symm ▸ ready.resumed.accepted) strict refined represented ready.resumed.bounds
    cut.flushed cut.runCountFits generation (freshGeneration ready cut.generationFits) runBytesFit executed
  refine ⟨published, executed, layout, valid, ?_, ?_⟩
  · intro pair chosen
    obtain ⟨_, _, accepted, _, range, _, decoded, through, _⟩ := inputs pair chosen
    exact ⟨accepted, range, decoded, through⟩
  intro pair survives files crashed
  obtain ⟨marker, choice, accepted, _, range, _, decoded, through, _⟩ :=
    inputs pair (List.mem_cons_of_mem _ survives)
  have keeperBytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have payload : some before.wal.active.bytes ∈ files.keeper.crashImages := by
    change some before.wal.active.bytes ∈ before.files.keeper.crashImages
    rw [ready.resumed.ready.keeperDurable, keeperBytes]
    exact List.mem_singleton_self _
  have names : [] ∈ files.later.crashImages := by
    change [] ∈ before.files.later.crashImages
    rw [ready.resumed.ready.pruned.2]
    exact List.mem_singleton_self _
  have trace : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨files, before.owners⟩ ⟨crashed, before.owners.set (directory.file .lock) none⟩ :=
    .powerLoss .empty survives payload names
  have watermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
  obtain ⟨checkpoint, table, replayedModel, selected, replayed, committed, _, refines, represents, _⟩ :=
    selectedCheckpoint_replays watermark accepted walFits ready.resumed.ordered
  have decided : ((checkpoint.getD (.empty, 0)).2 = before.installed.generation ∧
        pair.manifest = before.wal.directory.active.manifest) ∨
      ((checkpoint.getD (.empty, 0)).2 = generation ∧ pair.manifest = some cut.checkpoint.manifest) := by
    have read := selectedGeneration selected
    rcases choice with old | new
    · rw [old] at read
      exact .inl ⟨Except.ok.inj (read.symm.trans priorGeneration), old⟩
    · have exactNew : pair.manifest = some cut.checkpoint.manifest := by
        rw [exactManifest]
        exact new
      rw [exactNew, Option.mapM, decodedNew] at read
      exact .inr ⟨(Except.ok.inj read).symm, exactNew⟩
  exact ⟨trace, marker, rfl, accepted, range, decoded, through, checkpoint, table, replayedModel,
    selected, decided, replayed, committed, refines, represents⟩

end CheckpointPowerCut
end Alvoki.Storage.DiskSession
