import Alvoki.Storage.Disk.CheckpointCutSession
import Alvoki.Storage.Disk.WalSegmentCommitEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary

/-- The append worker sees the mutable tail and marker. Carry forward the
sealed files, other staged contents and later-name inventory from reopen. -/
def resumedAppendFiles (before : FileImage) (history : List WAL.Write) (first : Nat)
    (written : WriteFiles) : FileImage :=
  let after := written.reopenImage (history.drop first) before.directory.active.manifest
    (before.directory.staged .manifest) before.keeper.staged
  { before with directory := after.directory, keeper := after.wal }

theorem resumedAppendFiles_retains (before : FileImage) (history : List WAL.Write) (first : Nat)
    (written : WriteFiles) :
    let after := resumedAppendFiles before history first written
    after.kept = before.kept ∧ after.later = before.later ∧
      after.directory.staged .manifest = before.directory.staged .manifest ∧ after.keeper.staged = before.keeper.staged :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Reached callback reports for the append and marker replacement schedule.
The count is absolute. The append targets the installed keeper. -/
structure ResumedAppendReports (directory : DiskDirectory) (image : FileImage) (state : Installed)
    (history : List WAL.Write) (event : WAL.Write) (effects : WriteEffects)
    (append write : FilePath → ByteArray → EStateM Unit WriteFiles Unit)
    (sync : Array FilePath → EStateM Unit WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM Unit WriteFiles Unit) : Prop where
  appendReport :
    let initial := WriteFiles.initial history (image.directory.staged .walBoundary)
    append (directory.file (.walSegment state.activeFirst)) (WAL.encodeFrame event) initial =
      effects.appendFrame event initial
  markerReports :
    let initial := WriteFiles.initial history (image.directory.staged .walBoundary)
    let newBytes := state.walBytes + frameSize
    let marker := WAL.Boundary.encode newBytes.toUInt64
    ∀ appended, effects.appendFrame event initial = .ok () appended →
      ∀ prior step remaining files, Publication.steps = prior ++ step :: remaining →
      (prior.forM (effects.markerStep marker)) appended = .ok () files →
      WalSegmentCommit.performMarkerAt directory state.activeFirst newBytes write sync rename step files =
        effects.markerStep marker step files

/-- The exact state available for a later append or checkpoint. The loaded
checkpoint stays tied to its unchanged manifest and durable run map. -/
structure ResumedAppendReady (state : Installed) (image : FileImage) (target : Target)
    (history : List WAL.Write) (published : CheckpointPublication.Image)
    (checkpoint : Option (PackedTable × UInt64)) : Prop where
  ready : image.Ready target
  through : target.range.through = history.length
  keeper : state.activeFirst = target.first
  bytes : state.walBytes = (WAL.encode history).size
  contents : target.trimmed = WAL.encode (history.drop target.first)
  generation : state.generation = (checkpoint.getD (.empty, 0)).2
  selected : SelectedIntegrityCheckpoint published.durable target.pair.manifest checkpoint
  accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) target.pair.manifest
  ordered : WAL.OrdinalsFrom 1 history
  bounds : state.table.RowBounds
  canonical : ∃ model, state.table.Refines model ∧ RepresentsWalHistory history model

theorem ResumedAppendReady.markerImage {state : Installed} {image : FileImage} {target : Target}
    {history : List WAL.Write} {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    (before : ResumedAppendReady state image target history published checkpoint) :
    image.directory.project .walBoundary =
      (WriteFiles.initial history (image.directory.staged .walBoundary)).marker := by
  obtain ⟨_, _, marker, count, visible, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have size : count.toNat = (WAL.encode history).size := by
    rw [absolute, before.through, WAL.encode_size, Nat.mul_comm]
  have exactCount : count = (WAL.encode history).size.toUInt64 := by
    rw [← size, Nat.toUInt64, UInt64.ofNat_toNat]
  have exactMarker := visible.trans (congrArg some (WAL.Boundary.decode_reencode decoded).symm)
  simp only [DirectoryPublication.Image.project, before.ready.selected, before.ready.settled,
    DirectoryPublication.Bindings.get, exactMarker, exactCount, List.map_singleton]
  rfl

private theorem resumedWalRange {pair : DirectoryPublication.Bindings} {marker : ByteArray} {count : UInt64}
    {watermark through : Nat} (checkpoint : selectedCheckpointWatermark pair.manifest = some watermark)
    (visible : pair.walBoundary = some marker) (decoded : WAL.Boundary.decode marker = .ok count)
    (bytes : count.toNat = through * frameSize) (covered : watermark ≤ through) :
    pair.walRange = some ⟨watermark, through⟩ := by
  simp only [DirectoryPublication.Bindings.walRange, checkpoint, visible, decoded, Except.toOption,
    Bind.bind, Option.bind]
  rw [bytes, Nat.mul_mod_left, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  simp only [covered, and_self, ite_true]

private theorem resumedAppendTarget {image : FileImage} {target : Target} (ready : image.Ready target)
    {history : List WAL.Write} (through : target.range.through = history.length) {first : Nat}
    (starts : first ≤ history.length) (event : WAL.Write)
    (newBytes : Nat) (count : newBytes = (WAL.encode (history ++ [event])).size)
    (fits : newBytes < UInt64.size) {effects : WriteEffects} {written : WriteFiles}
    (reported : runWriteEffects history event effects (image.directory.staged .walBoundary) = .ok () written) :
    let extended := history ++ [event]
    let after := resumedAppendFiles image history first written
    ∃ nextTarget : Target,
      nextTarget.pair = ⟨target.pair.manifest, some (WAL.Boundary.encode newBytes.toUInt64)⟩ ∧
      nextTarget.range = ⟨target.range.watermark, extended.length⟩ ∧ nextTarget.first = first ∧
      nextTarget.trimmed = WAL.encode (extended.drop first) ∧ after.Ready nextTarget := by
  intro extended after
  obtain ⟨pairExact, settled, keeperExact, keeperDurable⟩ :=
    WalSegmentCommit.settledSegment_ofSuccess starts reported image.directory.active.manifest
  let pair : DirectoryPublication.Bindings := ⟨target.pair.manifest, some (WAL.Boundary.encode newBytes.toUInt64)⟩
  have exactPair : after.directory.active = pair := by
    change (⟨image.directory.active.manifest, written.marker.active⟩ : DirectoryPublication.Bindings) = _ at pairExact ⊢
    simpa only [pair, count, ready.selected, extended] using pairExact
  let range : MarkedWalRange := ⟨target.range.watermark, extended.length⟩
  have grows : history.length ≤ extended.length := by simp [extended]
  have decoded : pair.walRange = some range := by
    have watermark := (DirectoryPublication.Bindings.walRange_accounting target.decoded).1
    have covered := (DirectoryPublication.Bindings.walRange_accounting target.decoded).2.1
    have nextCovered : target.range.watermark ≤ extended.length := by
      rw [through] at covered
      exact Nat.le_trans covered grows
    have bytes : newBytes.toUInt64.toNat = extended.length * frameSize := by
      rw [UInt64.toNat_ofNat_of_lt' fits, count, WAL.encode_size, Nat.mul_comm]
    exact resumedWalRange (pair := pair) watermark rfl (WAL.Boundary.decode_encode _) bytes nextCovered
  let nextTarget : Target :=
    ⟨pair, range, decoded, first, Nat.le_trans starts grows,
      WAL.encode (extended.drop first), by rw [WAL.encode_size, List.length_drop, Nat.mul_comm]⟩
  exact ⟨nextTarget, rfl, rfl, rfl, rfl, exactPair, settled.trans (congrArg (fun binding => [binding]) exactPair),
    keeperExact, keeperDurable.trans (congrArg (fun bytes => [bytes]) keeperExact), ready.pruned⟩

/-- Once the native ready and stat checks have admitted the same stable
segment, a successful actual append schedule acknowledges the next ordinal
and leaves one durable marker and keeper image for the extended history. -/
theorem ResumedAppendReady.acknowledged {state : Installed} {image : FileImage} {target : Target}
    {history : List WAL.Write} {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    (before : ResumedAppendReady state image target history published checkpoint)
    (directory : DiskDirectory) {key : UInt64} {value : Option UInt64} {event : WAL.Write} {table : PackedTable}
    (prepared : prepareWrite state.table key value = some (event, table))
    (fits : state.walBytes + frameSize < UInt64.size) (effects : WriteEffects)
    (append write : FilePath → ByteArray → EStateM Unit WriteFiles Unit)
    (sync : Array FilePath → EStateM Unit WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM Unit WriteFiles Unit)
    (reports : ResumedAppendReports directory image state history event effects append write sync rename)
    {written : WriteFiles}
    (committed : WalSegmentCommit.commitAt directory state.activeFirst event (state.walBytes + frameSize)
      append write sync rename (WriteFiles.initial history (image.directory.staged .walBoundary)) = .ok () written) :
    let extended := history ++ [event]
    let after := resumedAppendFiles image history state.activeFirst written
    let next := { state with table, walBytes := state.walBytes + frameSize }
    event = ⟨table.committed, key, value⟩ ∧ event.sequence.toNat = history.length + 1 ∧ ∃ nextTarget,
      nextTarget.pair = ⟨target.pair.manifest, some (WAL.Boundary.encode next.walBytes.toUInt64)⟩ ∧
      nextTarget.range = ⟨target.range.watermark, extended.length⟩ ∧
      ResumedAppendReady next after nextTarget extended published checkpoint := by
  intro extended after next
  obtain ⟨model, refines, represents⟩ := before.canonical
  have clock : history.length = state.table.committed.toNat :=
    represents.committed_count.symm.trans (congrArg UInt64.toNat refines.committed).symm
  obtain ⟨fields, sequence, ordinal, _, length⟩ := prepareWrite_extends_history before.ordered clock prepared
  have count : state.walBytes + frameSize = (WAL.encode extended).size := by
    rw [before.bytes, length]
  have first : state.activeFirst ≤ history.length := by
    rw [before.keeper, ← before.through]
    exact target.firstCovered
  have modeled := (WalSegmentCommit.commitAt_reports directory state.activeFirst history event _ count effects
    (image.directory.staged .walBoundary) append write sync rename reports.appendReport reports.markerReports).symm.trans committed
  obtain ⟨nextTarget, pair, range, start, contents, ready⟩ :=
    resumedAppendTarget before.ready before.through first event _ count fits modeled
  have replayed : replay state.table [event] = .ok table := by
    change (replayWrite state.table event >>= fun table => Except.ok table) = .ok table
    rw [replay_prepared prepared]
    rfl
  obtain ⟨nextModel, replay, refined⟩ := replay_refines refines replayed
  have historyFits : (WAL.encode extended).size < UInt64.size := by rwa [← count]
  have accepted := published.acceptsVersioned_extend_history (suffix := [event]) before.accepted historyFits
  have nextReady : ResumedAppendReady next after nextTarget extended published checkpoint := by
    constructor
    · exact ready
    · exact congrArg MarkedWalRange.through range
    · exact start.symm
    · exact count
    · rw [contents, start]
    · exact before.generation
    · rw [pair]
      exact before.selected
    · rw [pair]
      exact accepted
    · exact ordinal
    · exact replay_rowBounds before.bounds replayed
    · exact ⟨nextModel, refined, represents.append replay⟩
  exact ⟨fields, by rw [fields]; exact sequence, nextTarget, pair, range, nextReady⟩

end Alvoki.Storage.DiskSession
