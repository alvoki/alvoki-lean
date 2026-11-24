import Alvoki.Storage.Disk.FirstMarkedSession
import Alvoki.Storage.Disk.WalSegmentCheckpointPublication

namespace Alvoki.Storage

open WalSegmentRepair DiskSession
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Use the actual visible publication cut, or the directory produced by
a power loss that selected an admitted pair. A live retry keeps all of the
cut's metadata choices until its own directory barrier. -/
inductive WalSegmentImage.CheckpointReopenDirectory (wal : WalSegmentImage) :
    DirectoryPublication.Image → Prop where
  | visible : CheckpointReopenDirectory wal wal.directory
  | crash (survives : pair ∈ wal.directory.crashImages) :
      CheckpointReopenDirectory wal (.settled pair)

theorem WalSegmentImage.CheckpointReopenDirectory.selectsActive
    {wal : WalSegmentImage} {directory : DirectoryPublication.Image}
    (observed : wal.CheckpointReopenDirectory directory) : wal.Selects directory.active := by
  cases observed with
  | visible => exact List.mem_cons_self ..
  | crash survives => exact List.mem_cons_of_mem _ survives

/-- Checkpoint publication leaves the segment files settled. Keep the
observed metadata image separately because its manifest may be unsettled.
The repair scratch name has no bearing on the selected prefix. -/
def WalSegmentImage.checkpointReopenFiles (wal : WalSegmentImage)
    (directory : DirectoryPublication.Image) (scratch : Option (ByteArray × Bool)) : FileImage :=
  ⟨directory, fun first => (wal.sealed.find? (fun segment => segment.first == first)).map (·.bytes),
    { Publication.Image.settled (some wal.active.bytes) with staged := scratch }, .settled []⟩

private theorem findSealedStart {sealed : List WalSegment} {segment : WalSegment}
    (ordered : sealed.Pairwise (fun left right => left.first < right.first)) (present : segment ∈ sealed) :
    sealed.find? (fun item => item.first == segment.first) = some segment := by
  induction sealed with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · simp
    · obtain ⟨before, remaining⟩ := List.pairwise_cons.mp ordered
      have different : (first.first == segment.first) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (before segment later))
      simp [List.find?, different, ih remaining later]

/-- A published checkpoint leaves a fixed, exact keeper even when its
manifest is still unsettled. The selected checkpoint only changes how much
of the immutable sealed prefix is read. When the checkpoint covers the
whole history, recovery still selects the active file as its keeper. -/
theorem WalSegmentImage.ReadLayout.checkpointReopenLayout
    {wal : WalSegmentImage} {history : List WAL.Write} (layout : wal.ReadLayout history)
    (valid : wal.Valid history) {directory : DirectoryPublication.Image}
    (observed : wal.CheckpointReopenDirectory directory) {range : MarkedWalRange}
    (decoded : directory.active.walRange = some range) (atEnd : range.through = history.length)
    (scratch : Option (ByteArray × Bool)) :
    let files := wal.checkpointReopenFiles directory scratch
    ∃ selected : CanonicalKeeperLayout files history,
      selected.range = range ∧ selected.keeper = wal.active ∧ selected.tail = ByteArray.empty ∧
      selected.sealed ++ [selected.keeper] = wal.readDescriptors range.watermark ∧
      selectWalSegmentReads (wal.segments.map (·.first)) range.watermark =
        some (selected.first, (wal.readDescriptors range.watermark).map (·.first)) ∧
      (∀ segment ∈ selected.sealed, files.kept segment.first = some segment.bytes) ∧
      files.keeper.crashImages ≠ [] ∧
      (∀ bytes ∈ files.keeper.crashImages, ∃ tail, bytes = some (selected.keeper.bytes ++ tail)) ∧
      files.later.Beyond range.through := by
  intro files
  obtain ⟨first, covers, _, offsets, chain, _⟩ := layout.selects valid observed.selectsActive decoded
  let sealed := if range.watermark < wal.active.last then
    wal.sealed.filter (fun segment => decide (range.watermark < segment.last)) else []
  have descriptors : wal.readDescriptors range.watermark = sealed ++ [wal.active] := by
    by_cases prefixNeeded : range.watermark < wal.active.last
    · simp [WalSegmentImage.readDescriptors, WalSegmentImage.afterWatermark, sealed, prefixNeeded, List.filter_append]
    · simp [WalSegmentImage.readDescriptors, sealed, prefixNeeded]
  rw [descriptors] at chain
  let selected : CanonicalKeeperLayout files history :=
    ⟨range, decoded, atEnd, first, sealed, wal.active, chain, covers, ByteArray.empty,
      by simp [files, WalSegmentImage.checkpointReopenFiles, Publication.Image.settled]⟩
  refine ⟨selected, rfl, rfl, rfl, descriptors.symm, offsets, ?_, ?_, ?_, ?_⟩
  · intro segment referenced
    have inSealed : segment ∈ wal.sealed := by
      by_cases prefixNeeded : range.watermark < wal.active.last
      · have included : segment ∈ wal.sealed.filter (fun segment => decide (range.watermark < segment.last)) := by
          simpa [selected, sealed, prefixNeeded] using referenced
        exact (List.mem_filter.mp included).1
      · simp [selected, sealed, prefixNeeded] at referenced
    have ordered := ((List.pairwise_append.mp layout.ordered).1).imp (fun relation => relation.1)
    change (wal.sealed.find? (fun item => item.first == segment.first)).map (·.bytes) = _
    rw [findSealedStart ordered inSealed]
    rfl
  · simp [files, WalSegmentImage.checkpointReopenFiles, Publication.Image.settled]
  · intro bytes candidate
    have exactBytes : bytes = some wal.active.bytes := by
      simpa [files, WalSegmentImage.checkpointReopenFiles, Publication.Image.settled] using candidate
    exact ⟨ByteArray.empty, by simpa [selected] using exactBytes⟩
  · simp [files, WalSegmentImage.checkpointReopenFiles, LaterNames.settled, LaterNames.Beyond]

/-- The manifest selected by the repair image has exactly the acceptance
and ordered durable files certified by the checkpoint cut. An absent
manifest uses the same zero watermark as marked recovery. -/
theorem CheckpointPublication.Image.checkpointReopenInputs
    {published : CheckpointPublication.Image} {before : WalSegmentImage} {history : List WAL.Write}
    {directory : DirectoryPublication.Image}
    (observed : (published.segmentedCheckpointView before).CheckpointReopenDirectory directory)
    (scratch : Option (ByteArray × Bool)) :
    let wal := published.segmentedCheckpointView before
    let files := wal.checkpointReopenFiles directory scratch
    (∀ pair, wal.Selects pair →
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = history.length) →
    ∃ range, files.directory.active.walRange = some range ∧ range.through = history.length ∧
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
        files.directory.active.manifest ∧
      (∀ bytes, files.directory.active.manifest = some bytes → ∃ manifest ordered,
        Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧ manifest.header.committed.toNat = range.watermark ∧
        (List.range manifest.header.runCount.toNat).mapM (published.durable manifest.header.generation) = some ordered ∧
        manifest.validateRuns ordered = true) := by
  intro wal files inputs
  obtain ⟨accepted, range, decoded, through⟩ := inputs directory.active observed.selectsActive
  refine ⟨range, decoded, through, accepted, ?_⟩
  intro bytes visible
  change directory.active.manifest = some bytes at visible
  have watermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
  rw [visible] at watermark
  obtain ⟨manifest, parsed, clock⟩ := selectedCheckpointWatermark_present_iff.mp watermark
  have accepted : published.AcceptsVersioned history.length.toUInt64
      (CheckpointRepresentsPrefix history) (some bytes) := visible ▸ accepted
  obtain ⟨ordered, stored, _, checked, _⟩ :=
    published.acceptsVersioned_runs accepted (Manifest.VersionedCheckpoint.decode_integrity parsed)
  exact ⟨manifest, ordered, parsed, clock, stored, checked⟩

end Alvoki.Storage
