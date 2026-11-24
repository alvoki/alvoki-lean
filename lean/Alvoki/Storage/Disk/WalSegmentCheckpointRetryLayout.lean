import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.WalSegmentBoundedRetry
import Alvoki.Storage.Disk.WalSegmentCheckpointReopen

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- Each allowed checkpoint selects the same acknowledged WAL and the
same exact keeper bytes. The pair fixes the checkpoint watermark. -/
def CheckpointRetryTarget (history : List WAL.Write) (first : Nat) (target : Target) : Prop :=
  target.first = first ∧ target.range.through = history.length ∧
    target.trimmed = WAL.encode (history.drop first)

theorem CheckpointRetryTarget.unique {history : List WAL.Write} {first : Nat}
    {left right : Target} (a : CheckpointRetryTarget history first left)
    (b : CheckpointRetryTarget history first right) (pair : left.pair = right.pair) : left = right := by
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  have start := a.1.trans b.1.symm
  have bytes := a.2.2.trans b.2.2.symm
  cases left
  cases right
  cases pair
  cases range
  cases start
  cases bytes
  rfl

end Alvoki.Storage.DiskSession

namespace Alvoki.Storage
open DiskSession WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

private theorem checkpointObservation {wal : WalSegmentImage} {directory : DirectoryPublication.Image}
    (observed : wal.CheckpointReopenDirectory directory) {scratch : Option (ByteArray × Bool)}
    {current : FileImage} (before : BeforeReopenBarrier (wal.checkpointReopenFiles directory scratch) current) :
    ∃ seen observedScratch, wal.CheckpointReopenDirectory seen ∧
      current = wal.checkpointReopenFiles seen observedScratch := by
  cases before with
  | live => exact ⟨directory, scratch, observed, rfl⟩
  | crash pair keeper later metadata payload names =>
    have exactKeeper : keeper = some wal.active.bytes := List.mem_singleton.mp payload
    have empty : later = [] := List.mem_singleton.mp names
    subst keeper
    subst later
    refine ⟨.settled pair, none, ?_, rfl⟩
    cases observed with
    | visible => exact .crash metadata
    | crash survives =>
      have exactPair := List.mem_singleton.mp metadata
      cases exactPair
      exact .crash survives

/-- Repair can stage only the checked bytes. If every keeper binding
already contains those bytes, all active and crash bindings stay exact. -/
private theorem WalSegmentRepair.EffectTrace.keeper_stays_exact {target : Target}
    {initial after : FileImage} (trace : EffectTrace target initial after)
    (keeper : initial.keeper.Valid (· = some target.trimmed)) :
    after.keeper.Valid (· = some target.trimmed) := by
  induction trace with
  | authorized => exact keeper
  | unlink _ _ ih | syncPruned _ ih => exact ih
  | scratch _ ih => exact ⟨ih.hasCrashImage, ih.activeValid, ih.crashValid⟩
  | replace _ _ ran ih =>
    unfold FileImage.replacementCut at ran
    obtain ⟨staged, executed, rfl⟩ := Option.map_eq_some_iff.mp ran
    have valid := Publication.Image.execute_cut_valid ih rfl _ executed
    split <;> exact valid
  | aligned _ _ _ ih =>
    refine ⟨by simp [FileImage.syncKeeper], ih.activeValid, ?_⟩
    intro candidate survives
    exact (List.mem_singleton.mp survives).trans ih.activeValid
  | crash _ _ keeperSurvives _ ih =>
    exact Publication.Image.settled_valid (ih.crashValid _ keeperSurvives)

/-- Before the first effective reopen barrier, power loss may still choose
a different manifest from the checkpoint cut. After the barrier, each
later attempt keeps the selected pair, its strict checkpoint, and exact
keeper bytes. The bounded plan can use the same sealed descriptors. -/
theorem CheckpointPublication.Image.checkpointRetryLayout
    {published : CheckpointPublication.Image} {before : WalSegmentImage} {history : List WAL.Write}
    (layout : (published.segmentedCheckpointView before).ReadLayout history)
    (valid : (published.segmentedCheckpointView before).Valid history)
    {directory : DirectoryPublication.Image}
    (observed : (published.segmentedCheckpointView before).CheckpointReopenDirectory directory)
    (inputs : ∀ pair, (published.segmentedCheckpointView before).Selects pair →
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = history.length)
    {scratch : Option (ByteArray × Bool)} {current : FileImage}
    (lineage : ReopenLineage ((published.segmentedCheckpointView before).checkpointReopenFiles directory scratch)
      (CheckpointRetryTarget history before.active.first) current) :
    let wal := published.segmentedCheckpointView before
    ∃ selected : CanonicalKeeperLayout current history,
      wal.Selects current.directory.active ∧ selected.keeper = before.active ∧ selected.tail = ByteArray.empty ∧
      selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark ∧
      selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
        some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
      Prepared current selected.target selected.plan ∧ current.later.visible = [] ∧
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
        current.directory.active.manifest := by
  intro wal
  have readChoice {image : FileImage}
      (choice : BeforeReopenBarrier (wal.checkpointReopenFiles directory scratch) image) :
      ∃ selected : CanonicalKeeperLayout image history,
        wal.Selects image.directory.active ∧ selected.keeper = before.active ∧ selected.tail = ByteArray.empty ∧
        selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark ∧
        selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
          some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
        Prepared image selected.target selected.plan ∧ image.later.visible = [] ∧
        image.keeper.Valid (· = some selected.target.trimmed) := by
    obtain ⟨seen, seenScratch, admitted, rfl⟩ := checkpointObservation observed choice
    have chosen := admitted.selectsActive
    obtain ⟨_, range, decoded, through⟩ := inputs seen.active chosen
    obtain ⟨selected, sameRange, keeper, noTail, descriptors, offsets, _, choices, keptPrefix, later⟩ :=
      layout.checkpointReopenLayout valid admitted decoded through seenScratch
    refine ⟨selected, chosen, keeper, noTail, sameRange.symm ▸ descriptors, sameRange.symm ▸ offsets,
      selected.prepared choices keptPrefix (sameRange.symm ▸ later), rfl, ?_⟩
    rw [show selected.target.trimmed = wal.active.bytes from congrArg WalSegment.bytes keeper]
    refine ⟨choices, rfl, ?_⟩
    intro candidate survives
    exact List.mem_singleton.mp survives
  cases lineage with
  | before choice =>
    obtain ⟨selected, chosen, keeper, tail, descriptors, offsets, prepared, empty, _⟩ := readChoice choice
    exact ⟨selected, chosen, keeper, tail, descriptors, offsets, prepared, empty, (inputs _ chosen).1⟩
  | repairing choice admitted prepared trace =>
    obtain ⟨selected, chosen, keeper, _, descriptors, offsets, sourcePrepared, empty, exactKeeper⟩ := readChoice choice
    have canonicalTarget : CheckpointRetryTarget history before.active.first selected.target := by
      have first := congrArg WalSegment.first keeper
      exact ⟨first, selected.through, first ▸ selected.chain.keeperBytes⟩
    have same := CheckpointRetryTarget.unique admitted canonicalTarget (prepared.pair.symm.trans sourcePrepared.pair)
    rw [same] at trace
    obtain ⟨retry, target, range, start, sealed, nextKeeper, _, retryPrepared⟩ :=
      trace.canonicalRetryLayout selected sourcePrepared
    have pair := (trace.valid sourcePrepared.pair sourcePrepared.keeperPrefix sourcePrepared.newer).selected
      |>.trans sourcePrepared.pair.symm
    have active : wal.Selects current.directory.active := pair.symm ▸ chosen
    have keeperBytes := (trace.keeper_stays_exact exactKeeper).activeValid
    have tail : retry.tail = ByteArray.empty := by
      have exactBytes := Option.some.inj (retry.visible.symm.trans keeperBytes)
      rw [nextKeeper] at exactBytes
      change selected.keeper.bytes ++ retry.tail = selected.keeper.bytes at exactBytes
      have length := congrArg ByteArray.size exactBytes
      rw [ByteArray.size_append] at length
      exact ByteArray.size_eq_zero_iff.mp (by omega)
    refine ⟨retry, active, nextKeeper.trans keeper, tail, ?_, ?_, target.symm ▸ retryPrepared,
      trace.emptyLater empty, (inputs _ active).1⟩
    · rw [range, sealed, nextKeeper]
      exact descriptors
    · rw [range, start]
      exact offsets

end Alvoki.Storage
