import Alvoki.Storage.Disk.Proofs.Recovery.FirstMarkedSession
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentBoundedOpenReports

namespace Alvoki.Storage

open System
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)
open DiskSession (CanonicalKeeperLayout)
open WalSegmentRepair

/-- Recovery cannot introduce later names. The authorization barrier
settles the initial empty listing, and subsequent modeled crashes can
only choose a surviving empty list. -/
theorem WalSegmentRepair.EffectTrace.emptyLater {target : Target} {initial after : FileImage}
    (trace : EffectTrace target initial after) (empty : initial.later.visible = []) :
    after.later.visible = [] := by
  suffices ∀ names ∈ after.later.visible :: after.later.crashImages, names = [] by
    exact this _ List.mem_cons_self
  induction trace with
  | authorized =>
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled, empty]
  | unlink prior _ ih =>
    intro names member
    simp only [FileImage.unlinkLater, LaterNames.unlink, List.mem_cons, List.mem_append, List.mem_map] at member
    rcases member with rfl | ⟨priorNames, allowed, rfl⟩ | allowed
    · rw [ih _ List.mem_cons_self]
      rfl
    · rw [ih _ (List.mem_cons_of_mem _ allowed)]
      rfl
    · exact ih _ (List.mem_cons_of_mem _ allowed)
  | syncPruned prior ih =>
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled, ih _ List.mem_cons_self]
  | replace prior gone ran ih =>
    unfold FileImage.replacementCut at ran
    obtain ⟨keeper, applies, rfl⟩ := Option.map_eq_some_iff.mp ran
    split
    · simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled, ih _ List.mem_cons_self]
    · exact ih
  | aligned prior gone exactRead ih => exact ih
  | scratch prior ih => exact ih
  | crash prior metadataSurvives keeperSurvives laterSurvive ih =>
    simp [FileImage.crash, LaterNames.settled, ih _ (List.mem_cons_of_mem _ laterSurvive)]

/-- Reconstruct a canonical visible layout after an authorized repair or
power-loss cut. The selected history and exact sealed map are unchanged.
The retry plan describes the newly visible keeper bytes and later names. -/
theorem WalSegmentRepair.EffectTrace.canonicalRetryLayout {initial after : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout initial history)
    (trace : EffectTrace layout.target initial after)
    (prepared : Prepared initial layout.target layout.plan) :
    ∃ retry : CanonicalKeeperLayout after history,
      retry.target = layout.target ∧ retry.range = layout.range ∧ retry.first = layout.first ∧
      retry.sealed = layout.sealed ∧ retry.keeper = layout.keeper ∧ after.kept = initial.kept ∧
      Prepared after layout.target retry.plan := by
  have durable := trace.valid prepared.pair prepared.keeperPrefix prepared.newer
  obtain ⟨tail, visible⟩ := durable.keeper.activeValid
  let retry : CanonicalKeeperLayout after history :=
    { range := layout.range
      decoded := durable.selected.symm ▸ layout.decoded
      through := layout.through
      first := layout.first
      sealed := layout.sealed
      keeper := layout.keeper
      chain := layout.chain
      covers := layout.covers
      tail := tail
      visible := visible }
  have sameTarget : retry.target = layout.target := by
    simp [CanonicalKeeperLayout.target, retry, durable.selected]
  exact ⟨retry, sameTarget, rfl, rfl, rfl, rfl, trace.keepsSealed,
    ⟨durable.selected, durable.keeper, durable.later, rfl, rfl, rfl, visible⟩⟩

namespace DiskSession

/-- The worker returns just the selected bytes, separately from the size of
the physical keeper described by the full repair plan. -/
def CanonicalKeeperLayout.boundedPlan {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) : Plan :=
  { layout.plan with keeperBytes := layout.keeper.bytes }

/-- The canonical keeper prefix satisfies the byte bound. The bounded plan
is valid when every listed suffix offset lies beyond the marker. -/
theorem CanonicalKeeperLayout.boundedPlan_valid {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history)
    (later : ∀ ordinal ∈ layout.boundedPlan.newer, layout.range.through < ordinal) :
    layout.boundedPlan.valid = true :=
  (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq layout.target.trimmedSize.symm, later⟩

theorem CanonicalKeeperLayout.boundedPlan_extractKeeper {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) :
    layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize = layout.keeper.bytes := by
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  rw [← size]
  exact ByteArray.extract_zero_size

theorem CanonicalKeeperLayout.boundedPlan_eq_extract {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) :
    layout.boundedPlan = { layout.plan with keeperBytes := layout.plan.keeperBytes.extract 0 layout.plan.keeperSize } := by
  have size : layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
  rw [size]
  unfold CanonicalKeeperLayout.boundedPlan CanonicalKeeperLayout.plan
  rw [ByteArray.extract_append_eq_left rfl]

/-- The bounded worker reads the same strict checkpoint and applies the
same canonical history at every keeper survivor. Only its physical size
can change the returned repair metadata. -/
theorem CanonicalKeeperLayout.prepareBoundedFromReplay {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history)
    {wal : WalSegmentImage} (readLayout : wal.ReadLayout history)
    (sameKeeper : layout.keeper = wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (noLater : image.later.visible = [])
    {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)} {table : PackedTable}
    (selectedCheckpoint : SelectedIntegrityCheckpoint durable image.directory.active.manifest checkpoint)
    (ordered : WAL.OrdinalsFrom 1 history)
    (reference : recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table)
    {directory owners descriptor}
    (raw : HealthyBoundedWalReports directory owners descriptor wal image.directory.active layout.range.watermark
      durable layout.tail) :
    prepareBoundedMarkedWith directory raw.reports.readOptional raw.list
      (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix =
      .ok (layout.boundedPlan,
        ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size.toUInt64, layout.keeper.first⟩,
        layout.plan.keeperBytes.size) := by
  obtain ⟨watermark, covered, marker, count, markerVisible, markerDecoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have clock := Option.some.inj (selectedCheckpoint.watermark.symm.trans watermark)
  have walRead := raw.readSelectedBounded readLayout layout.through covered absolute offsets
  have covers : layout.first ≤ (checkpoint.getD (.empty, 0)).1.committed.toNat := clock.symm ▸ layout.covers
  have counted : count.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have countBytes : count.toNat = (WAL.encode history).size := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  have countEq : count = (WAL.encode history).size.toUInt64 :=
    UInt64.ofNat_toNat.symm.trans (congrArg Nat.toUInt64 countBytes)
  have recovered := layout.chain.replaysMarked ByteArray.empty (layout.through ▸ absolute) covers ordered reference
  rw [ByteArray.append_empty] at recovered
  have sameFiles : layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(layout.keeper.first, layout.keeper.bytes)] =
        (wal.readDescriptors layout.range.watermark).map (fun segment => (segment.first, segment.bytes)) := by
    rw [← descriptors, List.map_append]
    rfl
  rw [sameFiles] at recovered
  have keeperRead : ((wal.readDescriptors layout.range.watermark).map
      (fun segment => (segment.first, segment.bytes))).getLast? =
    some (layout.keeper.first, layout.keeper.bytes) := by rw [← descriptors, List.map_append]; simp
  have bounded := prepareBoundedMarkedWith_reported directory raw.reports.readOptional raw.list
    (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix (raw.readCheckpoint selectedCheckpoint)
    (raw.marker.trans (congrArg Except.ok markerVisible)) markerDecoded
    (by rw [clock]; exact walRead) recovered keeperRead
  rw [counted, countEq] at bounded
  simpa only [CanonicalKeeperLayout.boundedPlan, CanonicalKeeperLayout.plan, noLater, sameKeeper] using bounded

/-- Exact bounded preparation derives the selected checkpoint, reference
table, row bounds and fresh pins from the same durable ordered run map.
Its purely canonical replay is independent of the unselected keeper tail. -/
theorem CanonicalKeeperLayout.prepareBoundedReports {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history)
    {wal : WalSegmentImage} (readLayout : wal.ReadLayout history)
    (sameKeeper : layout.keeper = wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (noLater : image.later.visible = [])
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {directory owners descriptor}
    (raw : HealthyBoundedWalReports directory owners descriptor wal image.directory.active layout.range.watermark
      published.durable layout.tail) :
    ∃ checkpoint table model,
      SelectedIntegrityCheckpoint published.durable image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
      prepareBoundedMarkedWith directory raw.reports.readOptional raw.list
        (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix =
        .ok (layout.boundedPlan,
          ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size.toUInt64, layout.keeper.first⟩,
          layout.plan.keeperBytes.size) ∧
      ((WAL.encode history).size.toUInt64).toNat = (WAL.encode history).size ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨watermark, _, _, count, _, _, absolute⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  have fits : (WAL.encode history).size < UInt64.size := byteCount ▸ count.toNat_lt_size
  obtain ⟨checkpoint, table, model, selectedCheckpoint, reference, committed, bounded, refines, represents, fresh⟩ :=
    selectedCheckpoint_replays watermark accepted fits ordered
  exact ⟨checkpoint, table, model, selectedCheckpoint, reference,
    layout.prepareBoundedFromReplay readLayout sameKeeper descriptors offsets noLater selectedCheckpoint ordered reference
      raw, UInt64.toNat_ofNat_of_lt' fits, committed, bounded, refines, represents, fresh⟩

end DiskSession

end Alvoki.Storage
