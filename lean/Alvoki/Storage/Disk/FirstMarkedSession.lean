import Alvoki.Storage.Disk.BoundedSegmentSession
import Alvoki.Storage.Disk.WalSegmentFirstOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- One visible marker selects a contiguous suffix of canonical frames.
The keeper's visible contents can extend past the marker, while the
preceding selected segments contain exactly their claimed spans. -/
structure CanonicalKeeperLayout (image : FileImage) (history : List WAL.Write) where
  range : MarkedWalRange
  decoded : image.directory.active.walRange = some range
  through : range.through = history.length
  first : Nat
  sealed : List WalSegment
  keeper : WalSegment
  chain : WalSegment.Chain history first (sealed ++ [keeper])
  covers : first ≤ range.watermark
  tail : ByteArray
  visible : image.keeper.active = some (keeper.bytes ++ tail)

def CanonicalKeeperLayout.target {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) : Target where
  pair := image.directory.active
  range := layout.range
  decoded := layout.decoded
  first := layout.keeper.first
  firstCovered := layout.through ▸ layout.chain.startsWithin layout.keeper (by simp)
  trimmed := layout.keeper.bytes
  trimmedSize := by
    rw [layout.chain.keeperBytes, WAL.encode_size, List.length_drop, layout.through, Nat.mul_comm]

def CanonicalKeeperLayout.plan {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) : Plan :=
  ⟨layout.range.through, layout.keeper.first, image.later.visible, layout.keeper.bytes ++ layout.tail⟩

theorem CanonicalKeeperLayout.prepared {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history)
    (keeperChoices : image.keeper.crashImages ≠ [])
    (keptPrefix : ∀ bytes ∈ image.keeper.crashImages, ∃ tail, bytes = some (layout.keeper.bytes ++ tail))
    (later : image.later.Beyond layout.range.through) : Prepared image layout.target layout.plan :=
  ⟨rfl, ⟨keeperChoices, ⟨layout.tail, layout.visible⟩, keptPrefix⟩, later, rfl, rfl, rfl, layout.visible⟩

/-- After native path and marker admission, healthy reports at the actual
locked paths derive the first marked replay and the ready session. The
full keeper in the inventory is a proof witness. The bounded worker uses
only the reported prefix and physical size. Crash choices keep the same
keeper with a compatible prefix. The rotation handoff covers a successor
that can disappear before the directory barrier. -/
theorem runOpenWithInstallation_firstMarked {directory : DiskDirectory} {descriptor nextRef : Nat}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout before.image history) (ordered : WAL.OrdinalsFrom 1 history)
    (keeperChoices : before.image.keeper.crashImages ≠ [])
    (keptPrefix : ∀ bytes ∈ before.image.keeper.crashImages, ∃ tail, bytes = some (layout.keeper.bytes ++ tail))
    (later : before.image.later.Beyond layout.range.through)
    (observed : RetryInventory directory before.image layout.target)
    {scanned : List Nat} (scan : observed.listing.offsets = .ok scanned)
    (sealed : observed.sealed = layout.sealed.map fun segment => (segment.first, segment.bytes))
    (olderBefore : ∀ start ∈ observed.older, start < layout.first)
    (following : ∀ start ∈ (observed.sealed.map Prod.fst ++ [layout.keeper.first]).drop 1,
      layout.range.watermark < start ∧ start ≤ layout.range.through)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (manifestRead : observed.listing.reports.readOptional (directory.file .manifest) =
      .ok before.image.directory.active.manifest)
    (runReads : ∀ bytes manifest, before.image.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
        (observed.listing.reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
          published.durable manifest.header.generation index)
    (markerRead : observed.listing.reports.readOptional (directory.file .walBoundary) =
      .ok before.image.directory.active.walBoundary)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (prefixRead : readPrefix (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size =
      .ok ⟨layout.keeper.bytes, (layout.keeper.bytes ++ layout.tail).size⟩)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves before.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] before.image = .ok () before.image.syncDirectory)
    (healthy : ∀ action prior next,
      ReachesAction layout.target before.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan removeFile throw write sync renameFile action prior = .ok () next) :
    let reports := observed.listing.reports
    let recover := reopenMarkedBoundedWith directory (fun path => liftExcept (reports.readOptional path))
      (fun _ => pure observed.entries) (fun path => pure (reports.lstat path))
      (fun path => liftExcept (reports.readBin path)) (fun path size => liftExcept (readPrefix path size))
      removeFile write sync renameFile
    ∃ checkpoint table model count session final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before = .ok session final ∧
      SelectedIntegrityCheckpoint published.durable before.image.directory.active.manifest checkpoint ∧
      session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready ⟨table, (checkpoint.getD (.empty, 0)).2, count.toNat, layout.keeper.first⟩ ∧
      before.image.directory.active.walBoundary = some (WAL.Boundary.encode count) ∧
      count.toNat = history.length * frameSize ∧ layout.keeper.bytes = WAL.encode (history.drop layout.keeper.first) ∧
      final.image.Ready layout.target ∧ before.owners (directory.file .lock) = none ∧
      final.owners.Owns directory descriptor ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs := by
  intro reports recover
  have prepared := layout.prepared keeperChoices keptPrefix later
  obtain ⟨checkpoint, table, model, count, selected, full, marker, absolute, keeper, committed, bounds, refines,
    represents, noPins⟩ := observed.prepareFirstMarked scan rfl layout.chain layout.tail layout.through ordered
      sealed rfl layout.visible layout.covers olderBefore following (later _ (List.mem_cons_self ..))
      accepted manifestRead runReads markerRead
  have keeperSize : layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
  have boundedRead : readPrefix (directory.file (.walSegment layout.plan.keeper)) layout.plan.keeperSize =
      .ok ⟨layout.plan.keeperBytes.extract 0 layout.plan.keeperSize, layout.plan.keeperBytes.size⟩ := by
    rw [keeperSize]
    change readPrefix (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size =
      .ok ⟨(layout.keeper.bytes ++ layout.tail).extract 0 layout.keeper.bytes.size,
        (layout.keeper.bytes ++ layout.tail).size⟩
    rw [ByteArray.extract_append_eq_left rfl]
    exact prefixRead
  obtain ⟨session, final, installed, path, lock, phase, stable, held, separate, phaseFresh, tokenFresh⟩ :=
    runOpenWithInstallation_bounded prepared liveRefs fresh acquisition unlock reports.readOptional
      (fun _ => .ok observed.entries) (fun path => .ok (reports.lstat path)) reports.readBin readPrefix full boundedRead
      removeFile write sync renameFile settles healthy
  exact ⟨checkpoint, table, model, count, session, final, installed, selected, path, lock, phase, marker, absolute,
    keeper, stable, acquisition rfl, held, committed, bounds, refines, represents, noPins, separate, phaseFresh,
    tokenFresh⟩

end Alvoki.Storage.DiskSession
