import Alvoki.Storage.Disk.AppendCutSession
import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.WalSegmentCheckpointReopen
import Alvoki.Storage.Disk.WalSegmentRotationReopen

namespace Alvoki.Storage.WalSegmentRotation

open DiskSession WalSegmentRepair

private theorem State.settleForReopen_visible (state : State) (image : WalSegmentImage) :
    state.settleForReopen.visible image = { state.visible image with directory := state.metadata.syncDirectory } := by
  by_cases absent : state.successor = .absent <;>
    simp [State.settleForReopen, State.visible, WalSegmentImage.rotated, absent]

theorem State.settledReopenImage_sync (state : State) (image : WalSegmentImage) :
    (state.settledReopenImage image).syncDirectory = state.settledReopenImage image := by
  simp only [State.settledReopenImage, State.visible_metadata, State.settleForReopen]
  rfl

/-- The surviving successor changes both the keeper and the sealed list.
Project to the fixed file image only after selecting this layout. -/
theorem State.crashReopenLayout (image : WalSegmentImage) (pair : DirectoryPublication.Bindings)
    (present : Bool) :
    let observed : State := ⟨.settled pair, if present then .durable else .absent⟩
    let retained := { image with directory := DirectoryPublication.Image.settled pair }
    observed.settleForReopen.visible image = if present then retained.rotated else retained := by
  cases present <;> rfl

/-- Use the keeper and sealed map only once the observed segment names are
settled. Before a barrier, a power loss must choose its surviving successor
in `WalSegmentRotation.Trace`. Its resulting state supplies its own layout. -/
theorem Trace.settledReopenLayout {initial : WalSegmentImage} {state : State} {history : List WAL.Write}
    (trace : Trace initial state) (rotation : CanRotate initial history) (layout : initial.ReadLayout history)
    (valid : initial.Valid history) {range : MarkedWalRange}
    (decoded : state.metadata.active.walRange = some range) (atEnd : range.through = history.length) :
    let wal := state.settleForReopen.visible initial
    let files := state.settledReopenImage initial
    wal.ReadLayout history ∧ wal.Valid history ∧ wal.active = (state.visible initial).active ∧
      files.directory.active = state.metadata.active ∧
      ∃ selected : CanonicalKeeperLayout files history,
        selected.range = range ∧ selected.keeper = wal.active ∧ selected.tail = ByteArray.empty ∧
        selected.sealed ++ [selected.keeper] = wal.readDescriptors range.watermark ∧
        selectWalSegmentReads (wal.segments.map WalSegment.first) range.watermark =
          some (selected.first, (wal.readDescriptors range.watermark).map WalSegment.first) ∧
        Prepared files selected.target selected.plan := by
  intro wal files
  have visible := state.settleForReopen_visible initial
  have stableLayout : wal.ReadLayout history := state.settleForReopen.visibleReadLayout rotation layout
  have stableValid : wal.Valid history := by
    intro pair chosen
    have same : pair = state.metadata.active := by
      simpa [wal, WalSegmentImage.Selects, State.visible_metadata, State.settleForReopen,
        DirectoryPublication.Image.syncDirectory] using chosen
    have earlier : (state.visible initial).Selects pair := by
      rw [WalSegmentImage.Selects, State.visible_metadata, same]
      exact List.mem_cons_self ..
    have admitted := (trace.preservesRecovery rotation valid).1 pair earlier
    simpa only [wal, visible, WalSegmentImage.afterWatermark] using admitted
  have samePair : wal.directory.active = state.metadata.active := by
    simp only [wal, State.visible_metadata, State.settleForReopen, DirectoryPublication.Image.syncDirectory]
  have exactFiles : files = wal.checkpointReopenFiles wal.directory none := rfl
  have observed : wal.CheckpointReopenDirectory wal.directory := .visible
  have stableRange : wal.directory.active.walRange = some range := samePair.symm ▸ decoded
  obtain ⟨selected, exactRange, keeper, tail, descriptors, offsets, _, choices, prefixes, later⟩ :=
    stableLayout.checkpointReopenLayout stableValid observed stableRange atEnd none
  have prepared := selected.prepared choices prefixes (exactRange.symm ▸ later)
  rw [exactFiles]
  exact ⟨stableLayout, stableValid, state.settleForReopen_keeper initial, samePair,
    selected, exactRange, keeper, tail, descriptors, offsets, prepared⟩

end Alvoki.Storage.WalSegmentRotation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Once the originating image is already settled, a bounded retry trace
with one canonical target is an extension of that authorization. -/
theorem BoundedReopenTrace.effectsAfterFixedAuthority {directory : DiskDirectory} {target : Target}
    {initial after : LockedFileState FileImage}
    (ran : BoundedReopenTrace directory (fun candidate => candidate = target) initial after)
    (fixed : initial.image.syncDirectory = initial.image) : EffectTrace target initial.image after.image := by
  have original : EffectTrace target initial.image initial.image := fixed ▸ .authorized
  have observed {current : FileImage} (before : BeforeReopenBarrier initial.image current) :
      EffectTrace target initial.image current := by
    cases before with
    | live => exact original
    | crash _ _ _ pair keeper names => exact .crash original pair keeper names
  cases ran.lineage (fun a b _ => a.trans b.symm) with
  | before source => exact observed source
  | repairing source canonical _ retry =>
    rw [canonical] at retry
    exact (observed source).trans retry

/-- Continue from a settled layout through failed opens, lock-reference
drops and power losses. The next healthy bounded open installs the exact
history and keeper chosen when the source layout obtained authority. -/
theorem BoundedReopenTrace.installsAfterFixedAuthority
    {directory : DiskDirectory} {initial retry : LockedFileState FileImage} {history : List WAL.Write}
    {wal : WalSegmentImage} (layout : wal.ReadLayout history) (ordered : WAL.OrdinalsFrom 1 history)
    (source : CanonicalKeeperLayout initial.image history) (sameKeeper : source.keeper = wal.active)
    (descriptors : source.sealed ++ [source.keeper] = wal.readDescriptors source.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) source.range.watermark =
      some (source.first, (wal.readDescriptors source.range.watermark).map WalSegment.first))
    (prepared : Prepared initial.image source.target source.plan)
    (fixed : initial.image.syncDirectory = initial.image) (emptyLater : initial.image.later.visible = [])
    (attempts : BoundedReopenTrace directory (fun candidate => candidate = source.target) initial retry)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      initial.image.directory.active.manifest)
    {generation : UInt64} (generationRead : ((initial.image.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok generation)
    {descriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    retry.image.kept = initial.image.kept ∧
    ∃ selected : CanonicalKeeperLayout retry.image history,
      selected.target = source.target ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor))
          descriptor wal retry.image.directory.active selected.range.watermark published.durable selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
        (∀ action prior next,
          ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
          prior.effect selected.target action = some next →
          performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
        AppendCutReady directory descriptor liveRefs history published retry.image selected.target generation
          (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
            (raw.reopen removeFile write sync renameFile) retry) := by
  have trace := attempts.effectsAfterFixedAuthority fixed
  obtain ⟨selected, target, range, first, sealed, keeper, kept, retryPrepared⟩ :=
    trace.canonicalRetryLayout source prepared
  have selectedPair := (trace.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.trans prepared.pair.symm
  refine ⟨kept, selected, target, ?_⟩
  intro raw settles healthy
  have selectedDescriptors : selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark := by
    rw [sealed, keeper, range]
    exact descriptors
  have selectedOffsets : selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
    rw [range, first]
    exact offsets
  exact runOpenWithInstallation_appendLayout layout ordered selected (keeper.trans sameKeeper) selectedDescriptors
    selectedOffsets (target.symm ▸ retryPrepared) (trace.emptyLater emptyLater)
    (by rw [selectedPair]; exact accepted) (by rw [selectedPair]; exact generationRead) raw liveRefs fresh acquisition
    unlock removeFile write sync renameFile settles healthy

end Alvoki.Storage.DiskSession
