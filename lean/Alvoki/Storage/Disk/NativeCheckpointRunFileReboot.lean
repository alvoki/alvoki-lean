import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryReboot
import Alvoki.Storage.Disk.NativeCheckpointRunFileStop

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  {stop : NativeCheckpointRunFileStop (image := image) state cut}

private theorem settledThroughFileEffect {path : FilePath}
    (separate : ∀ index ≤ stop.effect.index,
      path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (known : ∀ names ∈ (stop.effect.prior.views 0).crashBindings,
      names path = (stop.effect.prior.views 0).visible path) :
    ∀ names ∈ stop.effect.view.crashBindings, names path = stop.effect.view.visible path := by
  intro names possible
  obtain ⟨earlier, allowed, kept⟩ := stop.effect.frame.crashNames names possible
  have distinct := separate _ (Nat.le_refl _)
  have earlierSettled := stop.effect.prior.settledNameAtEnd
    (fun index within => separate index (Nat.le_of_lt within)) known earlier allowed
  exact (kept path distinct).trans (earlierSettled.trans (stop.effect.frame.visibleNames path distinct).symm)

/-- A single reboot choice for the reported stopped checkpoint effect.
The root, lock and WAL are observed once at checkpoint entry; the
returned run prefixes and the stopped run fsync preserve that authority. -/
structure NativeCheckpointRunFileReboot (stop : NativeCheckpointRunFileStop (image := image) state cut) where
  stableName : ∀ path, path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
      path = state.session.directory.file .manifest →
    ∀ names ∈ (stop.effect.prior.views 0).crashBindings, names path = (stop.effect.prior.views 0).visible path
  marker : ∃ inode, (stop.effect.prior.views 0).Stable (state.session.directory.file .walBoundary) inode
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  keeper : ∃ inode, (stop.effect.prior.views 0).Stable
    (state.session.directory.file (.walSegment state.writer.wal.active.first)) inode state.writer.wal.active.bytes
  seals : ∀ segment ∈ state.writer.wal.sealed, ∃ inode, (stop.effect.prior.views 0).Stable
    (state.session.directory.file (.walSegment segment.first)) inode segment.bytes
  names : FilePath → Option Nat
  chosen : names ∈ stop.effect.view.crashBindings
  contents : Nat → ByteArray
  durable : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, names path = some inode → contents inode ∈ (stop.effect.prior.inodes stop.effect.after).crashBytes inode
  rebootObjects : Nat → Nat

namespace NativeCheckpointRunFileReboot

variable (reboot : NativeCheckpointRunFileReboot stop)

include reboot in
private theorem markerStable : ∃ inode, stop.effect.view.Stable (state.session.directory.file .walBoundary) inode
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
  obtain ⟨inode, prior⟩ := reboot.marker
  exact ⟨inode, stop.effect.stableAfter (checkpointFixedNameNeRun _ (.inr (.inr rfl)) _ _)
    (stop.effect.prior.stablePath prior
      (fun index _ => checkpointFixedNameNeRun _ (.inr (.inr rfl)) _ index) _ (Nat.le_refl _))⟩

private theorem segmentStable {first : Nat} {bytes : ByteArray}
    (initial : ∃ inode, (stop.effect.prior.views 0).Stable (state.session.directory.file (.walSegment first)) inode bytes) :
    ∃ inode, stop.effect.view.Stable (state.session.directory.file (.walSegment first)) inode bytes := by
  obtain ⟨inode, stable⟩ := initial
  exact ⟨inode, stop.effect.stableAfter (checkpointSegmentNameNeRun _ first _ _)
    (stop.effect.prior.stablePath stable
      (fun index _ => checkpointSegmentNameNeRun _ first _ index) _ (Nat.le_refl _))⟩

/-- Project the stopped effect to the already supported marked-restart
input. The selected files and reboot observations are from this cut. -/
def observed (valid : state.Valid) : NativeReadyQuietCrash state where
  live := ⟨stop.effect.view.visible, (stop.effect.prior.inodes stop.effect.after).crashBytes⟩
  directoryBound := (stop.custody valid).2.2.2.2.1.trans (congrArg some stop.effect.prior.capturedInode)
  lockBound := (stop.custody valid).2.2.2.2.2
  manifest := by
    have equal : state.files.image.directory.active.manifest = state.writer.target.pair.manifest :=
      congrArg DirectoryPublication.Bindings.manifest valid.retained.resumed.ready.selected
    have stable := stop.effect.manifestAtEffect
    rw [stop.effect.filesAtEffect, equal] at stable
    cases selected : state.writer.target.pair.manifest <;> rw [selected] at stable
    · exact stable
    · obtain ⟨inode, _, path⟩ := stable
      exact ⟨inode, path.visibleBinding, path.crashBytes⟩
  marker := by
    obtain ⟨inode, retained⟩ := reboot.markerStable
    exact ⟨inode, retained.visibleBinding, retained.crashBytes⟩
  keeper := by
    obtain ⟨inode, retained⟩ := segmentStable reboot.keeper
    exact ⟨inode, retained.visibleBinding, retained.crashBytes⟩
  sealedFiles := fun segment member => by
    obtain ⟨inode, retained⟩ := segmentStable (reboot.seals segment member)
    exact ⟨inode, retained.visibleBinding, retained.crashBytes⟩
  runs := fun bytes metadata binding decoded index within payload stored => by
    obtain ⟨inode, _, retained⟩ := stop.effect.priorRunBytes valid
      ((congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair).trans binding) decoded within stored
    exact ⟨inode, retained.visibleBinding, retained.crashBytes⟩
  crashNames := stop.effect.view.crashBindings
  settled := by
    intro names possible path selected
    rcases selected with rfl | rfl | selected
    · exact settledThroughFileEffect (fun index _ => (file_ne_directory _ (.run _ index)).symm)
        (reboot.stableName _ (.inl rfl)) names possible
    · exact settledThroughFileEffect (fun index _ => checkpointFixedNameNeRun _ (.inl rfl) _ index)
        (reboot.stableName _ (.inr (.inl rfl))) names possible
    rcases selected with rfl | wal | ⟨payload, metadata, index, bound, decoded, within, rfl⟩
    · exact settledThroughFileEffect (fun index _ => checkpointFixedNameNeRun _ (.inr (.inl rfl)) _ index)
        (reboot.stableName _ (.inr (.inr rfl))) names possible
    · rcases wal with rfl | rfl | ⟨segment, member, rfl⟩
      · obtain ⟨_, retained⟩ := reboot.markerStable
        exact (retained.crashBinding names possible).trans retained.visibleBinding.symm
      · obtain ⟨_, retained⟩ := segmentStable reboot.keeper
        exact (retained.crashBinding names possible).trans retained.visibleBinding.symm
      · obtain ⟨_, retained⟩ := segmentStable (reboot.seals segment member)
        exact (retained.crashBinding names possible).trans retained.visibleBinding.symm
    have selected := valid.retained.resumed.selected
    have same := (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair).trans bound
    obtain ⟨stored, found⟩ := selected.runExists bound decoded within
    obtain ⟨_, _, retained⟩ := stop.effect.priorRunBytes valid same decoded within found
    exact (retained.crashBinding names possible).trans retained.visibleBinding.symm
  names := reboot.names
  chosen := reboot.chosen
  contents := reboot.contents
  durable := reboot.durable
  rebootObjects := reboot.rebootObjects

/-- The retained checkpoint and WAL derive the plan before any
callbacks of the next opener are supplied. -/
structure Plan (valid : state.Valid) where
  layout : CanonicalKeeperLayout (reboot.observed valid).retry.image state.writer.history
  target : layout.target = state.writer.target
  keeper : layout.keeper = state.writer.wal.active
  descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared (reboot.observed valid).retry.image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint state.writer.published.durable
    (reboot.observed valid).retry.image.directory.active.manifest state.writer.checkpoint

theorem plans (valid : state.Valid) : Nonempty (reboot.Plan valid) := by
  obtain ⟨layout, target, keeper, descriptors, offsets, prepared⟩ := valid.retained.powerLossLayout
  exact ⟨⟨layout, target, keeper, descriptors, offsets, prepared, valid.retained.resumed.selected⟩⟩

end NativeCheckpointRunFileReboot

end Alvoki.Storage.DiskSession
