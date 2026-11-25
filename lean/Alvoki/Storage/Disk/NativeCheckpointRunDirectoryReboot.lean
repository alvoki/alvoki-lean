import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryStop
import Alvoki.Storage.Disk.NativeReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  {stop : NativeCheckpointRunDirectoryStop (image := image) state cut}

private theorem fixedNameNeRun (directory : DiskDirectory) {file : DiskFile}
    (fixed : file = .lock ∨ file = .manifest ∨ file = .walBoundary) (generation : UInt64) (index : Nat) :
    directory.file file ≠ directory.file (.run generation index) := by
  intro equal
  have bases := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
  have start := congrArg (fun name : String => name.toList.take 4) bases
  rcases fixed with same | same | same
  · subst file
    change "LOCK".toList.take 4 = ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at start
    simp [String.toList_append] at start
  · subst file
    change "MANIFEST".toList.take 4 = ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at start
    simp [String.toList_append] at start
  · subst file
    change "WAL.commit".toList.take 4 = ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at start
    simp [String.toList_append] at start

private theorem segmentNameNeRun (directory : DiskDirectory) (first : Nat) (generation : UInt64) (index : Nat) :
    directory.file (.walSegment first) ≠ directory.file (.run generation index) := by
  intro equal
  obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive equal.symm
  contradiction

/-- Returned run callbacks cannot change the binding of a different
name whose crash choices already agreed at the entered state. -/
private theorem settledThroughRunPrefix {path : FilePath}
    (separate : ∀ index < cut.checkpoint.table.runs.length,
      path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (known : ∀ names ∈ (stop.runs.views 0).crashBindings, names path = (stop.runs.views 0).visible path) :
    ∀ names ∈ stop.view.crashBindings, names path = stop.view.visible path := by
  have throughPrefix (through : Nat) (bound : through ≤ cut.checkpoint.table.runs.length) :
      ∀ names ∈ (stop.runs.views through).crashBindings, names path = (stop.runs.views through).visible path := by
    induction through with
    | zero => exact known
    | succ index previous =>
      intro names possible
      obtain ⟨_, _, _, _, _, _, _, frame⟩ := stop.runs.runReports index bound
      obtain ⟨earlier, allowed, kept⟩ := frame.crashNames names possible
      have distinct := separate index bound
      exact (kept path distinct).trans ((previous (Nat.le_of_lt bound) earlier allowed).trans
        (frame.visibleNames path distinct).symm)
  intro names possible
  have effect := stop.survivingNames names possible
  cases took : cut.tookEffect <;> simp only [took, Bool.false_eq_true, ite_false, ite_true] at effect
  · exact (throughPrefix _ (Nat.le_refl _) names effect).trans (congrFun stop.visibleNames path).symm
  · exact congrFun effect path

/-- A single reboot choice for the reported stopped checkpoint effect.
The root, lock and WAL are observed once at checkpoint entry; the
completed run frames and the stopped fsync transport that authority. -/
structure NativeCheckpointRunDirectoryReboot (stop : NativeCheckpointRunDirectoryStop (image := image) state cut) where
  stableName : ∀ path, path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
      path = state.session.directory.file .manifest →
    ∀ names ∈ (stop.runs.views 0).crashBindings, names path = (stop.runs.views 0).visible path
  marker : ∃ inode, (stop.runs.views 0).Stable (state.session.directory.file .walBoundary) inode
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  keeper : ∃ inode, (stop.runs.views 0).Stable
    (state.session.directory.file (.walSegment state.writer.wal.active.first)) inode state.writer.wal.active.bytes
  seals : ∀ segment ∈ state.writer.wal.sealed, ∃ inode, (stop.runs.views 0).Stable
    (state.session.directory.file (.walSegment segment.first)) inode segment.bytes
  names : FilePath → Option Nat
  chosen : names ∈ stop.view.crashBindings
  contents : Nat → ByteArray
  durable : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, names path = some inode → contents inode ∈ (stop.runs.inodes stop.reached).crashBytes inode
  rebootObjects : Nat → Nat

namespace NativeCheckpointRunDirectoryReboot

variable (reboot : NativeCheckpointRunDirectoryReboot stop)

include reboot in
private theorem markerStable : ∃ inode, stop.view.Stable (state.session.directory.file .walBoundary) inode
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
  obtain ⟨inode, prior⟩ := reboot.marker
  exact ⟨inode, stop.preservesStable (stop.runs.stablePath prior
    (fun index _ => fixedNameNeRun _ (.inr (.inr rfl)) _ index) _ (Nat.le_refl _))⟩

private theorem segmentStable {first : Nat} {bytes : ByteArray}
    (initial : ∃ inode, (stop.runs.views 0).Stable (state.session.directory.file (.walSegment first)) inode bytes) :
    ∃ inode, stop.view.Stable (state.session.directory.file (.walSegment first)) inode bytes := by
  obtain ⟨inode, stable⟩ := initial
  exact ⟨inode, stop.preservesStable (stop.runs.stablePath stable
    (fun index _ => segmentNameNeRun _ first _ index) _ (Nat.le_refl _))⟩

/-- Project the stopped effect to the already supported marked-restart
input. The selected files and reboot observations are from this cut. -/
def observed (valid : state.Valid) : NativeReadyQuietCrash state where
  live := ⟨stop.view.visible, (stop.runs.inodes stop.reached).crashBytes⟩
  directoryBound := (stop.custody valid).2.2.2.2.1.trans (congrArg some stop.runs.capturedInode)
  lockBound := (stop.custody valid).2.2.2.2.2
  manifest := by
    have equal : state.files.image.directory.active.manifest = state.writer.target.pair.manifest :=
      congrArg DirectoryPublication.Bindings.manifest valid.retained.resumed.ready.selected
    have stable := stop.manifestStable
    rw [equal] at stable
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
    obtain ⟨inode, _, retained⟩ := stop.priorRunStable valid
      ((congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair).trans binding) decoded within stored
    exact ⟨inode, retained.visibleBinding, retained.crashBytes⟩
  crashNames := stop.view.crashBindings
  settled := by
    intro names possible path selected
    rcases selected with rfl | rfl | selected
    · exact settledThroughRunPrefix (fun index _ => (file_ne_directory _ (.run _ index)).symm)
        (reboot.stableName _ (.inl rfl)) names possible
    · exact settledThroughRunPrefix (fun index _ => fixedNameNeRun _ (.inl rfl) _ index)
        (reboot.stableName _ (.inr (.inl rfl))) names possible
    rcases selected with rfl | wal | ⟨payload, metadata, index, bound, decoded, within, rfl⟩
    · exact settledThroughRunPrefix (fun index _ => fixedNameNeRun _ (.inr (.inl rfl)) _ index)
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
    obtain ⟨_, _, retained⟩ := stop.priorRunStable valid same decoded within found
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

end NativeCheckpointRunDirectoryReboot
end Alvoki.Storage.DiskSession
