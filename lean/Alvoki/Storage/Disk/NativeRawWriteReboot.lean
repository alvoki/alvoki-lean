import Alvoki.Storage.Disk.NativeMutatingOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- One reported reboot selects a joint durable map at the reached failed
write. The new observations are made at the rebooted heap. The file
projection records the settled pair, keeper and visible later names, with
the immutable seal map supplied by the earlier writer. -/
structure RawWriteRebootEntry {heap : Type} (state : NativeReadyState) (view : OpenCloseHeapView heap FileImage)
    (storage : heap → CheckpointStorageObservation) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (failed rebooted : heap) : Prop where
  chosen : names rebooted ∈ (storage failed).crashNames
  sampled : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, names rebooted path = some inode → visible rebooted inode ∈ (storage failed).files.bytes inode
  image : let directory := state.session.directory
    (view.files rebooted).image = state.writer.files.crash
      ⟨(names rebooted (directory.file .manifest)).map (visible rebooted),
        (names rebooted (directory.file .walBoundary)).map (visible rebooted)⟩
      ((names rebooted (directory.file (.walSegment state.writer.wal.active.first))).map (visible rebooted))
      (view.files rebooted).image.later.visible
  noDescriptors : (view.descriptors rebooted).slots = []
  released : (view.files rebooted).owners = (view.files failed).owners.set (state.session.directory.file .lock) none

variable {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
  {visible : heap → Nat → ByteArray} {entry failed rebooted : heap}

/-- The same sampled manifest and protected inodes initialize the live
retry state. The marker can select either earlier history or the entire
uncertain batch, and a retained keeper may be longer than that marker. -/
theorem RawWriteRebootEntry.selectsRetry
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    (old : NativeReadyStorage state (storage entry))
    (frame : (storage entry).Frames state.writeFramePath (storage failed))
    {batch : List WAL.Write} {target : Target}
    (admitted : BatchRetryTarget state.writer.history batch state.writer.wal.active.first target)
    (select : names rebooted ∈ (storage failed).crashNames →
      (∀ path inode, (path = state.session.directory.file .manifest ∨ path = state.session.directory.file .walBoundary ∨
        path = state.session.directory.file (.walSegment state.writer.wal.active.first)) →
        names rebooted path = some inode → visible rebooted inode ∈ (storage failed).files.bytes inode) →
      target.pair = ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
        (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩ ∧
      target.Accepts ((names rebooted (state.session.directory.file (.walSegment state.writer.wal.active.first))).map
        (visible rebooted)))
    (later : ∀ first ∈ (view.files rebooted).image.later.visible, target.range.through < first) :
    RawOpenRetryTrace.SelectedEntry view state target names visible rebooted ∧
    TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
    (view.descriptors rebooted).slots = [] := by
  have sampled path
      (walPath : path = state.session.directory.file .manifest ∨ path = state.session.directory.file .walBoundary ∨
        path = state.session.directory.file (.walSegment state.writer.wal.active.first)) :=
    seen.sampled path (walPath.elim Or.inl (fun wal => .inr (.inl (wal.imp_right Or.inl))))
  obtain ⟨pair, keeper⟩ := select seen.chosen (fun path inode scope => sampled path scope inode)
  have start : target.first = state.writer.wal.active.first := admitted.1
  have manifest := old.selectedWriteManifest frame _ seen.chosen _ (seen.sampled _ (.inl rfl))
  have sameManifest := (congrArg DirectoryPublication.Bindings.manifest pair).trans manifest
  obtain ⟨root, lock, sealedFiles, runs⟩ :=
    old.retainsWriteRebootFiles frame _ seen.chosen _ seen.sampled
  let dir := state.session.directory
  have kept : NativeReadyProtectedStorage state ⟨names rebooted, fun inode => [visible rebooted inode]⟩ := by
    refine ⟨root, lock, ?_, ?_, ?_⟩
    · change (match state.writer.target.pair.manifest with
        | none => names rebooted (dir.file .manifest) = none
        | some bytes => ∃ inode, names rebooted (dir.file .manifest) = some inode ∧
            [visible rebooted inode] = [bytes])
      rw [← manifest]
      cases named : names rebooted (dir.file .manifest) with
      | none => rfl
      | some inode => exact ⟨inode, rfl, rfl⟩
    · intro segment member
      obtain ⟨inode, _, bound, content⟩ := sealedFiles segment member
      exact ⟨inode, bound, congrArg (fun bytes => [bytes]) content⟩
    · intro bytes metadata present decoded index within payload stored
      obtain ⟨inode, _, bound, content⟩ := runs bytes metadata present decoded index within payload stored
      exact ⟨inode, bound, congrArg (fun bytes => [bytes]) content⟩
  have selected : (view.files rebooted).image.directory.active = target.pair := by
    rw [seen.image]
    exact pair.symm
  have settled : (view.files rebooted).image.directory.crashImages = [target.pair] := by
    rw [seen.image]
    exact congrArg (fun pair => [pair]) pair.symm
  have keeperValid : (view.files rebooted).image.keeper.Valid target.Accepts := by
    rw [seen.image]
    refine ⟨by simp [FileImage.crash, Publication.Image.settled], keeper, ?_⟩
    intro bytes member
    exact (List.mem_singleton.mp member).symm ▸ keeper
  have laterValid : (view.files rebooted).image.later.Beyond target.range.through := by
    rw [seen.image]
    intro names member first contains
    have same : names = (view.files rebooted).image.later.visible := by
      simpa [FileImage.crash, LaterNames.settled] using member
    exact later first (same ▸ contains)
  refine ⟨⟨⟨selected, settled, keeperValid, laterValid⟩, ?_, sameManifest, kept, ?_, ?_⟩, ?_, seen.noDescriptors⟩
  · rw [seen.image]
    rfl
  · unfold RawOpenRetryTrace.KeeperAt
    rw [seen.image, start]
    rfl
  · exact (congrArg DirectoryPublication.Bindings.walBoundary pair).symm
  · rw [seen.released]
    intro path
    simp [LockOwners.set]

end Alvoki.Storage.DiskSession
