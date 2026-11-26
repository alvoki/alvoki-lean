import Alvoki.Storage.Disk.NativeRawWriteReboot

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The immutable physical footprint of a selected retry. The keeper
can be trimmed or replaced during repair and has its own live relation.
The root's name in its parent must remain settled independently of any
fsync of the root's children. -/
structure NativeReadyState.SelectedRetryDurability (state : NativeReadyState) (target : Target)
    (storage : CheckpointStorageObservation) : Prop where
  protectedFiles : NativeReadyProtectedStorage state storage.files
  marker : ∀ bytes, target.pair.walBoundary = some bytes →
    storage.files.Stored (state.session.directory.file .walBoundary) bytes
  rootSettled : ∀ names ∈ storage.crashNames,
    names state.session.directory.path = storage.files.names state.session.directory.path

theorem NativeReadyState.SelectedRetryDurability.frame {state : NativeReadyState} {target : Target}
    {before after : CheckpointStorageObservation} (retained : state.SelectedRetryDurability target before)
    (files : before.files.Frames state.selectedRetryPath after.files)
    (parent : before.Frames (· = state.session.directory.path) after) :
    state.SelectedRetryDurability target after := by
  refine ⟨retained.protectedFiles.frame (fun path keep => files path (.inr keep)),
    fun bytes selected => files.stored (.inl rfl) (retained.marker bytes selected), ?_⟩
  have settled := parent.settledFrom (by
    intro names allowed path same
    exact same.symm ▸ retained.rootSettled names allowed)
  exact fun names allowed => settled names allowed _ rfl

variable {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
  {visible : heap → Nat → ByteArray} {failed rebooted : heap}

/-- At the observed reboot the same sampled names are live and every
selected regular file begins with its sampled bytes as its durable
choice. Later crash maps at this heap agree on those restored names. -/
structure RawWriteRebootEntry.DurableReset
    (_seen : RawWriteRebootEntry state view storage names visible failed rebooted) : Prop where
  bindings : ∀ path, state.crashPath path → (storage rebooted).files.names path = names rebooted path
  bytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, names rebooted path = some inode → (storage rebooted).files.bytes inode = [visible rebooted inode]
  crashBindings : ∀ surviving ∈ (storage rebooted).crashNames, ∀ path, state.crashPath path →
    surviving path = names rebooted path

private theorem RawWriteRebootEntry.DurableReset.stored
    {seen : RawWriteRebootEntry state view storage names visible failed rebooted}
    (reset : seen.DurableReset) {path : FilePath} {payload : ByteArray}
    (selected : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (rebootFile : (⟨names rebooted, fun inode => [visible rebooted inode]⟩ : CheckpointSurvivingFiles).Stored path payload) :
    (storage rebooted).files.Stored path payload := by
  obtain ⟨inode, bound, bytes⟩ := rebootFile
  exact ⟨inode, (reset.bindings path (.inr (.inr selected))).trans bound, (reset.bytes path selected inode bound).trans bytes⟩

/-- Project the already selected reboot into the actual physical
observation. This also retains sealed files older than the replay window. -/
theorem RawWriteRebootEntry.startsDurableRetry
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    (reset : seen.DurableReset) {target : Target}
    (selected : RawOpenRetryTrace.SelectedEntry view state target names visible rebooted) :
    state.SelectedRetryDurability target (storage rebooted) := by
  let directory := state.session.directory
  have old := selected.protectedFiles
  refine ⟨⟨(reset.bindings directory.path (.inl rfl)).trans old.directoryBound,
    (reset.bindings (directory.file .lock) (.inr (.inl rfl))).trans old.lockBound, ?_, ?_, ?_⟩, ?_, ?_⟩
  · cases manifest : state.writer.target.pair.manifest with
    | none =>
      have missing := old.manifest
      rw [manifest] at missing
      exact (reset.bindings (directory.file .manifest) (.inr (.inr (.inl rfl)))).trans missing
    | some bytes =>
      have stored := old.manifest
      rw [manifest] at stored
      exact reset.stored (.inl rfl) stored
  · intro segment member
    exact reset.stored (.inr (.inl (.inr (.inr ⟨segment, member, rfl⟩)))) (old.sealedFiles segment member)
  · intro bytes metadata present decoded index within payload stored
    exact reset.stored (.inr (.inr ⟨bytes, metadata, index, present, decoded, within, rfl⟩))
      (old.runs bytes metadata present decoded index within payload stored)
  · intro bytes marked
    obtain ⟨inode, bound, contents⟩ := Option.map_eq_some_iff.mp (selected.marker.trans marked)
    exact reset.stored (.inr (.inl (.inl rfl))) ⟨inode, bound, congrArg (fun bytes => [bytes]) contents⟩
  · intro surviving possible
    exact (reset.crashBindings surviving possible directory.path (.inl rfl)).trans
      (reset.bindings directory.path (.inl rfl)).symm

/-- Carry the immutable footprint alongside the mutable live keeper
through the same actual failed calls used for logical recovery. A read
failure or a failed repair can use its own local frame for the carrier. -/
theorem RawOpenRetryTrace.SelectedEffects.preservesDurability
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
    {first reached : heap} {returns : List (FilePath × IO.Error)}
    {attempts : source.FailedCalls first returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) state.selectedRetryPath
      (fun heap => RawOpenRetryTrace.KeeperAt view state.session.directory target names visible heap ∧
        state.SelectedRetryDurability target (storage heap)) attempts)
    (initial : RawOpenRetryTrace.SelectedEntry view state target names visible first)
    (durable : state.SelectedRetryDurability target (storage first)) :
    RawOpenRetryTrace.KeeperAt view state.session.directory target names visible reached ∧
      state.SelectedRetryDurability target (storage reached) :=
  (effects.preserves initial.valid).2.2.2.2 ⟨initial.keeper, durable⟩

end Alvoki.Storage.DiskSession
