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

/-- A retry can change the keeper and later WAL names. The protected
files retain their live and durable bytes, and each surviving binding
of the database directory still comes from the earlier parent map. -/
structure NativeReadyState.SelectedRetryFrame (state : NativeReadyState)
    (before after : CheckpointStorageObservation) (beforeBytes afterBytes : Nat → ByteArray) : Prop where
  live : (⟨before.files.names, fun inode => [beforeBytes inode]⟩ : CheckpointSurvivingFiles).Frames
    state.selectedRetryPath ⟨after.files.names, fun inode => [afterBytes inode]⟩
  durable : before.files.Frames state.selectedRetryPath after.files
  parent : before.Frames (· = state.session.directory.path) after

theorem NativeReadyState.SelectedRetryFrame.refl (state : NativeReadyState)
    (atState : CheckpointStorageObservation) (bytes : Nat → ByteArray) :
    state.SelectedRetryFrame atState atState bytes bytes :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, .refl _ _⟩

theorem NativeReadyState.SelectedRetryFrame.trans {state : NativeReadyState}
    {first middle last : CheckpointStorageObservation} {firstBytes middleBytes lastBytes : Nat → ByteArray}
    (before : state.SelectedRetryFrame first middle firstBytes middleBytes)
    (after : state.SelectedRetryFrame middle last middleBytes lastBytes) :
    state.SelectedRetryFrame first last firstBytes lastBytes :=
  ⟨before.live.trans after.live, before.durable.trans after.durable, before.parent.trans after.parent⟩

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
    RawOpenRetryTrace.KeeperAt view state.session.directory target names visible rebooted ∧
      state.SelectedRetryDurability target (storage rebooted) := by
  let directory := state.session.directory
  have old := selected.protectedFiles
  refine ⟨selected.keeper, ⟨⟨(reset.bindings directory.path (.inl rfl)).trans old.directoryBound,
    (reset.bindings (directory.file .lock) (.inr (.inl rfl))).trans old.lockBound, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
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

/-- Carry a frame across a block of actual failed calls. The premise
sees each issued call's prefix in the full chronology and its actual
error and reached heap. -/
theorem RawMarkedOpenInterpreter.FailedCalls.framesAfter
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {first entry reached : heap} {lead more : List (FilePath × IO.Error)}
    (block : source.FailedCalls entry more reached) (previousCalls : source.FailedCalls first lead entry)
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (each : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
      source.FailedCalls first prior before → List.IsPrefix (prior ++ [(input, cause)]) (lead ++ more) →
      source.openTable input before = .error cause after → frame before after) :
    frame entry reached := by
  induction block with
  | empty => exact refl _
  | @next earlier before after cause previous input returned ih =>
    have extended : List.IsPrefix (lead ++ earlier) (lead ++ (earlier ++ [(input, cause)])) := by
      rw [← List.append_assoc]
      exact List.prefix_append ..
    have initial := ih (fun ran inside result => each ran (inside.trans extended) result)
    have last := each (previousCalls.append previous) (by rw [List.append_assoc]; exact List.prefix_rfl) returned
    exact trans initial last

section CheckpointRetry

variable {rebooted reached : heap} {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
  {errors : List (FilePath × IO.Error)}

/-- Carry actual durable payloads of the sampled files and settlement
of the root's name in its parent through the same failed calls. -/
theorem RawMarkedOpenInterpreter.FailedCalls.carriesCheckpointReset
    (attempts : source.FailedCalls rebooted errors reached)
    (observe : heap → CheckpointStorageObservation) (scope : FilePath → Prop) (root : FilePath)
    (sample : CheckpointSurvivingFiles) (rootSelected : scope root)
    (reset : sample.Frames scope (observe rebooted).files)
    (rootReset : ∀ names ∈ (observe rebooted).crashNames, names root = sample.names root)
    (each : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
      source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(input, cause)]) errors →
      source.openTable input before = .error cause after →
      (observe before).files.Frames scope (observe after).files ∧
      (observe before).Frames (· = root) (observe after)) :
    sample.Frames scope (observe reached).files ∧
    ∀ names ∈ (observe reached).crashNames, names root = (observe reached).files.names root := by
  obtain ⟨files, parent⟩ := attempts.framesAfter .empty
    (fun before after =>
      (observe before).files.Frames scope (observe after).files ∧
      (observe before).Frames (· = root) (observe after))
    (fun atHeap => ⟨(CheckpointStorageObservation.Frames.refl scope (observe atHeap)).visible, .refl _ _⟩)
    (fun first next => ⟨first.1.trans next.1, first.2.trans next.2⟩)
    (fun prior inside ran => each prior (by simpa only [List.nil_append] using inside) ran)
  refine ⟨reset.trans files, fun names included => parent.settledFrom ?_ names included root rfl⟩
  intro survivor allowed name onlyRoot
  subst name
  exact (rootReset survivor allowed).trans (reset root rootSelected).1.symm


end CheckpointRetry

/-- Add the durable file observation to an existing retry carrier.
The same selected-effects proof still controls the keeper and logical
image. The extra physical laws apply only to the actual failed calls. -/
theorem RawOpenRetryTrace.SelectedEffects.withDurableFrames
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
    {first reached : heap} {returns : List (FilePath × IO.Error)}
    {files : heap → CheckpointSurvivingFiles} {protectedPaths : FilePath → Prop} {keep : heap → Prop}
    {attempts : source.FailedCalls first returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source first target files protectedPaths keep attempts)
    (each : ∀ {earlier : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
      source.FailedCalls first earlier before → List.IsPrefix (earlier ++ [(input, cause)]) returns →
      source.openTable input before = .error cause after →
      (storage before).files.Frames state.selectedRetryPath (storage after).files ∧
      (storage before).Frames (· = state.session.directory.path) (storage after)) :
    RawOpenRetryTrace.SelectedEffects view source first target files protectedPaths
      (fun heap => keep heap ∧ state.SelectedRetryDurability target (storage heap)) attempts := by
  induction effects with
  | empty => exact .empty
  | @append earlier more entry reached prior block before image kept inodes carries ih =>
    have previous := ih (fun ran inside result => each ran (List.prefix_append_of_prefix inside) result)
    let frame (entry reached : heap) :=
      (storage entry).files.Frames state.selectedRetryPath (storage reached).files ∧
      (storage entry).Frames (· = state.session.directory.path) (storage reached)
    obtain ⟨footprint, parent⟩ := block.framesAfter prior frame
      (fun heap => ⟨(CheckpointStorageObservation.Frames.refl _ (storage heap)).visible, .refl _ _⟩)
      (fun first last => ⟨first.1.trans last.1, first.2.trans last.2⟩) each
    exact .append (calls := block) previous image kept inodes (fun selected => ⟨carries selected.1, selected.2.frame footprint parent⟩)

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
    (physical : RawOpenRetryTrace.KeeperAt view state.session.directory target names visible first ∧
      state.SelectedRetryDurability target (storage first)) :
    RawOpenRetryTrace.KeeperAt view state.session.directory target names visible reached ∧
      state.SelectedRetryDurability target (storage reached) :=
  (effects.preserves initial.valid).2.2.2.2 physical

end Alvoki.Storage.DiskSession
