import Alvoki.Storage.Disk.NativeMarkedAdmissionRejections
import Alvoki.Storage.Disk.NativeRawWriteReboot
import Alvoki.Storage.Disk.NativeRotationErrorPowerLoss

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

section BeforeFlockRetry

variable {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
  {first entry reached : heap} {earlier : List (FilePath × IO.Error)}
  {prior : source.FailedCalls first earlier entry}
  {input : FilePath} {cause : IO.Error} {firstOffset through : Nat}

private abbrev retryLiveFiles (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨(storage atHeap).files.names, fun inode => [visible atHeap inode]⟩

private abbrev retryObservations (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState)
    (target : Target) (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (firstOffset through : Nat) (atHeap : heap) : Prop :=
  let names := fun atHeap => (storage atHeap).files.names
  let directory := state.session.directory
  state.writer.wal.NamespaceWindow directory firstOffset through (names atHeap) ∧
  RawOpenRetryTrace.KeeperAt view directory target names visible atHeap ∧
  state.SelectedRetryDurability target (storage atHeap) ∧
  RawOpenRetryTrace.LaterWalAt view directory target names atHeap

/-- Local read-only projections at the callbacks reached by an open
before flock. The extra WAL paths include absent names and the live
keeper, whose uncommitted tail does not have to be durable. -/
structure RawOpenRetryTrace.BeforeFlockFrame (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (before after : heap) : Prop where
  image : (view.files after).image = (view.files before).image
  live : (retryLiveFiles storage visible before).Frames
    (fun path => state.selectedRetryPath path ∨ ∃ start, path = state.session.directory.file (.walSegment start))
    (retryLiveFiles storage visible after)
  durable : (storage before).Frames state.selectedRetryPath (storage after)

private theorem RawOpenRetryTrace.BeforeFlockFrame.trans {before middle after : heap}
    (left : RawOpenRetryTrace.BeforeFlockFrame view state storage visible before middle)
    (right : RawOpenRetryTrace.BeforeFlockFrame view state storage visible middle after) :
    RawOpenRetryTrace.BeforeFlockFrame view state storage visible before after :=
  ⟨right.image.trans left.image, left.live.trans right.live, left.durable.trans right.durable⟩

/-- Add the literal path/metadata rejection before any next retry. The
actual pre-flock outcome determines the public diagnostic and reached
heap. When an append is reached, its error must supply its own frame. -/
theorem RawOpenRetryTrace.SelectedEffects.beforeFlock
    (before : RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
      state.selectedRetryPath (retryObservations view state target storage visible firstOffset through) prior)
    (failed : source.calls.beforeFlock input entry = .error cause reached)
    (effects : source.calls.BeforeFlockErrorFrames input entry cause reached
      (RawOpenRetryTrace.BeforeFlockFrame view state storage visible)) :
    ∃ returned : source.openTable input entry = .error cause reached,
      RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
        state.selectedRetryPath (retryObservations view state target storage visible firstOffset through)
        (prior.next input returned) := by
  obtain ⟨returned, rejected⟩ := source.returnsBeforeFlock failed
  have framed := rejected.framesRejected RawOpenRetryTrace.BeforeFlockFrame.trans effects
  refine ⟨returned, .append (calls := .next .empty input returned) before (.inl framed.image)
    (fun path selected => framed.live path (.inl selected)) ?_⟩
  intro carried
  let directory := state.session.directory
  have canonical (start : Nat) :
      (storage reached).files.names (directory.file (.walSegment start)) =
        (storage entry).files.names (directory.file (.walSegment start)) :=
    (framed.live _ (.inr ⟨start, rfl⟩)).1
  have keeperFrame := CheckpointSurvivingFiles.Frames.visiblePayload
    (names := fun atHeap => (storage atHeap).files.names) (bytes := visible) framed.live
    (path := directory.file (.walSegment target.first)) (.inr ⟨target.first, rfl⟩)
  have keeper := carried.2.1
  unfold RawOpenRetryTrace.KeeperAt at keeper
  refine ⟨carried.1.frame (fun start _ _ => congrArg Option.isSome (canonical start)), ?_,
    carried.2.2.1.frame framed.durable.visible
      (framed.durable.weaken (fun path root => .inr (.inl root))),
    carried.2.2.2.frame (congrArg (fun image : FileImage => image.later.visible) framed.image)
      (fun start _ => canonical start)⟩
  unfold RawOpenRetryTrace.KeeperAt
  rw [framed.image, keeper, keeperFrame]

end BeforeFlockRetry

/-- A read-only failed block and a failed repair both extend the retry
prefix. The read-only block frames the keeper that it entered with. -/
theorem RawOpenRetryTrace.SelectedEffects.readOnlyWithDurability
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
    {first entry reached : heap} {earlier more : List (FilePath × IO.Error)}
    {prior : source.FailedCalls first earlier entry}
    (before : RawOpenRetryTrace.SelectedEffects view source first target
      (fun atHeap => ⟨(storage atHeap).files.names, fun inode => [visible atHeap inode]⟩) state.selectedRetryPath
      (fun atHeap => RawOpenRetryTrace.KeeperAt view state.session.directory target
          (fun atHeap => (storage atHeap).files.names) visible atHeap ∧
        state.SelectedRetryDurability target (storage atHeap)) prior)
    (block : RawFinalizedOpenAttempts view state.session.directory source.calls source.init source.release entry more reached)
    (frame : state.SelectedRetryFrame (storage entry) (storage reached) (visible entry) (visible reached))
    (keeper : (⟨(storage entry).files.names, fun inode => [visible entry inode]⟩ : CheckpointSurvivingFiles).Frames
      (· = state.session.directory.file (.walSegment target.first))
      ⟨(storage reached).files.names, fun inode => [visible reached inode]⟩)
    (executed : source.FailedCalls entry more reached) :
    RawOpenRetryTrace.SelectedEffects view source first target
      (fun atHeap => ⟨(storage atHeap).files.names, fun inode => [visible atHeap inode]⟩) state.selectedRetryPath
      (fun atHeap => RawOpenRetryTrace.KeeperAt view state.session.directory target
          (fun atHeap => (storage atHeap).files.names) visible atHeap ∧
        state.SelectedRetryDurability target (storage atHeap)) (prior.append executed) :=
  before.readOnly block frame.live (fun carried =>
    ⟨block.keepsVisibleKeeper (target := target) keeper carried.1, carried.2.frame frame.durable frame.parent⟩) executed

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
  (effects.preserves initial.valid).2.2.2 physical

open WAL (frameSize)

/-- Reindex the namespace at the actual successor sampled by this
rotation reboot. Only that slot can add a canonical segment. -/
theorem NativeRotationErrorCrash.walNamespace {state : NativeReadyState}
    {diagnostic : Option IO.Error} {failure : NativeRotationDirectoryFailure state diagnostic}
    (crash : NativeRotationErrorCrash failure) (valid : state.Valid) {first through : Nat}
    {names : FilePath → Option Nat}
    (initial : state.writer.wal.NamespaceWindow state.session.directory first through names)
    (parentNames : ∀ start, first ≤ start → start ≤ through →
      names (state.session.directory.file (.walSegment start)) =
        (failure.parent.files.view.child failure.parent.root (renderWalSegmentName start)).map
          failure.parent.files.view.modelObject)
    (parentSettled : ∀ start, first ≤ start → start ≤ through →
      ∀ child ∈ failure.parent.files.crashNames (renderWalSegmentName start),
        child.isSome = (failure.parent.files.view.child failure.parent.root (renderWalSegmentName start)).isSome)
    (directoryChoices : ∀ start, first ≤ start → start ≤ through → start ≠ state.writer.installed.walBytes / frameSize →
      failure.reported.after.crashNames (renderWalSegmentName start) =
        if failure.reported.effective then
          [failure.created.files.view.child failure.parent.root (renderWalSegmentName start)]
        else failure.created.files.crashNames (renderWalSegmentName start)) :
    (crash.writer valid).wal.NamespaceWindow state.session.directory first through crash.names := by
  let wal := state.writer.wal
  let successor := state.writer.installed.walBytes / frameSize
  have sameEnd : wal.active.last = successor := valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
  have rotated : state.writer.wal.rotated.segments.map WalSegment.first = state.writer.wal.segments.map WalSegment.first ++ [successor] := by
    change (wal.segments ++ [(⟨wal.active.last, wal.active.last, ByteArray.empty⟩ : WalSegment)]).map WalSegment.first = _
    rw [List.map_append, List.map_cons, List.map_nil, sameEnd]
  have absent : successor ∉ wal.segments.map WalSegment.first := by
    intro listed
    obtain ⟨segment, present, eq⟩ := List.mem_map.mp listed
    have rotation := valid.retained.rotationInput failure.parent.nonempty
    rcases List.mem_append.mp present with sealed | active
    · exact Nat.ne_of_lt (Nat.lt_trans (rotation.sealedBefore segment sealed) rotation.nonempty)
        (eq.trans sameEnd.symm)
    · obtain rfl := List.mem_singleton.mp active
      exact Nat.ne_of_lt rotation.nonempty (eq.trans sameEnd.symm)
  have selected : (crash.names (state.session.directory.file (.walSegment successor))).isSome =
      crash.successor.isSome := by
    rw [state.session.directory.walSegment_path, crash.child, Option.isSome_map]
    rfl
  have frame (start : Nat) (lower : first ≤ start) (upper : start ≤ through) (other : start ≠ successor) :
      (crash.names (state.session.directory.file (.walSegment start))).isSome =
        (names (state.session.directory.file (.walSegment start))).isSome := by
    let name := renderWalSegmentName start
    change (crash.names (state.session.directory.file (.walSegment start))).isSome =
      (names (state.session.directory.file (.walSegment start))).isSome
    have separate : name ≠ renderWalSegmentName successor := by
      intro equal
      exact other (Option.some.inj (by simpa only [name, parseWalSegmentName_render] using congrArg parseWalSegmentName equal))
    have survived := crash.chosen name
    change crash.view.child failure.parent.root name ∈ failure.reported.after.crashNames name at survived
    rw [directoryChoices start lower upper other] at survived
    have sampled : crash.names (state.session.directory.file (.walSegment start)) =
        (crash.view.child failure.parent.root name).map crash.view.modelObject :=
      (congrArg crash.names (state.session.directory.walSegment_path start)).trans (crash.child name)
    rw [sampled, parentNames start lower upper, Option.isSome_map, Option.isSome_map]
    change (crash.view.child failure.parent.root name).isSome = (failure.parent.files.view.child failure.parent.root name).isSome
    dsimp only [name] at separate survived ⊢
    cases effective : failure.reported.effective with
    | false =>
      simp only [effective, Bool.false_eq_true, ↓reduceIte, failure.created.crashFrame _ separate] at survived
      exact parentSettled start lower upper _ survived
    | true =>
      simp only [effective, ↓reduceIte, List.mem_singleton, failure.created.names _ separate] at survived
      rw [survived]
  intro start lower upper
  by_cases atSuccessor : start = successor
  · subst start
    rw [selected]
    cases choice : crash.successor with
    | none => simpa only [NativeRotationErrorCrash.writer, choice, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, false_iff] using absent
    | some object =>
      simp only [NativeRotationErrorCrash.writer, choice, Option.isSome_some, ↓reduceIte,
        SegmentedWriterState.rotated, rotated, List.mem_append, List.mem_singleton, or_true]
  · rw [frame start lower upper atSuccessor]
    have original := initial start lower upper
    cases choice : crash.successor with
    | none => simpa only [NativeRotationErrorCrash.writer, choice, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte] using original
    | some object =>
      simpa only [NativeRotationErrorCrash.writer, choice, Option.isSome_some, ↓reduceIte,
        SegmentedWriterState.rotated, rotated, List.mem_append, List.mem_singleton, atSuccessor, or_false] using original


end Alvoki.Storage.DiskSession
