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

/-- The inode currently bound at the keeper path can be settled by the
next authorization barrier. Any of its durable payloads can be read. -/
def RawOpenRetryTrace.LiveKeeperCrashChoices (directory : DiskDirectory) (target : Target)
    (storage : CheckpointStorageObservation) : Prop :=
  ∃ inode, storage.files.names (directory.file (.walSegment target.first)) = some inode ∧
    ∀ payload ∈ storage.files.bytes inode, target.Accepts (some payload)

/-- Each joint namespace must retain a keeper whose durable bytes contain
the selected prefix. A replacement may have removed that inode's live name. -/
def RawOpenRetryTrace.KeeperCrashChoices (directory : DiskDirectory) (target : Target)
    (storage : CheckpointStorageObservation) : Prop :=
  ∀ names ∈ storage.crashNames, ∃ inode, names (directory.file (.walSegment target.first)) = some inode ∧
    ∀ payload ∈ storage.files.bytes inode, target.Accepts (some payload)

theorem RawOpenRetryTrace.LiveKeeperCrashChoices.frame {directory : DiskDirectory} {target : Target}
    {before after : CheckpointStorageObservation} {scope : FilePath → Prop}
    (kept : LiveKeeperCrashChoices directory target before) (framed : before.files.Frames scope after.files)
    (inside : scope (directory.file (.walSegment target.first))) : LiveKeeperCrashChoices directory target after := by
  obtain ⟨inode, bound, accepted⟩ := kept
  obtain ⟨name, bytes⟩ := framed _ inside
  exact ⟨inode, name.trans bound, fun payload present => accepted payload ((bytes inode bound) ▸ present)⟩

theorem RawOpenRetryTrace.KeeperCrashChoices.frame {directory : DiskDirectory} {target : Target}
    {before after : CheckpointStorageObservation} {scope : FilePath → Prop}
    (kept : KeeperCrashChoices directory target before) (framed : before.CrashFileFrame scope after)
    (inside : scope (directory.file (.walSegment target.first))) : KeeperCrashChoices directory target after := by
  intro names allowed
  obtain ⟨prior, earlier, same⟩ := framed.toFrames.survivors names allowed
  obtain ⟨inode, oldBound, accepted⟩ := kept prior earlier
  have bound := (same _ inside).trans oldBound
  exact ⟨inode, bound, fun payload present => accepted payload (framed.bytes names allowed _ inside inode bound payload present)⟩

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

/-- The live keeper chosen by the first reboot starts with one durable
payload and the same binding in every subsequent crash namespace. Its
accepted prefix comes from the selected retry target at the reboot heap. -/
theorem RawWriteRebootEntry.keeperCrashChoices
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    (reset : seen.DurableReset) {target : Target}
    (selected : RawOpenRetryTrace.SelectedEntry view state target names visible rebooted)
    (sameFirst : target.first = state.writer.wal.active.first) :
    RawOpenRetryTrace.LiveKeeperCrashChoices state.session.directory target (storage rebooted) ∧
      RawOpenRetryTrace.KeeperCrashChoices state.session.directory target (storage rebooted) := by
  let path := state.session.directory.file (.walSegment target.first)
  have survivorPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path :=
    .inr (.inl (.inr (.inl (congrArg (fun first => state.session.directory.file (.walSegment first)) sameFirst))))
  have inCrash : state.crashPath path := .inr (.inr survivorPath)
  obtain ⟨tail, trimmed⟩ := selected.valid.keeper.activeValid
  rw [selected.keeper] at trimmed
  obtain ⟨inode, bound, exactBytes⟩ := Option.map_eq_some_iff.mp trimmed
  have durable := reset.bytes path survivorPath inode bound
  have accepted : ∀ payload ∈ (storage rebooted).files.bytes inode, target.Accepts (some payload) := by
    intro payload present
    rw [durable] at present
    exact ⟨tail, congrArg some ((List.mem_singleton.mp present).trans exactBytes)⟩
  exact ⟨⟨inode, (reset.bindings path inCrash).trans bound, accepted⟩,
    fun names survives => ⟨inode, (reset.crashBindings names survives path inCrash).trans bound, accepted⟩⟩

/-- Storage observations needed at the next marked open. The immutable
files retain their durable contents. The keeper is read through the
current live binding, which a previous repair may have replaced. -/
abbrev RawOpenRetryTrace.RecoveryObservations (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState)
    (target : Target) (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (firstOffset through : Nat) (atHeap : heap) : Prop :=
  let names := fun atHeap => (storage atHeap).files.names
  let directory := state.session.directory
  state.writer.wal.NamespaceWindow directory firstOffset through (names atHeap) ∧
  RawOpenRetryTrace.KeeperAt view directory target names visible atHeap ∧
  state.SelectedRetryDurability target (storage atHeap) ∧
  RawOpenRetryTrace.LaterWalAt view directory target names atHeap

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

/-- Start the failed-call fold on the actual reset heap. The bounded
catalog and the later list use the same namespace as the sampled files. -/
theorem RawWriteRebootEntry.startsRecoveryObservations
    (seen : RawWriteRebootEntry state view storage (fun atHeap => (storage atHeap).files.names) visible failed rebooted)
    (reset : seen.DurableReset) {target : Target}
    (selected : RawOpenRetryTrace.SelectedEntry view state target
      (fun atHeap => (storage atHeap).files.names) visible rebooted)
    {firstOffset through : Nat}
    (window : state.writer.wal.NamespaceWindow state.session.directory firstOffset through (storage rebooted).files.names) :
    RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through rebooted :=
  ⟨window, selected.keeper, (seen.startsDurableRetry reset selected).2, seen.laterNames selected.valid.selected.symm⟩

/-- After a repair, the next power loss selects a single directory map.
The immutable files and marker keep their selected bindings on that map.
The keeper may name a different inode, whose sampled bytes must retain
the committed prefix. These facts re-establish the ordinary retry entry. -/
theorem RawWriteRebootEntry.selectsRetryAfterRepair
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    {target : Target} (first : target.first = state.writer.wal.active.first)
    (sameManifest : target.pair.manifest = state.writer.target.pair.manifest)
    (durable : state.SelectedRetryDurability target (storage failed))
    (bindings : ∀ path, state.selectedRetryPath path → path ≠ state.session.directory.path →
      names rebooted path = (storage failed).files.names path)
    (keeper : RawOpenRetryTrace.KeeperCrashChoices state.session.directory target (storage failed)) :
    RawOpenRetryTrace.SelectedEntry view state target names visible rebooted ∧
    TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
    (view.descriptors rebooted).slots = [] := by
  have selectedName (path : FilePath) (selected : state.selectedRetryPath path) :
      names rebooted path = (storage failed).files.names path := by
    by_cases root : path = state.session.directory.path
    · exact root ▸ durable.rootSettled _ seen.chosen
    · exact bindings path selected root
  obtain ⟨protectedFiles, manifest⟩ := durable.protectedFiles.samplesRebootFiles (names rebooted) (visible rebooted)
    (fun path inside => selectedName path (.inr inside)) seen.sampled
  obtain ⟨_, _, marker, _, present, _, _⟩ := DirectoryPublication.Bindings.walRange_accounting target.decoded
  let markerPath := state.session.directory.file .walBoundary
  obtain ⟨inode, named, contents⟩ := (durable.marker marker present).samplesAtBinding (names rebooted)
    (visible rebooted) (selectedName markerPath (.inl rfl)) (fun inode => seen.samplesWal markerPath inode (.inr (.inl rfl)))
  have marked : (names rebooted markerPath).map (visible rebooted) = target.pair.walBoundary := by
    rw [named, Option.map_some, contents, present]
  have pair : target.pair = ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
      (names rebooted markerPath).map (visible rebooted)⟩ := by
    change DirectoryPublication.Bindings.mk target.pair.manifest target.pair.walBoundary = _
    rw [sameManifest, manifest, marked]
  obtain ⟨keeperInode, keeperName, accepts⟩ := keeper (names rebooted) seen.chosen
  rw [first] at keeperName
  have bytes := seen.samplesWal _ keeperInode (.inr (.inr rfl)) keeperName
  apply seen.selectsSampledRetry first sameManifest protectedFiles pair
  rw [keeperName, Option.map_some]
  exact accepts _ bytes

/-- An exact keeper payload in the sampled namespace supplies the
canonical layout for the retained writer, with any observed later files. -/
theorem RawOpenRetryTrace.SelectedEntry.readyRebootLayout
    (selected : RawOpenRetryTrace.SelectedEntry view state state.writer.target names visible rebooted)
    (ready : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (payload : (names rebooted (state.session.directory.file (.walSegment state.writer.wal.active.first))).map
      (visible rebooted) = some state.writer.target.trimmed) :
    ∃ layout : CanonicalKeeperLayout (view.files rebooted).image state.writer.history,
      layout.target = state.writer.target ∧ layout.keeper = state.writer.wal.active ∧
      layout.tail = ByteArray.empty ∧
      layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark ∧
      selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
        some (layout.first, (layout.sealed ++ [layout.keeper]).map WalSegment.first) ∧
      Prepared (view.files rebooted).image layout.target layout.plan := by
  have active := selected.keeper
  unfold RawOpenRetryTrace.KeeperAt at active
  rw [ready.active] at active
  have activeBytes := active.trans payload
  obtain ⟨original, originalTarget, atKeeper, descriptors, offsets, _⟩ := ready.powerLossLayout
  let layout : CanonicalKeeperLayout (view.files rebooted).image state.writer.history := {
    range := original.range
    decoded := by
      rw [selected.valid.selected, ← originalTarget]
      exact original.decoded
    through := original.through
    first := original.first
    sealed := original.sealed
    keeper := original.keeper
    chain := original.chain
    covers := original.covers
    tail := .empty
    visible := by
      rw [ByteArray.append_empty]
      exact activeBytes.trans (congrArg (fun target : Target => some target.trimmed) originalTarget.symm)
  }
  have sameTarget : layout.target = state.writer.target :=
    (Target.eq_of_fields (selected.valid.selected.trans (congrArg Target.pair originalTarget).symm)
      rfl rfl rfl : layout.target = original.target).trans originalTarget
  have chosen : (view.files rebooted).image.Valid layout.target := sameTarget.symm ▸ selected.valid
  have prepared := layout.prepared chosen.keeper.hasCrashImage chosen.keeper.crashValid chosen.later
  refine ⟨layout, sameTarget, atKeeper, rfl, descriptors, ?_, prepared⟩
  rw [descriptors]
  exact offsets

/-- A settled writer has no uncertain batch to select. One sampled
reboot map carries its unchanged target and exact keeper into the next
open, together with the bounded namespace and reset durability. -/
theorem RawWriteRebootEntry.startsReadyRecovery
    (seen : RawWriteRebootEntry state view storage (fun atHeap => (storage atHeap).files.names) visible failed rebooted)
    (valid : state.Valid) (stable : NativeReadyStorage state (storage failed))
    (reset : seen.DurableReset) {firstOffset : Nat}
    (catalog : state.writer.wal.SettledNamespaceWindow state.session.directory firstOffset
      state.writer.target.range.through (storage failed)) :
    let names := fun atHeap => (storage atHeap).files.names
    let target := state.writer.target
    RawOpenRetryTrace.SelectedEntry view state target names visible rebooted ∧
    RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset target.range.through rebooted ∧
    TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ layout : CanonicalKeeperLayout (view.files rebooted).image state.writer.history,
      layout.target = target ∧ layout.keeper = state.writer.wal.active ∧ layout.tail = ByteArray.empty ∧
      layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark ∧
      selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
        some (layout.first, (layout.sealed ++ [layout.keeper]).map WalSegment.first) ∧
      Prepared (view.files rebooted).image layout.target layout.plan := by
  intro names target
  let directory := state.session.directory
  let path := directory.file (.walSegment state.writer.wal.active.first)
  let ready := valid.retained
  have marker : target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary ready.resumed.ready.selected).symm.trans
      (congrArg Publication.Image.active ready.resumed.markerImage)
  have durable : state.SelectedRetryDurability target (storage failed) :=
    ⟨stable.toNativeReadyProtectedStorage, fun _ bound => Option.some.inj (marker.symm.trans bound) ▸ stable.marker,
      fun names chosen => stable.settled names chosen _ (.inl rfl)⟩
  have bytes : target.trimmed = state.writer.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  obtain ⟨inode, live, payloads⟩ := stable.keeper
  have keeper (map) (chosen : map ∈ (storage failed).crashNames) : map path = some inode :=
    (stable.settled map chosen path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))).trans live
  have exactPayload {payload : ByteArray} (sampled : payload ∈ (storage failed).files.bytes inode) :
      payload = target.trimmed := by
    rw [payloads, ← bytes] at sampled
    exact List.mem_singleton.mp sampled
  have choices : RawOpenRetryTrace.KeeperCrashChoices directory target (storage failed) := by
    intro map allowed
    exact ⟨inode, ready.active.symm ▸ keeper map allowed, fun payload member =>
      exactPayload member ▸ target.acceptsTrimmed⟩
  obtain ⟨selected, vacant, empty⟩ := seen.selectsRetryAfterRepair ready.active rfl durable
    (fun path selected _ => stable.settled _ seen.chosen path
      (NativeReadyState.crashPath_iff_write.mpr (selected.imp_right Or.inr))) choices
  have bound : names rebooted path = some inode := keeper _ seen.chosen
  have contents := exactPayload (seen.samplesWal path inode (.inr (.inr rfl)) bound)
  have payload : (names rebooted path).map (visible rebooted) = some target.trimmed := by
    rw [bound, Option.map_some, contents]
  exact ⟨selected, seen.startsRecoveryObservations reset selected (catalog.2 _ seen.chosen), vacant, empty,
    selected.readyRebootLayout ready payload⟩

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

/-- A read-only retry block preserves the same scoped crash candidates
through the actual caller-visible errors. No restart has selected a new map. -/
theorem RawOpenRetryTrace.KeeperCrashChoices.afterFailedCalls
    {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {directory : DiskDirectory} {target : Target}
    {first reached : heap} {errors : List (FilePath × IO.Error)}
    (attempts : source.FailedCalls first errors reached)
    (observe : heap → CheckpointStorageObservation) (scope : FilePath → Prop)
    (inside : scope (directory.file (.walSegment target.first)))
    (live : LiveKeeperCrashChoices directory target (observe first))
    (crash : KeeperCrashChoices directory target (observe first))
    (each : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
      source.FailedCalls first prior before → List.IsPrefix (prior ++ [(input, cause)]) errors →
      source.openTable input before = .error cause after → (observe before).CrashFileFrame scope (observe after)) :
    LiveKeeperCrashChoices directory target (observe reached) ∧ KeeperCrashChoices directory target (observe reached) := by
  have framed := attempts.framesAfter .empty (fun before after => (observe before).CrashFileFrame scope (observe after))
    (fun atHeap => .refl scope (observe atHeap)) (fun first last => first.trans last)
    (fun prior inside returned => each prior (by simpa only [List.nil_append] using inside) returned)
  exact ⟨live.frame framed.toFrames.visible inside, crash.frame framed inside⟩

/-- A rejection before flock carries the survivor frame on the same
heap as the actual public error. The lock append error has its own law. -/
theorem RawMarkedOpenInterpreter.framesCrashFilesBeforeFlock {stream : Type}
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {before after : heap} {cause : IO.Error}
    (failed : source.calls.beforeFlock input before = .error cause after)
    (observe : heap → CheckpointStorageObservation) (scope : FilePath → Prop)
    (effects : source.calls.BeforeFlockErrorFrames input before cause after
      (fun entry reached => (observe entry).CrashFileFrame scope (observe reached))) :
    source.openTable input before = .error cause after ∧ (observe before).CrashFileFrame scope (observe after) :=
  source.framesBeforeFlock failed (frame := fun entry reached => (observe entry).CrashFileFrame scope (observe reached))
    (fun first last => first.trans last) effects

section CheckpointRetry

variable {rebooted reached : heap} {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
  {errors : List (FilePath × IO.Error)}

/-- A frame for failed opens that preserve the sampled checkpoint.
The selected live bytes, durable bytes, and root binding in the parent
directory survive. WAL name presence also records gaps in the catalog. -/
structure SampledCheckpointRetryFrame (directory : DiskDirectory) (scope : FilePath → Prop)
    (through : Nat) (observe : heap → CheckpointStorageObservation) (readBytes : heap → Nat → ByteArray)
    (before after : heap) : Prop where
  live : (⟨(observe before).files.names, fun inode => [readBytes before inode]⟩ : CheckpointSurvivingFiles).Frames
    scope ⟨(observe after).files.names, fun inode => [readBytes after inode]⟩
  walNames : ∀ start ≤ through, ((observe after).files.names (directory.file (.walSegment start))).isSome =
    ((observe before).files.names (directory.file (.walSegment start))).isSome
  durable : (observe before).files.Frames scope (observe after).files
  parent : (observe before).Frames (· = directory.path) (observe after)

theorem SampledCheckpointRetryFrame.refl {directory : DiskDirectory} {scope : FilePath → Prop}
    {through : Nat} {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}
    (atHeap : heap) : SampledCheckpointRetryFrame directory scope through observe readBytes atHeap atHeap :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl,
    fun _ _ => ⟨rfl, fun _ _ => rfl⟩, .refl _ _⟩

theorem SampledCheckpointRetryFrame.trans {directory : DiskDirectory} {scope : FilePath → Prop}
    {through : Nat} {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}
    {before middle after : heap}
    (left : SampledCheckpointRetryFrame directory scope through observe readBytes before middle)
    (right : SampledCheckpointRetryFrame directory scope through observe readBytes middle after) :
    SampledCheckpointRetryFrame directory scope through observe readBytes before after :=
  ⟨left.live.trans right.live, fun start bound => (right.walNames start bound).trans (left.walNames start bound),
    left.durable.trans right.durable, left.parent.trans right.parent⟩

/-- One fold over the actual failed occurrences carries both the live
reader input and the durable retry input to the next attempt. -/
theorem RawMarkedOpenInterpreter.FailedCalls.framesSampledCheckpoint
    (attempts : source.FailedCalls rebooted errors reached)
    {directory : DiskDirectory} {scope : FilePath → Prop} {through : Nat}
    {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}
    (each : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
      source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(input, cause)]) errors →
      source.openTable input before = .error cause after →
      SampledCheckpointRetryFrame directory scope through observe readBytes before after) :
    SampledCheckpointRetryFrame directory scope through observe readBytes rebooted reached :=
  attempts.framesAfter .empty _ SampledCheckpointRetryFrame.refl SampledCheckpointRetryFrame.trans
    (fun prior inside returned => each prior (by simpa only [List.nil_append] using inside) returned)

variable (source) in
/-- At an observed failed occurrence, local resolver, stat, and
append-error frames supply both the literal reader's live facts and
the ready continuation's durable facts. The public return identifies
the same heap even when a callback advances it. -/
theorem RawMarkedOpenInterpreter.framesSampledCheckpointBeforeFlock
    {input : FilePath} {before after atFailure : heap} {cause prefixCause : IO.Error}
    (returned : source.openTable input before = .error cause after)
    (failed : source.calls.beforeFlock input before = .error prefixCause atFailure)
    {directory : DiskDirectory} {scope : FilePath → Prop} {through : Nat}
    {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}
    (callbacks : source.calls.BeforeFlockErrorFrames input before prefixCause atFailure
      (SampledCheckpointRetryFrame directory scope through observe readBytes)) :
    SampledCheckpointRetryFrame directory scope through observe readBytes before after := by
  obtain ⟨actual, framed⟩ := source.framesBeforeFlock failed SampledCheckpointRetryFrame.trans callbacks
  exact (EStateM.Result.error.inj (actual.symm.trans returned)).2 ▸ framed

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

section ReadOnlyRetries

variable {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
  {first entry reached : heap} {earlier : List (FilePath × IO.Error)}
  {prior : source.FailedCalls first earlier entry}
  {input : FilePath} {cause : IO.Error} {firstOffset through : Nat}

private abbrev retryLiveFiles (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨(storage atHeap).files.names, fun inode => [visible atHeap inode]⟩

/-- A read-only attempt frames the selected live and durable files, the
live keeper, and the canonical WAL names used by a later retry. -/
structure RawOpenRetryTrace.ReadOnlyFilesFrame (state : NativeReadyState)
    (target : Target) (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (before after : heap) : Prop where
  live : (retryLiveFiles storage visible before).Frames
    (fun path => state.selectedRetryPath path ∨ path = state.session.directory.file (.walSegment target.first))
    (retryLiveFiles storage visible after)
  canonical : ∀ start, ((storage after).files.names (state.session.directory.file (.walSegment start))).isSome =
    ((storage before).files.names (state.session.directory.file (.walSegment start))).isSome
  durable : (storage before).Frames state.selectedRetryPath (storage after)

theorem RawOpenRetryTrace.ReadOnlyFilesFrame.refl (atHeap : heap) :
    RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible atHeap atHeap :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ => rfl, .refl _ _⟩

theorem RawOpenRetryTrace.ReadOnlyFilesFrame.trans {before middle after : heap}
    (left : RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible before middle)
    (right : RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible middle after) :
    RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible before after :=
  ⟨left.live.trans right.live,
    fun start => (right.canonical start).trans (left.canonical start), left.durable.trans right.durable⟩

/-- Attach the scoped effects of one actually returned read-only failure.
Other attempts may preserve the same target by repairing its live keeper. -/
theorem RawOpenRetryTrace.SelectedEffects.appendReadOnlyReturn
    (before : RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
      state.selectedRetryPath (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through) prior)
    (returned : source.openTable input entry = .error cause reached)
    (image : (view.files reached).image = (view.files entry).image)
    (framed : RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible entry reached) :
    RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
      state.selectedRetryPath (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through)
      (prior.next input returned) := by
  apply RawOpenRetryTrace.SelectedEffects.append (calls := .next .empty input returned) before (.inl image)
    (fun path selected => framed.live path (.inl selected))
  intro carried
  have keeperFrame := CheckpointSurvivingFiles.Frames.visiblePayload
    (names := fun atHeap => (storage atHeap).files.names) (bytes := visible) framed.live
    (path := state.session.directory.file (.walSegment target.first)) (.inr rfl)
  have keeper := carried.2.1
  unfold RawOpenRetryTrace.KeeperAt at keeper
  refine ⟨carried.1.frame (fun start _ _ => framed.canonical start), ?_,
    carried.2.2.1.frame framed.durable.visible
      (framed.durable.weaken (fun path root => .inr (.inl root))),
    carried.2.2.2.framePresence (congrArg (fun state : FileImage => state.later.visible) image)
      (fun start _ => framed.canonical start)⟩
  unfold RawOpenRetryTrace.KeeperAt
  rw [image, keeper, keeperFrame]

/-- Add the literal path/metadata rejection before any next retry. The
actual pre-flock outcome determines the public diagnostic and reached
heap. When an append is reached, its error must supply its own frame. -/
theorem RawOpenRetryTrace.SelectedEffects.beforeFlock
    (before : RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
      state.selectedRetryPath (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through) prior)
    (failed : source.calls.beforeFlock input entry = .error cause reached)
    (effects : source.calls.BeforeFlockErrorFrames input entry cause reached
      (fun before after => (view.files after).image = (view.files before).image ∧
        RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible before after)) :
    ∃ returned : source.openTable input entry = .error cause reached,
      RawOpenRetryTrace.SelectedEffects view source first target (retryLiveFiles storage visible)
        state.selectedRetryPath (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through)
        (prior.next input returned) ∧
      (view.files reached).image = (view.files entry).image ∧
      RawOpenRetryTrace.ReadOnlyFilesFrame state target storage visible entry reached := by
  obtain ⟨returned, image, framed⟩ := source.framesBeforeFlock failed
    (fun first next => ⟨next.1.trans first.1, first.2.trans next.2⟩) effects
  exact ⟨returned, before.appendReadOnlyReturn returned image framed, image, framed⟩

end ReadOnlyRetries

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
