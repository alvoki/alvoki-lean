import Alvoki.Storage.Disk.NativeMutatingOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Presence of canonical WAL names in a given replay window. Older names
may already have been collected. Names beyond the window belong to later
repair. Inode identity and bytes have independent invariants. -/
def _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow (wal : WalSegmentImage)
    (directory : DiskDirectory) (first through : Nat) (names : FilePath → Option Nat) : Prop :=
  ∀ start, first ≤ start → start ≤ through →
    ((names (directory.file (.walSegment start))).isSome = true ↔ start ∈ wal.segments.map WalSegment.first)

theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.frame
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through : Nat}
    {before after : FilePath → Option Nat} (initial : wal.NamespaceWindow directory first through before)
    (presence : ∀ start, first ≤ start → start ≤ through →
      (after (directory.file (.walSegment start))).isSome = (before (directory.file (.walSegment start))).isSome) :
    wal.NamespaceWindow directory first through after :=
  fun start lower upper => presence start lower upper ▸ initial start lower upper

theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.restrict
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through lower upper : Nat}
    {names : FilePath → Option Nat} (initial : wal.NamespaceWindow directory first through names)
    (starts : first ≤ lower) (ends : upper ≤ through) : wal.NamespaceWindow directory lower upper names :=
  fun start after before => initial start (Nat.le_trans starts after) (Nat.le_trans before ends)

/-- In the requested interval, the live directory and every joint crash
map name exactly the modeled WAL segments, including the gaps. -/
abbrev _root_.Alvoki.Storage.WalSegmentImage.SettledNamespaceWindow
    (wal : WalSegmentImage) (directory : DiskDirectory) (first through : Nat)
    (storage : CheckpointStorageObservation) : Prop :=
  wal.NamespaceWindow directory first through storage.files.names ∧
    ∀ names ∈ storage.crashNames, wal.NamespaceWindow directory first through names

theorem WalNamePresenceFrame.preservesNamespaceWindow
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through : Nat}
    {entry reached : CheckpointStorageObservation}
    (frame : WalNamePresenceFrame directory first through entry reached)
    (initial : wal.SettledNamespaceWindow directory first through entry) :
    wal.SettledNamespaceWindow directory first through reached := by
  refine ⟨initial.1.frame frame.live, ?_⟩
  intro names survives
  obtain ⟨prior, fromLive | fromCrash, same⟩ := frame.survivors names survives
  · exact initial.1.frame (fromLive ▸ same)
  · exact (initial.2 prior fromCrash).frame same

private def rebootBindings (directory : DiskDirectory) (names : FilePath → Option Nat)
    (visible : Nat → ByteArray) : DirectoryPublication.Bindings :=
  ⟨(names (directory.file .manifest)).map visible, (names (directory.file .walBoundary)).map visible⟩

/-- Canonical starts beyond a decoded marker in one captured directory. -/
def DirectoryReadNamespace.laterWalStarts (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (through : Nat) : List Nat :=
  ((namespaceView.names root).filterMap parseWalSegmentName).eraseDups.mergeSort.filter fun start =>
    decide (through < start)

private theorem DirectoryReadNamespace.mem_laterWalStarts
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (through start : Nat) :
    start ∈ namespaceView.laterWalStarts root through ↔
      through < start ∧ ∃ object, namespaceView.child root (renderWalSegmentName start) = some object := by
  simp only [laterWalStarts, List.mem_filter, decide_eq_true_eq, List.mem_mergeSort, List.mem_eraseDups,
    List.mem_filterMap]
  constructor
  · rintro ⟨⟨name, listed, parsed⟩, beyond⟩
    exact ⟨beyond, (namespaceView.namesExact _ _).mp ((parseWalSegmentName_eq_some_iff.mp parsed) ▸ listed)⟩
  · rintro ⟨beyond, named⟩
    exact ⟨⟨_, (namespaceView.namesExact _ _).mpr named, parseWalSegmentName_render start⟩, beyond⟩

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
    let pair := rebootBindings directory (names rebooted) (visible rebooted)
    ∃ (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (later : List Nat),
      names rebooted directory.path = some (namespaceView.modelObject root) ∧
      (∀ start, (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names rebooted (directory.file (.walSegment start))) ∧
      (∀ range, pair.walRange = some range → later = namespaceView.laterWalStarts root range.through) ∧
      (view.files rebooted).image = state.writer.files.crash pair
        ((names rebooted (directory.file (.walSegment state.writer.wal.active.first))).map (visible rebooted))
        later
  noDescriptors : (view.descriptors rebooted).slots = []
  released : (view.files rebooted).owners = (view.files failed).owners.set (state.session.directory.file .lock) none

variable {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
  {visible : heap → Nat → ByteArray} {entry failed rebooted : heap}

/-- Both selected bindings come from the same reboot namespace. -/
theorem RawWriteRebootEntry.activePair
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted) :
    (view.files rebooted).image.directory.active =
      ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
        (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩ := by
  obtain ⟨_, _, _, _, _, _, image⟩ := seen.image
  rw [image]
  rfl

/-- The later list contains exactly the canonical WAL names in the sampled
namespace whose starts exceed the marker of the selected retry. -/
theorem RawWriteRebootEntry.laterNames
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    {target : Target} (selected : target.pair = (view.files rebooted).image.directory.active) (start : Nat) :
    start ∈ (view.files rebooted).image.later.visible ↔
      target.range.through < start ∧
      ∃ inode, names rebooted (state.session.directory.file (.walSegment start)) = some inode := by
  obtain ⟨namespaceView, root, later, _, children, projected, image⟩ := seen.image
  let pair := rebootBindings state.session.directory (names rebooted) (visible rebooted)
  have exactPair : target.pair = pair := selected.trans seen.activePair
  have range : pair.walRange = some target.range := by
    rw [← exactPair]
    exact target.decoded
  rw [image]
  change start ∈ later ↔ _
  rw [projected _ range, namespaceView.mem_laterWalStarts]
  constructor
  · rintro ⟨beyond, object, child⟩
    exact ⟨beyond, namespaceView.modelObject object, by simpa only [child, Option.map_some] using (children start).symm⟩
  · rintro ⟨beyond, inode, bound⟩
    obtain ⟨object, child, _⟩ := Option.map_eq_some_iff.mp ((children start).trans bound)
    exact ⟨beyond, object, child⟩

/-- Use the same joint survivor the reboot actually selected. Tracking
positive files alone does not supply this frame for absent WAL names. -/
theorem RawWriteRebootEntry.walNamespace
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    {first through : Nat}
    (frame : WalNamePresenceFrame state.session.directory first through (storage entry) (storage failed))
    (initial : state.writer.wal.SettledNamespaceWindow state.session.directory first through (storage entry)) :
    state.writer.wal.NamespaceWindow state.session.directory first through (names rebooted) :=
  (frame.preservesNamespaceWindow initial).2 _ seen.chosen

/-- The manifest, marker and keeper are sampled through the same map.
Recovery may also sample runs and seals without requiring byte choices
for the lock or directory. -/
theorem RawWriteRebootEntry.samplesWal
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted) :
    ∀ path inode,
      (path = state.session.directory.file .manifest ∨ path = state.session.directory.file .walBoundary ∨
        path = state.session.directory.file (.walSegment state.writer.wal.active.first)) →
      names rebooted path = some inode → visible rebooted inode ∈ (storage failed).files.bytes inode := by
  intro path inode selected bound
  exact seen.sampled path (selected.elim Or.inl (fun wal => .inr (.inl (wal.imp_right Or.inl)))) inode bound

/-- Interpret the exact joint survivor of a late publication error.
The rename and directory-sync proofs both supply the same selections.
Their live bindings are independent of the map sampled at reboot. -/
theorem WalPublicationPayloads.Selections.retryTargetAtReboot
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (valid : state.Valid)
    (prepared : prepareBatch state.writer.installed.table rows = some (batch, table))
    (fits : state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    (old : NativeReadyStorage state (storage entry))
    (frame : (storage entry).Frames state.writeFramePath (storage failed))
    {payloads : WalPublicationPayloads} {liveNew : Bool} {allows : Bool → Prop}
    (selected : payloads.Selections state.session.directory state.writer.wal.active.first (storage failed) liveNew allows)
    (sameKeeper : payloads.keeperBytes = state.writer.wal.active.bytes ++ WAL.encodeBatch batch)
    (oldMarker : payloads.oldMarkerBytes = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
    (newMarker : payloads.newMarkerBytes =
      WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64)
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted) :
    ∃ target, BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
      target.pair = ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
        (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩ ∧
      target.Accepts ((names rebooted (state.session.directory.file (.walSegment state.writer.wal.active.first))).map
        (visible rebooted)) :=
  selected.retryTargets valid prepared fits old frame sameKeeper oldMarker newMarker
    (names rebooted) seen.chosen (visible rebooted) seen.samplesWal

/-- The same sampled manifest and protected inodes initialize the live
retry state. The marker can select either earlier history or the entire
uncertain batch, and a retained keeper may be longer than that marker. -/
theorem RawWriteRebootEntry.selectsRetry
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    (old : NativeReadyStorage state (storage entry))
    (frame : (storage entry).Frames state.writeFramePath (storage failed))
    {batch : List WAL.Write} {target : Target}
    (admitted : BatchRetryTarget state.writer.history batch state.writer.wal.active.first target)
    (pair : target.pair = ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
      (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩)
    (keeper : target.Accepts ((names rebooted (state.session.directory.file (.walSegment state.writer.wal.active.first))).map
      (visible rebooted))) :
    RawOpenRetryTrace.SelectedEntry view state target names visible rebooted ∧
    TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
    (view.descriptors rebooted).slots = [] := by
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
  obtain ⟨_, _, _, _, _, _, image⟩ := seen.image
  have selected : (view.files rebooted).image.directory.active = target.pair := seen.activePair.trans pair.symm
  have settled : (view.files rebooted).image.directory.crashImages = [target.pair] := by
    rw [image]
    exact congrArg (fun pair => [pair]) pair.symm
  have keeperValid : (view.files rebooted).image.keeper.Valid target.Accepts := by
    rw [image]
    refine ⟨by simp [FileImage.crash, Publication.Image.settled], keeper, ?_⟩
    intro bytes member
    exact (List.mem_singleton.mp member).symm ▸ keeper
  have laterValid : (view.files rebooted).image.later.Beyond target.range.through := by
    have fixed : (view.files rebooted).image.later.crashImages = [(view.files rebooted).image.later.visible] := by
      rw [image]
      rfl
    intro later member first contains
    have same : later = (view.files rebooted).image.later.visible := by
      simpa [fixed] using member
    exact ((seen.laterNames selected.symm first).mp (same ▸ contains)).1
  refine ⟨⟨⟨selected, settled, keeperValid, laterValid⟩, ?_, sameManifest, kept, ?_, ?_⟩, ?_, seen.noDescriptors⟩
  · rw [image]
    rfl
  · unfold RawOpenRetryTrace.KeeperAt
    rw [image, start]
    rfl
  · exact (congrArg DirectoryPublication.Bindings.walBoundary pair).symm
  · rw [seen.released]
    intro path
    simp [LockOwners.set]

end Alvoki.Storage.DiskSession
