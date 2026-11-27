import Alvoki.Storage.Disk.Proofs.Native.Open.NativeMutatingOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A rooted directory barrier settles the live WAL catalog, including
absent segments. Only its child-name effects enter this argument. -/
theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.afterDirectorySync
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through : Nat}
    {entry reached : CheckpointStorageObservation}
    (live : wal.NamespaceWindow directory first through entry.files.names)
    (visible : ∀ file, reached.files.names (directory.file file) = entry.files.names (directory.file file))
    (settled : ∀ names ∈ reached.crashNames, ∀ file,
      names (directory.file file) = reached.files.names (directory.file file)) :
    wal.SettledNamespaceWindow directory first through reached := by
  have reachedLive := live.frame (fun start _ _ => congrArg Option.isSome (visible (.walSegment start)))
  exact ⟨reachedLive, fun names survives => reachedLive.frame (fun start _ _ =>
    congrArg Option.isSome (settled names survives (.walSegment start)))⟩

/-- After the accepted unlink loop, the selected catalog extends to any
prospective marker. A later address is either in the actual scan's
remove list or was already absent. The frame applies to canonical
segment paths and preserves holes below and above the current cutoff. -/
theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.afterAcceptedUnlinks
    {heap : Type} {wal : WalSegmentImage} {directory : DiskDirectory} {first cutoff : Nat}
    {plan : Plan} {names : heap → FilePath → Option Nat} {before after : heap}
    (selected : wal.NamespaceWindow directory first cutoff (names before))
    (bounded : ∀ start ∈ wal.segments.map WalSegment.first, start ≤ cutoff)
    (later : ∀ start ∈ plan.newer, cutoff < start)
    (listed : ∀ start, cutoff < start →
      (names before (directory.file (.walSegment start))).isSome = true → start ∈ plan.newer)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (unlink : ∀ {ordinal entry reached result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) entry = .ok result reached →
      RunCollection.ownedUnlinkResult result = .ok () →
      names reached (directory.file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal → names reached (directory.file (.walSegment start)) =
        names entry (directory.file (.walSegment start)))
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) before = .ok () after) :
    ∀ through, wal.NamespaceWindow directory first through (names after) := by
  obtain ⟨removed, preserved⟩ := namesOfReturnedWalUnlinks directory plan remove write sync rename names
    (fun path => ∃ start, path = directory.file (.walSegment start))
    (fun start _ => ⟨start, rfl⟩) (fun member called accepted => by
      obtain ⟨absent, frame⟩ := unlink member called accepted
      refine ⟨absent, ?_⟩
      rintro _ ⟨start, rfl⟩ apart
      exact frame start fun equal => apart (congrArg (fun n => directory.file (.walSegment n)) equal)) returned
  intro _ start lower _
  let path := directory.file (.walSegment start)
  have unchanged (notListed : start ∉ plan.newer) : names after path = names before path :=
    preserved path ⟨start, rfl⟩ (fun ordinal member equal =>
      notListed ((directory.walSegment_path_injective equal).symm ▸ member))
  by_cases past : cutoff < start
  · have absent : names after path = none := by
      by_cases found : start ∈ plan.newer
      · exact removed start found
      · rw [unchanged found]
        cases named : names before path with
        | none => rfl
        | some inode => exact (found (listed start past (by simp [path, named]))).elim
    change (names after path).isSome = true ↔ start ∈ wal.segments.map WalSegment.first
    simp only [absent, Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun modeled => (Nat.not_le_of_gt past) (bounded start modeled)
  · have notListed : start ∉ plan.newer := fun member => past (later start member)
    change (names after path).isSome = true ↔ _
    rw [unchanged notListed]
    exact selected start lower (Nat.le_of_not_gt past)

private def rebootBindings (directory : DiskDirectory) (names : FilePath → Option Nat)
    (visible : Nat → ByteArray) : DirectoryPublication.Bindings :=
  ⟨(names (directory.file .manifest)).map visible, (names (directory.file .walBoundary)).map visible⟩

/-- Canonical starts beyond a decoded marker in one captured directory. -/
def DirectoryReadNamespace.laterWalStarts (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (through : Nat) : List Nat :=
  ((namespaceView.names root).filterMap parseWalSegmentName).eraseDups.mergeSort.filter fun start =>
    decide (through < start)

theorem DirectoryReadNamespace.mem_laterWalStarts
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

/-- The reboot image with the directory observer fixed. The next
literal open can use this observer for its directory stream. -/
abbrev RawWriteRebootImage {heap : Type} (state : NativeReadyState) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray) (rebooted : heap)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) : Prop :=
  let directory := state.session.directory
  let pair := rebootBindings directory (names rebooted) (visible rebooted)
  ∃ later : List Nat,
    names rebooted directory.path = some (namespaceView.modelObject root) ∧
    (∀ start, (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
      names rebooted (directory.file (.walSegment start))) ∧
    (∀ range, pair.walRange = some range → later = namespaceView.laterWalStarts root range.through) ∧
    (view.files rebooted).image = state.writer.files.crash pair
      ((names rebooted (directory.file (.walSegment state.writer.wal.active.first))).map (visible rebooted))
      later

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
  image : ∃ (namespaceView : DirectoryReadNamespace) (root : DeviceInode),
    RawWriteRebootImage state view names visible rebooted namespaceView root
  noDescriptors : (view.descriptors rebooted).slots = []
  released : (view.files rebooted).owners = (view.files failed).owners.set (state.session.directory.file .lock) none

variable {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
  {visible : heap → Nat → ByteArray} {entry failed rebooted : heap}

theorem RawWriteRebootImage.activePair {namespaceView : DirectoryReadNamespace} {root : DeviceInode}
    (sample : RawWriteRebootImage state view names visible rebooted namespaceView root) :
    (view.files rebooted).image.directory.active =
      ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
        (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩ := by
  obtain ⟨_, _, _, _, image⟩ := sample
  rw [image]
  rfl

/-- Both selected bindings come from the same reboot namespace. -/
theorem RawWriteRebootEntry.activePair
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted) :
    (view.files rebooted).image.directory.active =
      ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
        (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩ := by
  obtain ⟨_, _, sample⟩ := seen.image
  exact sample.activePair

/-- The later list contains exactly the canonical WAL names in the sampled
namespace whose starts exceed the marker of the selected retry. -/
theorem RawWriteRebootEntry.laterNames
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    {target : Target} (selected : target.pair = (view.files rebooted).image.directory.active) (start : Nat) :
    start ∈ (view.files rebooted).image.later.visible ↔
      target.range.through < start ∧
      ∃ inode, names rebooted (state.session.directory.file (.walSegment start)) = some inode := by
  obtain ⟨namespaceView, root, sample⟩ := seen.image
  let pair := rebootBindings state.session.directory (names rebooted) (visible rebooted)
  have exactPair : target.pair = pair := selected.trans sample.activePair
  obtain ⟨later, _, children, projected, image⟩ := sample
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

/-- Assemble the retry entry from the exact sampled image. The
immutable files and selected keeper can come from different local
proofs about the same survivor, including a later reboot after repair. -/
theorem RawWriteRebootEntry.selectsSampledRetry
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    {target : Target}
    (start : target.first = state.writer.wal.active.first)
    (sameManifest : target.pair.manifest = state.writer.target.pair.manifest)
    (kept : NativeReadyProtectedStorage state ⟨names rebooted, fun inode => [visible rebooted inode]⟩)
    (pair : target.pair = ⟨(names rebooted (state.session.directory.file .manifest)).map (visible rebooted),
      (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)⟩)
    (keeper : target.Accepts ((names rebooted (state.session.directory.file (.walSegment state.writer.wal.active.first))).map
      (visible rebooted))) :
    RawOpenRetryTrace.SelectedEntry view state target names visible rebooted ∧
    TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
    (view.descriptors rebooted).slots = [] := by
  obtain ⟨_, _, sample⟩ := seen.image
  have selected : (view.files rebooted).image.directory.active = target.pair := sample.activePair.trans pair.symm
  obtain ⟨_, _, _, _, image⟩ := sample
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
  have atFailure := old.toNativeReadyProtectedStorage.frame frame.visible
  obtain ⟨kept, manifest⟩ := atFailure.samplesRebootFiles (names rebooted) (visible rebooted)
    (fun path protectedPath => (old.chosenWriteBinding frame _ seen.chosen protectedPath).trans
      (frame.visible path protectedPath).1.symm) seen.sampled
  exact seen.selectsSampledRetry admitted.1 ((congrArg DirectoryPublication.Bindings.manifest pair).trans manifest)
    kept pair keeper

end Alvoki.Storage.DiskSession
