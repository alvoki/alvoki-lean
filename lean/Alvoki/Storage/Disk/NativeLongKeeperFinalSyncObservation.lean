import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperStageSyncError
import Alvoki.Storage.Disk.NativeLongKeeperRenameError
import Alvoki.Storage.Disk.NativeLongKeeperStorage
import Alvoki.Storage.Disk.NativeLongKeeperPending
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeMarkedFirstUnlinkError
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail
import Alvoki.Storage.Disk.NativeLateWriteRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting CheckpointPublication

private theorem NativeReadyState.selectedRetryPath_rootOrChild {state : NativeReadyState} {path : FilePath}
    (retained : state.selectedRetryPath path) :
    path = state.session.directory.path ∨ ∃ file, path = state.session.directory.file file := by
  rcases retained with marker | held
  · exact .inr ⟨.walBoundary, marker⟩
  rcases held with root | lock | manifest | sealedPath | runPath
  · exact .inl root
  · exact .inr ⟨.lock, lock⟩
  · exact .inr ⟨.manifest, manifest⟩
  · obtain ⟨segment, _, same⟩ := sealedPath
    exact .inr ⟨.walSegment segment.first, same⟩
  · obtain ⟨_, metadata, index, _, _, _, same⟩ := runPath
    exact .inr ⟨.run metadata.header.generation index, same⟩

private theorem WalRootSyncEffect.framesScopedFiles {directory : DiskDirectory} {scope : FilePath → Prop}
    {effective : Bool} {entry reached : CheckpointStorageObservation}
    (effect : WalRootSyncEffect directory effective entry reached)
    (parent : entry.Frames (· = directory.path) reached)
    (managed : ∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file) :
    entry.files.Frames scope reached.files := by
  intro path retained
  rcases managed path retained with atRoot | ⟨file, rfl⟩
  · exact parent.visible path atRoot
  · exact ⟨effect.visible file, fun inode bound =>
      effect.bytes reached.files.names (.inl rfl) file inode ((effect.visible file).trans bound)⟩

/-- A directory fsync frames the protected child bytes for either
reported effect. Parent binding continuity is a separate effect law. -/
private theorem WalRootSyncEffect.framesSelectedRetry {state : NativeReadyState} {effective : Bool}
    {entry reached : CheckpointStorageObservation} {before after : Nat → ByteArray}
    (effect : WalRootSyncEffect state.session.directory effective entry reached)
    (parent : entry.Frames (· = state.session.directory.path) reached)
    (live : ∀ path, state.selectedRetryPath path → ∀ inode,
      entry.files.names path = some inode → after inode = before inode) :
    state.SelectedRetryFrame entry reached before after := by
  have durable := effect.framesScopedFiles parent (scope := state.selectedRetryPath)
    (fun _ => NativeReadyState.selectedRetryPath_rootOrChild)
  exact ⟨fun path held => ⟨(durable path held).1, fun inode named =>
    congrArg List.singleton (live path held inode named)⟩, durable, parent⟩

/-- The replacement is exact. The old inode's payload choices remain
relevant while a joint survivor can still name it. -/
private theorem WalKeeperRenameEffect.acceptsKeeperSurvivors
    {directory : DiskDirectory} {target : Target} {old replacement : Nat} {effective : Bool}
    {before reached : CheckpointStorageObservation} {beforeBytes reachedBytes : Nat → ByteArray}
    (effect : WalKeeperRenameEffect directory target.first replacement effective before reached beforeBytes reachedBytes)
    (settled : ∀ names ∈ before.crashNames, names (directory.file (.walSegment target.first)) = some old)
    (staged : before.files.bytes replacement = [target.trimmed])
    (oldPayload : ∀ bytes ∈ before.files.bytes old, target.Accepts (some bytes)) :
    RawOpenRetryTrace.KeeperCrashChoices directory target reached := by
  intro names survives
  obtain ⟨moved, _, named, bytes, _⟩ := effect.keeperSurvivors settled staged names survives
  refine ⟨_, named, fun payload sampled => ?_⟩
  rw [bytes] at sampled
  cases moved with
  | false => exact oldPayload payload sampled
  | true =>
    have exactPayload : payload = target.trimmed := List.mem_singleton.mp sampled
    exact exactPayload ▸ target.acceptsTrimmed

/-- The final sync selects the live trimmed inode when it settles. On
a before-effect error the reboot uses one of the prior joint maps. -/
private theorem WalRootSyncEffect.acceptsKeeperSurvivors
    {directory : DiskDirectory} {target : Target} {entry reached : CheckpointStorageObservation}
    {effective : Bool} {replacement : Nat}
    (effect : WalRootSyncEffect directory effective entry reached)
    (prior : RawOpenRetryTrace.KeeperCrashChoices directory target entry)
    (live : entry.files.names (directory.file (.walSegment target.first)) = some replacement)
    (durable : entry.files.bytes replacement = [target.trimmed]) :
    RawOpenRetryTrace.KeeperCrashChoices directory target reached := by
  intro names survives
  let file := DiskFile.walSegment target.first
  have carries (inode : Nat) (named : names (directory.file file) = some inode) :
      reached.files.bytes inode = entry.files.bytes inode :=
    effect.bytes names (.inr survives) file inode named
  cases applied : effective with
  | false =>
    obtain ⟨earlier, possible, same⟩ := effect.unchanged applied names survives
    obtain ⟨inode, earlierNamed, accepted⟩ := prior earlier possible
    have named := (same file).trans earlierNamed
    exact ⟨inode, named, fun payload member => accepted payload (carries inode named ▸ member)⟩
  | true =>
    have named := (effect.settled applied names survives file).trans ((effect.visible file).trans live)
    refine ⟨replacement, named, fun payload member => ?_⟩
    rw [carries replacement named, durable] at member
    exact (List.mem_singleton.mp member) ▸ target.acceptsTrimmed

/-- A settled selected child stays settled on any survivors of an
ineffective barrier. An effective barrier uses its live binding. -/
private theorem WalRootSyncEffect.keepsSelectedChildren
    {state : NativeReadyState} {entry reached : CheckpointStorageObservation} {effective : Bool}
    (effect : WalRootSyncEffect state.session.directory effective entry reached)
    (prior : ∀ names ∈ entry.crashNames, ∀ path, state.selectedRetryPath path →
      path ≠ state.session.directory.path → names path = entry.files.names path) :
    ∀ names ∈ reached.crashNames, ∀ path, state.selectedRetryPath path →
      path ≠ state.session.directory.path → names path = reached.files.names path := by
  intro names survives path selected notRoot
  rcases NativeReadyState.selectedRetryPath_rootOrChild selected with atRoot | ⟨file, rfl⟩
  · exact False.elim (notRoot atRoot)
  cases applied : effective with
  | true => exact effect.settled applied names survives file
  | false =>
    obtain ⟨earlier, possible, same⟩ := effect.unchanged applied names survives
    exact (same file).trans ((prior earlier possible _ selected notRoot).trans (effect.visible file).symm)

/-- Keeper replacement has no effect on the other selected children.
Their prior settlement therefore carries through the actual rename. -/
private theorem WalKeeperRenameEffect.keepsSelectedChildren
    {state : NativeReadyState} {first replacement : Nat} {effective : Bool}
    {entry reached : CheckpointStorageObservation} {entryBytes reachedBytes : Nat → ByteArray}
    (effect : WalKeeperRenameEffect state.session.directory first replacement effective entry reached entryBytes reachedBytes)
    (ready : state.Valid) (atKeeper : first = state.writer.wal.active.first)
    (prior : ∀ names ∈ entry.crashNames, ∀ path, state.selectedRetryPath path →
      path ≠ state.session.directory.path → names path = entry.files.names path) :
    ∀ names ∈ reached.crashNames, ∀ path, state.selectedRetryPath path →
      path ≠ state.session.directory.path → names path = reached.files.names path := by
  let scope : FilePath → Prop := fun path => state.selectedRetryPath path ∧ path ≠ state.session.directory.path
  have frame := effect.framesOffTarget (scope := scope)
    (fun _ retained => NativeReadyState.selectedRetryPath_rootOrChild retained.1) (by
      intro path retained
      exact ⟨atKeeper.symm ▸ state.protectedPathNeWalFromActive ready retained.1 (Nat.le_refl _),
        state.stagedWalOutsideRetryFootprint path retained.1⟩)
  intro names possible path protectedPath notRoot
  exact frame.settledFrom (fun priorMap earlier name retained => prior priorMap earlier name retained.1 retained.2)
    names possible path ⟨protectedPath, notRoot⟩

/-- Read the admitted keeper from the same namespace used to read the
settled marker. Its payload belongs to the selected inode at the crash. -/
theorem RawWriteRebootEntry.selectsRepairedKeeper
    {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
    {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
    {visible : heap → Nat → ByteArray} {failed rebooted : heap} {target : Target}
    (seen : RawWriteRebootEntry state view storage names visible failed rebooted)
    (first : target.first = state.writer.wal.active.first)
    (keeper : RawOpenRetryTrace.KeeperCrashChoices state.session.directory target (storage failed))
    (marker : (view.files rebooted).image.directory.active.walBoundary = target.pair.walBoundary) :
    ∃ inode count, names rebooted (state.session.directory.file (.walSegment target.first)) = some inode ∧
      ((names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted)).map
        WAL.Boundary.decode = some (.ok count) ∧
      WAL.Boundary.selectRetained target.first count (visible rebooted inode) = .ok target.trimmed := by
  obtain ⟨inode, named, accepted⟩ := keeper _ seen.chosen
  have sampled := seen.samplesWal (state.session.directory.file (.walSegment target.first)) inode
    (.inr (.inr (congrArg (fun start => state.session.directory.file (.walSegment start)) first))) named
  obtain ⟨_, _, payload, count, marked, decoded, _⟩ := DirectoryPublication.Bindings.walRange_accounting target.decoded
  have markerBytes : (names rebooted (state.session.directory.file .walBoundary)).map (visible rebooted) = some payload := by
    have physical := congrArg DirectoryPublication.Bindings.walBoundary seen.activePair
    exact physical.symm.trans (marker.trans marked)
  exact ⟨inode, count, named, by rw [markerBytes, Option.map_some, decoded],
    target.selectKeeper marked decoded (accepted _ sampled)⟩


section PruneDirectorySync

variable {heap : Type} {directory : DiskDirectory} {view : OpenCloseHeapView heap FileImage}
  {scope : FilePath → Prop} {through : Nat} {storage : heap → CheckpointStorageObservation}
  {visible : heap → Nat → ByteArray}

private theorem NativeReadyState.pruneRecoveryScope_excludesUnlinks {state : NativeReadyState} {target : Target}
    {plan : Plan} (sameDirectory : state.session.directory = directory)
    (valid : state.Valid) (first : target.first = state.writer.wal.active.first)
    (checked : plan.valid = true) (cutoff : target.range.through ≤ plan.through)
    (ordinal : Nat) (listed : ordinal ∈ plan.newer) :
    ¬ state.pruneRecoveryScope target.range.through (directory.file (.walSegment ordinal)) := by
  have later := Nat.lt_of_le_of_lt cutoff (((Plan.valid_iff plan).mp checked).2.2 ordinal listed)
  rw [← sameDirectory]
  rintro (⟨selected, _⟩ | ⟨start, within, same⟩)
  · have afterKeeper := first ▸ Nat.le_trans target.firstCovered (Nat.le_of_lt later)
    exact state.protectedPathNeWalFromActive valid selected afterKeeper rfl
  · have sameStart := state.session.directory.walSegment_path_injective same
    exact (Nat.not_le_of_gt later) (sameStart.symm ▸ within)

/-- A singleton directory group can fail while reading the cache cell, on
an empty cell, or at fsync on the handle the cell returned. The last case
exposes the original diagnostic before the group formats it for callers. -/
theorem AlignedKeeperCacheCallbacks.directoryGroupError_iff
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (before reached : heap) (reported : IO.Error) :
    calls.syncPaths directory.path cached active pending #[directory.path] before = .error reported reached ↔
      match calls.getDirectory cached before with
      | .error diagnostic after => after = reached ∧ reported = IO.userError s!"sync failed for '{directory.path}': {diagnostic}"
      | .ok none after => after = reached ∧
          reported = IO.userError s!"sync failed for '{directory.path}': {IO.userError "database is closed"}"
      | .ok (some handle) issued => ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
          reported = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" := by
  rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single]
  cases read : calls.getDirectory cached before with
  | error e after =>
    simp [syncWithHandles, Bind.bind, EStateM.bind, read, eq_comm, and_comm]
    exact fun _ => Iff.rfl
  | ok cell issued =>
    cases cell with
    | none =>
      simp [syncWithHandles, Bind.bind, EStateM.bind, read, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, eq_comm, and_comm]
      exact fun _ => Iff.rfl
    | some handle =>
      cases raw : calls.sync handle issued with
      | ok value after => simp [syncWithHandles, Bind.bind, EStateM.bind, read, raw, Pure.pure, EStateM.pure]
      | error diagnostic after =>
        simp [syncWithHandles, Bind.bind, EStateM.bind, read, raw, Pure.pure, EStateM.pure]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨_, ⟨rfl, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨rfl, rfl⟩, rfl⟩
          exact ⟨rfl, rfl⟩

private theorem AlignedKeeperCacheCallbacks.rawDirectoryErrorAfterRead
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error}
    (loaded : calls.getDirectory cached before = .ok (some handle) issued)
    (returned : calls.syncPaths directory.path cached active pending #[directory.path] before = .error cause reached) :
    ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
      cause = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" := by
  simpa only [loaded] using (calls.directoryGroupError_iff cached active pending before reached cause).mp returned

/-- A reported root fsync error frames the selected files even if the
directory's child bindings have settled. The literal cached handle
identifies that root independently of the report's effect. -/
theorem AlignedKeeperCacheCallbacks.framesPruneDirectoryError
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error} {effective : Bool}
    (loaded : calls.getDirectory cached before = .ok (some handle) issued)
    (returned : calls.syncPaths directory.path cached active pending #[directory.path] before = .error cause reached)
    (target : RawFsyncTarget view before issued handle)
    (bound : (storage issued).files.names directory.path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (loadFrame : SampledCheckpointRetryFrame directory scope through storage visible before issued)
    (managed : ∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file)
    (observation : ∀ diagnostic, calls.sync handle issued = .error diagnostic reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      WalRootSyncEffect directory effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = directory.path) (storage reached) ∧
      ∀ path, scope path → ∀ inode, (storage issued).files.names path = some inode →
        visible reached inode = visible issued inode) :
    ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
      cause = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" ∧
      SampledCheckpointRetryFrame directory scope through storage visible before reached ∧
      WalRootSyncEffect directory effective (storage issued) (storage reached) := by
  obtain ⟨diagnostic, failed, reported⟩ := calls.rawDirectoryErrorAfterRead cached active pending loaded returned
  obtain ⟨children, parent, live⟩ := observation diagnostic failed target.live bound
  have durable := children.framesScopedFiles parent managed
  have atSync : SampledCheckpointRetryFrame directory scope through storage visible issued reached :=
    ⟨fun path selected => ⟨(durable path selected).1, fun inode named => congrArg (fun bytes => [bytes])
      (live path selected inode named)⟩,
      fun start _ => congrArg Option.isSome (children.visible (.walSegment start)), durable, parent⟩
  exact ⟨diagnostic, failed, reported, loadFrame.trans atSync, children⟩

end PruneDirectorySync

section CatalogAtError

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {wal : WalSegmentImage} {target : Target} {plan : Plan} {names : heap → FilePath → Option Nat}

/-- Once the actual unlink pass has returned, cleanup need only carry
canonical name presence. A later rename may exchange the keeper inode
without changing its membership in the selected namespace. -/
theorem RawOpenRetryTrace.keepsCatalogAfterPruning
    {afterUnlinks reached : heap} {first through : Nat}
    (pruned : ∀ upper, wal.NamespaceWindow directory first upper (names afterUnlinks))
    (firstCovered : first ≤ target.range.through)
    (bounded : ∀ start ∈ wal.segments.map WalSegment.first, start ≤ target.range.through)
    (afterPrune : ∀ start, first ≤ start → (names reached (directory.file (.walSegment start))).isSome =
      (names afterUnlinks (directory.file (.walSegment start))).isSome)
    (laterEmpty : (view.files reached).image.later.visible = []) :
    wal.NamespaceWindow directory first through (names reached) ∧
      RawOpenRetryTrace.LaterWalAt view directory target names reached := by
  have complete upper := (pruned upper).frame (fun start lower _ => afterPrune start lower)
  refine ⟨complete through, ?_⟩
  intro start
  rw [laterEmpty]
  constructor
  · simp
  · rintro ⟨above, inode, named⟩
    have present : (names reached (directory.file (.walSegment start))).isSome = true := by rw [named]; rfl
    have lower := Nat.le_trans firstCovered (Nat.le_of_lt above)
    exact (Nat.not_le_of_gt above (bounded start ((complete start start lower (Nat.le_refl start)).mp present))).elim

end CatalogAtError

section ReplacementPrefix

/-- Follow the logical image of the actual rooted barriers, accepted
suffix removals, and staged fsync up to the keeper rename. Both later
error sites see this same synced stage and the same pruned catalog. -/
theorem longKeeperSyncPrefix {heap : Type} (files : heap → FileImage) (directory : DiskDirectory)
    (target : Target) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {entry authorized pruned recorded synced : heap}
    (authorize : sync #[directory.path] entry = .ok () authorized)
    (prune : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () pruned)
    (written : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded)
    (persisted : sync #[directory.file .stagedWal] recorded = .ok () synced)
    (covers : ∀ ordinal ∈ (files entry).later.visible, ordinal ∈ plan.newer)
    (later : ∀ ordinal ∈ plan.newer, target.range.through < ordinal)
    (authorizationImage : sync #[directory.path] entry = .ok () authorized →
      files authorized = (files entry).syncDirectory)
    (pruneImage : ∀ {unlinked}, ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () unlinked →
      sync #[directory.path] unlinked = .ok () pruned → files pruned = (files unlinked).syncDirectory)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () → files after = (files before).unlinkLater ordinal)
    (writeStage : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded →
      files recorded = (files pruned).withScratch (some (target.trimmed, false)))
    (syncStage : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded →
      sync #[directory.file .stagedWal] recorded = .ok () synced →
      files synced = (files recorded).withScratch (some (target.trimmed, true))) :
    EffectTrace target (files entry) (files pruned) ∧
      files pruned = { (files entry).syncDirectory.syncDirectory with later := LaterNames.settled [] } ∧
      files synced = (files pruned).withScratch (some (target.trimmed, true)) := by
  have authorizedImage := authorizationImage authorize
  have allLater : ∀ ordinal ∈ (files authorized).later.visible, ordinal ∈ plan.newer := by
    rw [authorizedImage]
    exact covers
  obtain ⟨_, unlinks, syncedPrune, unlinkedImage⟩ := foldReturnedPrune directory plan remove write sync rename
    (fun projected reached => files reached = projected) FileImage.unlinkLater rfl
    (fun {ordinal _ _ _ _} member called accepted earlier =>
      (unlink member called accepted).trans (congrArg (fun image => image.unlinkLater ordinal) earlier)) prune
  have prunedImage := pruneImage unlinks syncedPrune
  have initial : EffectTrace target (files entry) (files authorized) := authorizedImage.symm ▸ .authorized
  have prunedTrace : EffectTrace target (files entry) (files pruned) := by
    rw [prunedImage, unlinkedImage]
    exact .syncPruned (initial.unlinks _ later)
  have stageImage : files synced = (files pruned).withScratch (some (target.trimmed, true)) := by
    rw [syncStage written persisted, writeStage written]
    rfl
  refine ⟨prunedTrace, ?_, stageImage⟩
  rw [prunedImage, unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ allLater, authorizedImage]

end ReplacementPrefix

/-- During repair, the directory slot belongs to the census of the
actual open attempt. -/
abbrev NativeReadyState.repairDirectoryScope (state : NativeReadyState) (current : DescriptorInventory)
    (cached : DescriptorSlot) : NativeReadyState :=
  { state with census := current, directorySlot := cached }

/-- A retry frame observes the directory and its protected files. Preparing
it under the reopened descriptor census leaves those path scopes unchanged. -/
private theorem NativeReadyState.SelectedRetryFrame.fromRepairDirectoryScope
    {state : NativeReadyState} {census : DescriptorInventory} {cached : DescriptorSlot}
    {before after : CheckpointStorageObservation} {earlier later : Nat → ByteArray}
    (frame : (state.repairDirectoryScope census cached).SelectedRetryFrame before after earlier later) :
    state.SelectedRetryFrame before after earlier later := ⟨frame.live, frame.durable, frame.parent⟩

section LivePrune

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {state : NativeReadyState} {target : Target}
  {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}

local notation "dir" => state.session.directory
local notation "liveNames" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (observe h))
local notation "liveImage" => fun h => LockedFileState.image (OpenCloseHeapView.files view h)
local notation "keeperPath" => DiskDirectory.file dir (DiskFile.walSegment (Target.first target))
local notation "keeperPayload" => fun h => Option.map (visible h) (liveNames h keeperPath)

variable (view state target observe visible) in
/-- A reached unlink can remove its victim even when it reports a
failure. Other bindings and the live keeper are framed locally. -/
abbrev RawOpenRetryTrace.WalUnlinkEffect (keeps : heap → heap → Prop)
    (ordinal : Nat) (before after : heap) (removed : Bool) : Prop :=
  liveImage after = (if removed then (liveImage before).unlinkLater ordinal else liveImage before) ∧
  liveNames after ((dir).file (.walSegment ordinal)) =
    (if removed then none else liveNames before ((dir).file (.walSegment ordinal))) ∧
  (∀ start, start ≠ ordinal → liveNames after ((dir).file (.walSegment start)) =
    liveNames before ((dir).file (.walSegment start))) ∧
  keeperPayload after = keeperPayload before ∧ keeps before after

variable (view state target observe visible) in
private abbrev LivePruneAt (entry beforeRepair : heap) (firstOffset through : Nat)
    (keeps : heap → heap → Prop) (reached : heap) : Prop :=
  EffectTrace target (liveImage entry) (liveImage reached) ∧
  state.writer.wal.NamespaceWindow dir firstOffset through (liveNames reached) ∧
  RawOpenRetryTrace.KeeperAt view dir target liveNames visible reached ∧
  RawOpenRetryTrace.LaterWalAt view dir target liveNames reached ∧ keeps beforeRepair reached

private theorem LivePruneAt.authorized
    {entry beforeRepair authorized : heap} {firstOffset through : Nat} {keeps : heap → heap → Prop}
    (initial : RawOpenRetryTrace.RecoveryObservations view state target observe visible firstOffset through entry)
    (image : liveImage authorized = (liveImage entry).syncDirectory)
    (names : ∀ start, (liveNames authorized ((dir).file (.walSegment start))).isSome =
      (liveNames entry ((dir).file (.walSegment start))).isSome)
    (keeper : keeperPayload authorized = keeperPayload entry)
    (frame : keeps beforeRepair authorized) :
    LivePruneAt view state target observe visible entry beforeRepair firstOffset through keeps authorized := by
  refine ⟨image.symm ▸ .authorized, initial.1.frame (fun start _ _ => names start), ?_, ?_, frame⟩
  · change (liveImage authorized).keeper.active = keeperPayload authorized
    rw [image, keeper]
    exact initial.2.1
  · exact initial.2.2.2.framePresence (congrArg (fun image => image.later.visible) image)
      (fun start _ => names start)

private theorem LivePruneAt.afterUnlink
    {entry beforeRepair before after : heap} {firstOffset through ordinal : Nat} {removed : Bool}
    {keeps : heap → heap → Prop} (earlier : LivePruneAt view state target observe visible entry beforeRepair
      firstOffset through keeps before)
    (within : through ≤ target.range.through) (later : target.range.through < ordinal)
    (compose : ∀ {first middle last}, keeps first middle → keeps middle last → keeps first last)
    (observed : RawOpenRetryTrace.WalUnlinkEffect view state target observe visible keeps ordinal before after removed) :
    LivePruneAt view state target observe visible entry beforeRepair firstOffset through keeps after := by
  obtain ⟨image, victim, names, keeper, frame⟩ := observed
  have boundedNames (start : Nat) (bounded : start ≤ through) :=
    congrArg Option.isSome (names start (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans bounded within) later)))
  have actualKeeper : RawOpenRetryTrace.KeeperAt view dir target liveNames visible after := by
    change (liveImage after).keeper.active = keeperPayload after
    rw [image, keeper]
    cases removed <;> simp only [Bool.false_eq_true, ite_false, ite_true, FileImage.unlinkLater]
    all_goals exact earlier.2.2.1
  refine ⟨?_, earlier.2.1.frame (fun start _ bounded => boundedNames start bounded), actualKeeper, ?_,
    compose earlier.2.2.2.2 frame⟩
  · rw [image]
    cases removed <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact earlier.1
    · exact earlier.1.unlink later
  · cases removed
    · have sameImage : liveImage after = liveImage before := by simpa only [Bool.false_eq_true, ite_false] using image
      have unchanged (start : Nat) : liveNames after ((dir).file (.walSegment start)) =
          liveNames before ((dir).file (.walSegment start)) := by
        by_cases same : start = ordinal
        · subst start
          simpa only [Bool.false_eq_true, ite_false] using victim
        · exact names start same
      exact earlier.2.2.2.1.frame (congrArg (fun image => image.later.visible) sameImage)
        (fun start _ => unchanged start)
    · have unlinked : liveImage after = (liveImage before).unlinkLater ordinal := by
        simpa only [ite_true] using image
      exact earlier.2.2.2.1.unlinked (congrArg (fun image => image.later.visible) unlinked)
        (by simpa only [ite_true] using victim) (fun start _ apart => names start apart)

/-- A local step with its own effect trace keeps the retry invariant when
the canonical keeper payload and the visible WAL membership are framed. -/
private theorem LivePruneAt.framed
    {entry beforeRepair before after : heap} {firstOffset through : Nat} {keeps : heap → heap → Prop}
    (earlier : LivePruneAt view state target observe visible entry beforeRepair firstOffset through keeps before)
    (trace : EffectTrace target (liveImage entry) (liveImage after))
    (active : (liveImage after).keeper.active = (liveImage before).keeper.active)
    (later : (liveImage after).later.visible = (liveImage before).later.visible)
    (names : ∀ start, (liveNames after ((dir).file (.walSegment start))).isSome =
      (liveNames before ((dir).file (.walSegment start))).isSome)
    (keeper : keeperPayload after = keeperPayload before)
    (frame : keeps before after)
    (compose : ∀ {first middle last}, keeps first middle → keeps middle last → keeps first last) :
    LivePruneAt view state target observe visible entry beforeRepair firstOffset through keeps after :=
  ⟨trace, earlier.2.1.frame (fun start _ _ => names start), active.trans (earlier.2.2.1.trans keeper.symm),
    earlier.2.2.2.1.framePresence later (fun start _ => names start), compose earlier.2.2.2.2 frame⟩

/-- A directory barrier keeps the live suffix and changes the permitted
crash choices according to the observed effect. -/
private theorem LivePruneAt.afterBarrier
    {entry beforeRepair unlinked issued reached : heap} {firstOffset through : Nat}
    {keeps : heap → heap → Prop} (earlier : LivePruneAt view state target observe visible entry beforeRepair
      firstOffset through keeps unlinked)
    (loadImage : liveImage issued = liveImage unlinked)
    (loadNames : ∀ start, liveNames issued ((dir).file (.walSegment start)) =
      liveNames unlinked ((dir).file (.walSegment start)))
    (loadKeeper : keeperPayload issued = keeperPayload unlinked)
    {effective : Bool} (root : WalRootSyncEffect dir effective (observe issued) (observe reached))
    (syncImage : liveImage reached = if effective then (liveImage issued).syncDirectory else liveImage issued)
    (syncKeeper : ∀ inode, liveNames issued keeperPath = some inode → visible reached inode = visible issued inode)
    (frame : keeps unlinked reached)
    (compose : ∀ {first middle last}, keeps first middle → keeps middle last → keeps first last) :
    LivePruneAt view state target observe visible entry beforeRepair firstOffset through keeps reached := by
  have loadTrace : EffectTrace target (liveImage entry) (liveImage issued) := loadImage.symm ▸ earlier.1
  have atReached : EffectTrace target (liveImage entry) (liveImage reached) := by
    rw [syncImage]
    cases effective <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact loadTrace
    · exact loadTrace.syncPruned
  have keepsVisible (start : Nat) :
      liveNames reached ((dir).file (.walSegment start)) = liveNames unlinked ((dir).file (.walSegment start)) :=
    (root.visible (.walSegment start)).trans (loadNames start)
  have sameLater : (liveImage reached).later.visible = (liveImage unlinked).later.visible := by
    rw [syncImage]
    cases effective <;> simp only [Bool.false_eq_true, ite_false, ite_true, FileImage.syncDirectory,
      LaterNames.syncDirectory, LaterNames.settled, loadImage]
  have sameKeeper : (liveImage reached).keeper.active = (liveImage unlinked).keeper.active := by
    rw [syncImage]
    cases effective <;> simp only [Bool.false_eq_true, ite_false, ite_true, FileImage.syncDirectory, loadImage]
  have keeperAtSync : keeperPayload reached = keeperPayload issued :=
    (congrArg (Option.map (visible reached)) (root.visible (.walSegment target.first))).trans
      (Option.map_congr syncKeeper)
  exact earlier.framed atReached sameKeeper sameLater (fun start => congrArg Option.isSome (keepsVisible start))
    (keeperAtSync.trans loadKeeper) frame compose

end LivePrune

section FailedMarkedRepair

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {source : RawMarkedOpenInterpreter heap stream} {entry : heap} {input : FilePath}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout (view.files entry).image history}
  {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
  (extents : MarkedWalExtentReports prepared listing)
  {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
  (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
  (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
  (valid : Prepared (view.files entry).image layout.target layout.plan)
  (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
    layout.range.watermark < first)
  (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
    (view.files entry).image.directory.active.manifest)
  (ordered : WAL.OrdinalsFrom 1 history)

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "remember" => fun path handle =>
  AlignedKeeperCacheCallbacks.modifyPending callbacks seed.pendingRef (pushPending path handle)
local notation "stageWrite" => source.stage.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks directory.path
  seed.directoryRef seed.activeRef seed.pendingRef

variable (sameStat : source.fileCalls.stat = source.calls.lookup)
  (flat : optionalMetadataWith (source.fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
  {markedMeta : IO.FS.Metadata}
  (marked : optionalMetadataWith (source.fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
    .ok (some markedMeta) seed.afterPending)
  (keeperRead : source.fileCalls.readKeeperWithRelease
    (fun path handle => (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef
      (pushPending path handle))
    (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
    reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)

include extents seals selected valid following accepted ordered sameStat flat marked keeperRead

/-- Carry a scoped frame from the checked reader through the actual
failed repair, cache disposal, unlock and lock release. The unlock can
replace the worker's error in the public diagnostic. The reading
prefix is also available to the repair and restart proofs. -/
theorem MarkedWalExtentReports.finalizesFailedRepairWithFrame
    {frame : heap → heap → Prop} (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (readerFrames : source.fileCalls.ScopeFrames frame)
    (listingFrames : source.directoryCalls.ScopeFrames directory frame)
    (keeperFrame : frame beforeKeeper afterKeeper)
    {cause : IO.Error}
    (repair : finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      source.remove stageWrite groupSync source.rename afterKeeper = .error cause reached)
    (repairFrame : frame afterKeeper reached)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized frame) :
    source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached ∧
      frame entry finalized.reached ∧ (view.files finalized.reached).image = (view.files reached).image ∧
      frame entry afterKeeper := by
  let worker := source.worker seed.directoryRef seed.activeRef seed.pendingRef
  have rejected := extents.workerReturnsFailedRepair source (raw := raw) seals selected valid following accepted ordered
    sameStat flat marked keeperRead repair
  have disposed := dispose.returnsAt worker cause rejected rfl owner
  obtain ⟨_, _, _, _, _, _, _, _, _, image, _⟩ := dispose.returnsAfterLockFinalizationAt worker cause disposed finalized
  obtain ⟨toListing, toKeeper⟩ := listing.framesThroughSeals selected seals frame refl trans readerFrames listingFrames
  have admitted := raw.framesThroughCache seed (frame := frame) trans scope.admission
  have beforeRepair := trans admitted (trans toListing (trans toKeeper keeperFrame))
  exact ⟨dispose.returnsMarkedInterpreter source sameDisposal (rejected _) finalized,
    trans beforeRepair (trans repairFrame (scope.afterWorker trans)), image, beforeRepair⟩

variable {scope : FilePath → Prop} {through : Nat}
  {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}

local notation "sampledFrame" => SampledCheckpointRetryFrame directory scope through observe readBytes

omit extents seals selected valid following accepted ordered sameStat flat marked keeperRead in
/-- The failed-prune producer supplies the frames to authorization and
public return. The actual cached authorization fsync supplies settlement
for the second reboot, whose new namespace may contain later WAL names. -/
theorem RawWriteRebootEntry.startsRecoveryAfterFailedPrune
    {state : NativeReadyState} {target : Target} {firstFailed first authorized failed rebooted : heap}
    {firstOffset : Nat} {earlier : List (FilePath × IO.Error)} {diagnostic : IO.Error}
    (firstBoot : RawWriteRebootEntry state view observe (fun atHeap => (observe atHeap).files.names)
      readBytes firstFailed first)
    (firstReset : firstBoot.DurableReset)
    (atBoot : RawOpenRetryTrace.SelectedEntry view state target
      (fun atHeap => (observe atHeap).files.names) readBytes first)
    (initialWindow : state.writer.wal.NamespaceWindow state.session.directory firstOffset target.range.through
      (observe first).files.names)
    (sameDirectory : state.session.directory = directory)
    (sameFirst : target.first = state.writer.wal.active.first)
    (covered : target.range.through ≤ through)
    (protectedPaths : ∀ path, state.selectedRetryPath path → scope path)
    (keeperPath : scope (state.session.directory.file (.walSegment target.first)))
    (prior : source.FailedCalls first earlier entry)
    (returned : source.openTable input entry = .error diagnostic failed)
    (firstToEntry : sampledFrame first entry)
    (toAuthorization : sampledFrame entry authorized)
    (toFailedReturn : sampledFrame entry failed)
    (authorization : groupSync #[directory.path] afterKeeper = .ok () authorized)
    (authEffects : (callbacks).CachedRootEffects (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
      view observe readBytes seed.directoryRef seed.handle)
    (heldRoot : CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
      view seed.directoryRef seed.handle afterKeeper)
    (rootAtRepair : (observe afterKeeper).files.names state.session.directory.path =
      some ((view.descriptors afterKeeper).inode admission.cached.description))
    (readsRoot : ∀ {before result issued}, (callbacks).getDirectory seed.directoryRef before = .ok result issued →
      result = view.directory before seed.directoryRef)
    (crashFiles : (observe authorized).SettledCrashFiles (state.pruneRecoveryScope target.range.through)
      (observe authorized) →
      (observe authorized).SettledCrashFiles (state.pruneRecoveryScope target.range.through) (observe failed))
    (secondBoot : RawWriteRebootEntry state view observe (fun atHeap => (observe atHeap).files.names)
      readBytes failed rebooted)
    (secondReset : secondBoot.DurableReset) :
    source.FailedCalls first (earlier ++ [(input, diagnostic)]) failed ∧
      RawOpenRetryTrace.SelectedEntry view state target (fun atHeap => (observe atHeap).files.names) readBytes rebooted ∧
      TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
      (view.descriptors rebooted).slots = [] ∧
      RawOpenRetryTrace.RecoveryObservations view state target observe readBytes firstOffset target.range.through rebooted := by
  have firstToAuthorization := firstToEntry.trans toAuthorization
  have firstToFailedReturn := firstToEntry.trans toFailedReturn
  have authKeeper := (firstBoot.keeperCrashChoices firstReset atBoot sameFirst).1.frame firstToAuthorization.durable keeperPath
  have authWindow :
      state.writer.wal.NamespaceWindow state.session.directory firstOffset target.range.through
        (observe authorized).files.names :=
    initialWindow.frame (fun start _ within => by
      simpa only [sameDirectory] using firstToAuthorization.walNames start (Nat.le_trans within covered))
  have parent : (observe first).Frames (· = state.session.directory.path) (observe failed) := by
    rw [sameDirectory]
    exact firstToFailedReturn.parent
  have durable := (firstBoot.startsDurableRetry firstReset atBoot).2.frame
    (fun path selected => firstToFailedReturn.durable path (protectedPaths path selected)) parent
  have authorizedAtDirectory :
      (callbacks).syncPaths state.session.directory.path seed.directoryRef seed.activeRef seed.pendingRef
        #[state.session.directory.path] afterKeeper = .ok () authorized := by
    rw [sameDirectory]
    exact authorization
  obtain ⟨_, _, _, _, settled, _⟩ := authEffects.framesRootSync rootAtRepair heldRoot readsRoot authorizedAtDirectory
  have authSettled : (observe authorized).SettledCrashFiles
      (state.pruneRecoveryScope target.range.through) (observe authorized) := by
    refine ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, ?_, fun _ _ _ _ _ _ _ present => present⟩
    intro names possible path inside
    obtain ⟨file, rfl⟩ := NativeReadyState.pruneRecoveryScope_child inside
    exact settled names possible file
  exact ⟨.next prior input returned,
    secondBoot.startsRecoveryAfterFramedPrune secondReset sameFirst atBoot.manifest durable
      authKeeper authWindow (crashFiles authSettled)⟩

/-- Both a failed suffix removal and an error at the following root
barrier extend the same failed-open chronology. Accepted removals
retain their live effects at the error heap. A barrier error may keep
an earlier map or settle the issued live map. The selected children
through the cutoff feed the same reboot proof in either case. -/
theorem MarkedWalExtentReports.extendsCheckpointRetryAfterFailedWalPruneBlock
    {first : heap} {earlier : List (FilePath × IO.Error)} (prior : source.FailedCalls first earlier entry)
    (readerFrames : source.fileCalls.ScopeFrames sampledFrame)
    (listingFrames : source.directoryCalls.ScopeFrames directory sampledFrame)
    (remembered : ∀ {path file before after}, remember path file before = .ok () after → sampledFrame before after)
    {authorized : heap} {cause : IO.Error}
    (authorization : groupSync #[directory.path] afterKeeper = .ok () authorized)
    (authorizedFrame : sampledFrame afterKeeper authorized)
    (needsPrune : layout.boundedPlan.newer ≠ [] ∨ layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (cutoff : through ≤ layout.boundedPlan.through)
    (outside : ∀ ordinal ∈ layout.boundedPlan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    (unlink : SampledCheckpointRetryFrame.WalUnlinkEffects directory scope through observe readBytes
      layout.boundedPlan source.remove)
    (stopped : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized =
      .error cause reached)
    (barrier : ∀ {unlinked}, ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized =
        .ok () unlinked → groupSync #[directory.path] unlinked = .error cause reached →
      ∃ (issued : heap) (handle : IO.FS.Handle) (effective : Bool),
        (callbacks).getDirectory seed.directoryRef unlinked = .ok (some handle) issued ∧
        RawFsyncTarget view unlinked issued handle ∧
        (observe issued).files.names directory.path =
          some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) ∧
        sampledFrame unlinked issued ∧
        (∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file) ∧
        ∀ diagnostic, (callbacks).sync handle issued = .error diagnostic reached →
          WalRootSyncEffect directory effective (observe issued) (observe reached) ∧
          (observe issued).Frames (· = directory.path) (observe reached) ∧
          ∀ path, scope path → ∀ inode, (observe issued).files.names path = some inode →
            readBytes reached inode = readBytes issued inode)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner dispose.reached)
    (cleanup : dispose.ScopeFrames finalized sampledFrame) :
    source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached ∧
      source.FailedCalls first (earlier ++ [(input, dispose.diagnostic cause)]) finalized.reached ∧
      sampledFrame entry finalized.reached ∧
      sampledFrame entry authorized ∧
      (∀ {state : NativeReadyState} {unlinked : heap},
        state.session.directory = directory → state.Valid →
        layout.target.first = state.writer.wal.active.first →
        ((layout.boundedPlan.newer.map Step.unlink).forM
          (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename))
          authorized = .ok () unlinked →
        (∀ {ordinal before after result},
          ¬ state.pruneRecoveryScope layout.target.range.through (directory.file (.walSegment ordinal)) →
          source.remove (directory.file (.walSegment ordinal)) before = .ok result after →
          RunCollection.ownedUnlinkResult result = .ok () →
          (observe before).CrashFileFrame (state.pruneRecoveryScope layout.target.range.through) (observe after)) →
        (∀ {issued : heap} {handle : IO.FS.Handle},
          (callbacks).getDirectory seed.directoryRef unlinked = .ok (some handle) issued →
          (observe unlinked).CrashFileFrame (state.pruneRecoveryScope layout.target.range.through) (observe issued)) →
        dispose.ScopeFrames finalized (fun before after =>
          (observe before).CrashFileFrame (state.pruneRecoveryScope layout.target.range.through) (observe after)) →
        (observe authorized).SettledCrashFiles (state.pruneRecoveryScope layout.target.range.through)
          (observe authorized) →
        (observe authorized).SettledCrashFiles (state.pruneRecoveryScope layout.target.range.through)
          (observe finalized.reached)) := by
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have checked := layout.boundedPlan_valid ((Plan.valid_iff layout.plan).mp valid.valid).2.2
  have extent : reads.wal.keeper.calls.metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size :=
    reads.wal.keeper.observesFile.extent
  have bounded : layout.boundedPlan.keeperSize ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [← bytes]
    change layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [extent]
    simp
  obtain ⟨repair, repairFrame⟩ := SampledCheckpointRetryFrame.afterFailedWalPruneBlock checked bytes bounded
    needsPrune cutoff outside authorization authorizedFrame unlink stopped (fun unlinks returned => by
      obtain ⟨_, _, _, loaded, target, bound, load, managed, physical⟩ := barrier unlinks returned
      obtain ⟨_, _, _, framed, _⟩ := (callbacks).framesPruneDirectoryError seed.directoryRef seed.activeRef seed.pendingRef
        loaded returned target bound load managed (fun diagnostic failed _ _ => physical diagnostic failed)
      exact framed)
  have keeperFrame := source.fileCalls.readKeeperKeepsFrame readerFrames SampledCheckpointRetryFrame.refl
    SampledCheckpointRetryFrame.trans remember remembered _ _ _ keeperRead
  obtain ⟨returned, framed, _, beforeRepair⟩ := extents.finalizesFailedRepairWithFrame seals selected valid following accepted ordered
    (frame := sampledFrame)
    sameStat flat marked keeperRead SampledCheckpointRetryFrame.refl SampledCheckpointRetryFrame.trans readerFrames
    listingFrames keeperFrame repair repairFrame dispose sameDisposal owner finalized cleanup
  refine ⟨returned, .next prior input returned, framed, beforeRepair.trans authorizedFrame, ?_⟩
  intro state unlinked sameDirectory ready targetFirst unlinks unlinkCrash loadCrash cleanupCrash settled
  let selectedScope := state.pruneRecoveryScope layout.target.range.through
  have managed (path : FilePath) (inside : selectedScope path) : ∃ file, path = directory.file file := by
    obtain ⟨file, named⟩ := NativeReadyState.pruneRecoveryScope_child inside
    exact ⟨file, named.trans (congrArg (fun current => current.file file) sameDirectory)⟩
  have offTarget := NativeReadyState.pruneRecoveryScope_excludesUnlinks
    sameDirectory ready targetFirst checked (Nat.le_refl layout.target.range.through)
  have throughUnlinks := CheckpointStorageObservation.CrashFileFrame.afterReturnedWalUnlinks offTarget unlinkCrash unlinks
  have returnedBarrier := failedPruneDirectoryOfReturnedUnlinks unlinks stopped
  obtain ⟨issued, handle, effective, loaded, target, bound, load, managedForRead, physical⟩ := barrier unlinks returnedBarrier
  obtain ⟨_, _, _, _, rootEffect⟩ := (callbacks).framesPruneDirectoryError seed.directoryRef seed.activeRef seed.pendingRef
    loaded returnedBarrier target bound load managedForRead (fun diagnostic raw _ _ => physical diagnostic raw)
  have throughIssue := throughUnlinks.trans (loadCrash loaded)
  exact (rootEffect.keepsSettledCrashFiles managed throughIssue settled).frame
    (cleanupCrash.afterWorker (fun earlier later => earlier.trans later))

omit extents seals selected following accepted ordered sameStat flat marked keeperRead in
/-- If the unlink loop itself returns an error, the selected crash
frame includes the failing call's reached effects and the actual cleanup.
This is the same authorization-to-return input to the sampled retry as
for an error at the root barrier. -/
theorem RawOpenCacheDisposal.settledCrashFilesAfterFailedWalUnlink
    {state : NativeReadyState} {authorized : heap} {cause : IO.Error}
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner dispose.reached)
    (sameDirectory : state.session.directory = directory)
    (ready : state.Valid)
    (targetFirst : layout.target.first = state.writer.wal.active.first)
    (stopped : ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename))
      authorized = .error cause reached)
    (unlink : ∀ ordinal ∈ layout.boundedPlan.newer, ∀ issued,
      ¬ state.pruneRecoveryScope layout.target.range.through (directory.file (.walSegment ordinal)) →
      (observe issued).CrashFileFrame (state.pruneRecoveryScope layout.target.range.through)
        (observe (NativeFileEffectProjection.reached (source.remove (directory.file (.walSegment ordinal)) issued))))
    (cleanup : dispose.ScopeFrames finalized (fun before after =>
      (observe before).CrashFileFrame (state.pruneRecoveryScope layout.target.range.through) (observe after)))
    (settled : (observe authorized).SettledCrashFiles (state.pruneRecoveryScope layout.target.range.through)
      (observe authorized)) :
    (observe authorized).SettledCrashFiles (state.pruneRecoveryScope layout.target.range.through)
      (observe finalized.reached) := by
  let selectedScope := state.pruneRecoveryScope layout.target.range.through
  have checked := layout.boundedPlan_valid ((Plan.valid_iff layout.plan).mp valid.valid).2.2
  have outside := NativeReadyState.pruneRecoveryScope_excludesUnlinks
    sameDirectory ready targetFirst checked (Nat.le_refl layout.target.range.through)
  have throughUnlinks := CheckpointStorageObservation.CrashFileFrame.afterWalUnlinks
    (write := stageWrite) (sync := groupSync) (rename := source.rename) outside unlink authorized
  have toError : (observe authorized).CrashFileFrame selectedScope (observe reached) := by
    simpa only [stopped, NativeFileEffectProjection.reached] using throughUnlinks
  exact settled.frame (toError.trans (cleanup.afterWorker (fun before after => before.trans after)))

end FailedMarkedRepair

section SelectedRetry

private def keepsWalNames {heap : Type} (directory : DiskDirectory) (names : heap → FilePath → Option Nat)
    (before after : heap) : Prop :=
  ∀ start, (names after (directory.file (.walSegment start))).isSome =
    (names before (directory.file (.walSegment start))).isSome

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {state : NativeReadyState}
  {source : RawMarkedOpenInterpreter heap stream} {first entry : heap} {input : FilePath}
  {target : Target} {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {earlier : List (FilePath × IO.Error)} {prior : source.FailedCalls first earlier entry}
  {firstOffset through : Nat} {keep : heap → Prop}

local notation "dir" => state.session.directory
local notation "retryNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "liveFiles" => fun atHeap => CheckpointSurvivingFiles.mk (retryNames atHeap) fun inode => [visible atHeap inode]
local notation "catalog" => fun atHeap => state.writer.wal.NamespaceWindow dir firstOffset through (retryNames atHeap)
local notation "selectedWal" =>
  RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through
local notation "walNameFrame" => keepsWalNames dir retryNames
local notation "retryFrame" => fun entry reached =>
  state.SelectedRetryFrame (storage entry) (storage reached) (visible entry) (visible reached)

variable {history : List WAL.Write} {layout : CanonicalKeeperLayout (view.files entry).image history}
  {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input state.session.directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
  (extents : MarkedWalExtentReports prepared listing)

include extents

omit extents in
/-- Retain the worker's reached keeper through actual cleanup, and extend
the selected retry at the same public error return. -/
private theorem RawOpenRetryTrace.SelectedEffects.appendsFinalizedRepair
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep prior)
    {worker returnedAt : heap} {diagnostic : IO.Error}
    (returned : source.openTable input entry = .error diagnostic returnedAt)
    (image : (view.files returnedAt).image = (view.files worker).image)
    (effects : EffectTrace target (view.files entry).image (view.files worker).image)
    (kept : retryFrame entry returnedAt)
    (keeperAtError : RawOpenRetryTrace.KeeperAt view dir target retryNames visible worker)
    (keeperCleanup : (liveFiles worker).Frames (· = (dir).file (.walSegment target.first)) (liveFiles returnedAt))
    (durability : keep entry → state.SelectedRetryDurability target (storage entry))
    (carries : RawOpenRetryTrace.KeeperAt view dir target retryNames visible returnedAt →
      state.SelectedRetryDurability target (storage returnedAt) → keep entry → keep returnedAt) :
    RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep
      (prior.next input returned) := by
  have keeperAt : RawOpenRetryTrace.KeeperAt view dir target retryNames visible returnedAt := by
    unfold RawOpenRetryTrace.KeeperAt at keeperAtError ⊢
    rw [image, keeperAtError]
    exact (keeperCleanup.visiblePayload (names := retryNames) (bytes := visible) rfl).symm
  have trace : EffectTrace target (view.files entry).image (view.files returnedAt).image := image.symm ▸ effects
  exact .append (calls := .next .empty input returned) before (.inr trace) kept.live
    (fun selected => carries keeperAt ((durability selected).frame kept.durable kept.parent) selected)

/-- Follow the selected reads and bounded repair on the cache allocated
by this open. The cleanup exposes the worker's changed keeper to the
next attempt and transports the earlier durable selections separately. -/
theorem MarkedWalExtentReports.extendsFailedRepair
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {cause : IO.Error}
    (repair : let sync := source.keeperCallbacks.withFileReads source.fileCalls
      finishBoundedMarkedOpen dir layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
        source.remove (source.stage.stage seed.pendingRef sync.modifyPending)
        (sync.syncPaths (dir).path seed.directoryRef seed.activeRef seed.pendingRef) source.rename afterKeeper =
      .error cause reached)
    (effects : EffectTrace layout.target (view.files entry).image (view.files reached).image)
    (repairFrame : retryFrame afterKeeper reached)
    (keeperAtError : RawOpenRetryTrace.KeeperAt view dir target retryNames visible reached)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (durability : keep entry → state.SelectedRetryDurability target (storage entry))
    (carries : (view.files finalized.reached).image = (view.files reached).image →
      RawOpenRetryTrace.KeeperAt view dir target retryNames visible finalized.reached →
      state.SelectedRetryDurability target (storage finalized.reached) → keep entry → keep finalized.reached) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep
        (prior.next input returned) ∧ (view.files finalized.reached).image = (view.files reached).image := by
  obtain ⟨returned, kept, image, _⟩ := extents.finalizesFailedRepairWithFrame seals selected valid following accepted ordered
    (frame := retryFrame)
    sameStat flat marked keeperRead (fun atHeap => NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap))
    NativeReadyState.SelectedRetryFrame.trans readerFrames listingFrames keeperFrame repair repairFrame dispose sameDisposal
    owner finalized scope
  exact ⟨returned, before.appendsFinalizedRepair returned image (sameTarget ▸ effects) kept keeperAtError
    keeperCleanup durability (carries image), image⟩

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "stageWrite" => LongKeeperStageCallbacks.stage source.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks (DiskDirectory.path dir) seed.directoryRef seed.activeRef seed.pendingRef

local notation "liveImage" => fun atHeap => LockedFileState.image (OpenCloseHeapView.files view atHeap)

local notation "durableKeeperFile" => fun before after =>
  CheckpointSurvivingFiles.Frames (fun path => path = DiskDirectory.file dir (DiskFile.walSegment target.first))
    (CheckpointStorageObservation.files (storage before)) (CheckpointStorageObservation.files (storage after))

omit extents in
/-- The first reboot fixes the durable bytes of the selected keeper.
The earlier read-only rejections and the current attempt's admission,
read and release callbacks preserve that same file up to repair. -/
theorem MarkedDirectoryReadReport.keepsLiveKeeperBeforeRepair
    (listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf)
    (attempts : source.FailedCalls first earlier entry)
    {failed : heap}
    (reboot : RawWriteRebootEntry state view storage retryNames visible failed first)
    (reset : reboot.DurableReset)
    (atBoot : RawOpenRetryTrace.SelectedEntry view state target retryNames visible first)
    (sameFirst : target.first = state.writer.wal.active.first)
    (failedKeeper : ∀ {previous : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
      source.FailedCalls first previous before → List.IsPrefix (previous ++ [(path, cause)]) earlier →
      source.openTable path before = .error cause after → durableKeeperFile before after)
    (cacheKeeper : raw.CacheFrames seed durableKeeperFile)
    (readKeeper : source.fileCalls.ScopeFrames durableKeeperFile)
    (listKeeper : source.directoryCalls.ScopeFrames dir durableKeeperFile)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper : heap}
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (longer : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (returned : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper) :
    RawOpenRetryTrace.LiveKeeperCrashChoices dir target (storage afterKeeper) := by
  have refl (atHeap : heap) : durableKeeperFile atHeap atHeap := fun _ _ => ⟨rfl, fun _ _ => rfl⟩
  have trans {before middle after : heap} (left : durableKeeperFile before middle)
      (right : durableKeeperFile middle after) : durableKeeperFile before after := left.trans right
  have previous := attempts.framesAfter .empty durableKeeperFile refl trans (fun prior inside call =>
    failedKeeper prior (by simpa only [List.nil_append] using inside) call)
  have admitted := raw.framesThroughCache seed (frame := durableKeeperFile) trans cacheKeeper
  obtain ⟨listed, sealed⟩ := listing.framesThroughSeals selected seals durableKeeperFile refl trans readKeeper listKeeper
  have keeper := source.fileCalls.longKeeperReadFrames readKeeper refl trans
    (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle)) _ longer returned
  exact (reboot.keeperCrashChoices reset atBoot sameFirst).1.frame
    (trans previous (trans admitted (trans listed (trans sealed keeper)))) rfl

section FailedPruneBlock

local notation "keeperPath" => DiskDirectory.file dir (DiskFile.walSegment (Target.first target))
local notation "keeperPayload" => fun atHeap => Option.map (visible atHeap) (retryNames atHeap keeperPath)

local notation "pruneUnlinks" => fun ordinals => List.forM (List.map Step.unlink ordinals)
  (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)

/-- Re-enter the selected retry at the actual public error after a
failed unlink or a failed post-prune directory barrier. The accepted
removals, reached victim and cleanup determine the next live suffix. -/
theorem MarkedWalExtentReports.extendsFailedPruneBlock
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (firstValid : (view.files first).image.Valid target)
    (firstSelected : selectedWal first)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper authorized worker : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (liveImage entry).directory.active.manifest checkpoint)
    (valid : Prepared (liveImage entry) layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1, layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (liveImage entry).directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    (within : through ≤ target.range.through)
    (needsPrune : layout.boundedPlan.newer ≠ [] ∨ layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (authorizedAt : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (authorizedImage : liveImage authorized = (liveImage entry).syncDirectory)
    (authorizedNames : walNameFrame entry authorized)
    (authorizedKeeper : keeperPayload authorized = keeperPayload entry)
    (authorizedFrame : retryFrame afterKeeper authorized)
    (unlink : ∀ {ordinal start finish result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      RawOpenRetryTrace.WalUnlinkEffect view state target storage visible retryFrame ordinal start finish true)
    {cause : IO.Error}
    (pruneFailed : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized =
      .error cause worker)
    (unlinkError : pruneUnlinks layout.boundedPlan.newer authorized = .error cause worker →
      ∀ {completed remaining : List Nat} {victim : Nat} {atVictim : heap},
        layout.boundedPlan.newer = completed ++ victim :: remaining →
        pruneUnlinks completed authorized = .ok () atVictim →
        (source.remove ((dir).file (.walSegment victim)) atVictim = .error cause worker ∨
          ∃ result, source.remove ((dir).file (.walSegment victim)) atVictim = .ok result worker ∧
            RunCollection.ownedUnlinkResult result = .error cause) →
        ∃ removed, RawOpenRetryTrace.WalUnlinkEffect view state target storage visible retryFrame
          victim atVictim worker removed)
    (barrierError : ∀ {unlinked}, pruneUnlinks layout.boundedPlan.newer authorized = .ok () unlinked →
      groupSync #[(dir).path] unlinked = .error cause worker →
      ∃ (issued : heap) (handle : IO.FS.Handle) (effective : Bool),
        (callbacks).getDirectory seed.directoryRef unlinked = .ok (some handle) issued ∧
        RawFsyncTarget view unlinked issued handle ∧
        retryNames issued (dir).path =
          some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) ∧
        liveImage issued = liveImage unlinked ∧
        (∀ start, retryNames issued ((dir).file (.walSegment start)) =
          retryNames unlinked ((dir).file (.walSegment start))) ∧
        keeperPayload issued = keeperPayload unlinked ∧ retryFrame unlinked issued ∧
        ∀ diagnostic, (callbacks).sync handle issued = .error diagnostic worker →
          (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
          retryNames issued (dir).path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
          WalRootSyncEffect dir effective (storage issued) (storage worker) ∧
          (storage issued).Frames (· = (dir).path) (storage worker) ∧
          liveImage worker = (if effective then (liveImage issued).syncDirectory else liveImage issued) ∧
          ∀ path, state.selectedRetryPath path ∨ path = keeperPath → ∀ inode,
            retryNames issued path = some inode → visible worker inode = visible issued inode)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed worker)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files worker).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (cleanup : dispose.ScopeFrames finalized retryFrame)
    (cleanupWal : dispose.ScopeFrames finalized (fun start finish =>
      (liveFiles start).Frames (· = keeperPath) (liveFiles finish) ∧ walNameFrame start finish)) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) := by
  have checked := layout.boundedPlan_valid ((Plan.valid_iff layout.plan).mp valid.valid).2.2
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have measured : reads.wal.keeper.calls.metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size :=
    reads.wal.keeper.observesFile.extent
  have enough : layout.boundedPlan.keeperSize ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [← bytes]
    change layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [measured]
    simp
  have repair := finishBoundedMarkedOpen_errorDuringPrune checked bytes enough needsPrune authorizedAt pruneFailed
  have later (start : Nat) (present : start ∈ layout.boundedPlan.newer) : target.range.through < start :=
    sameTarget ▸ ((Plan.valid_iff _).mp checked |>.2.2 start present)
  let invariant := LivePruneAt view state target storage visible entry afterKeeper firstOffset through retryFrame
  have initial := (before.preserves firstValid).2.2.2 firstSelected
  have atAuthorization : invariant authorized :=
    LivePruneAt.authorized initial authorizedImage authorizedNames authorizedKeeper authorizedFrame
  have folded := foldWalUnlinksWithPrefix dir layout.boundedPlan source.remove stageWrite groupSync source.rename
    (fun (_ : Unit) => invariant) (fun _ _ => ()) (initial := ()) atAuthorization
    (fun member called accepted prior =>
      LivePruneAt.afterUnlink prior within (later _ member) NativeReadyState.SelectedRetryFrame.trans
        (unlink member called accepted))
  have atWorker : invariant worker := by
    cases unlinks : pruneUnlinks layout.boundedPlan.newer authorized with
    | error diagnostic stopped =>
      have reported := pruneFailed
      rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at reported
      have same : EStateM.Result.error diagnostic stopped = (EStateM.Result.error cause worker :
          EStateM.Result IO.Error heap Unit) := by
        simpa only [Bind.bind, EStateM.bind, unlinks] using reported
      obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj same
      simp only [unlinks] at folded
      obtain ⟨completed, victim, remaining, atVictim, ordinal, prefixReturned, reachedVictim, failedVictim⟩ := folded
      obtain ⟨removed, observed⟩ := unlinkError unlinks ordinal prefixReturned failedVictim
      have listed : victim ∈ layout.boundedPlan.newer := by
        rw [ordinal]
        exact List.mem_append_right _ List.mem_cons_self
      exact LivePruneAt.afterUnlink reachedVictim within (later _ listed)
        NativeReadyState.SelectedRetryFrame.trans observed
    | ok value unlinked =>
      cases value
      simp only [unlinks] at folded
      have failed := failedPruneDirectoryOfReturnedUnlinks unlinks pruneFailed
      obtain ⟨_, _, _, loaded, rootSlot, bound, loadImage, loadNames, loadKeeper, loadFrame, syncEffect⟩ :=
        barrierError unlinks failed
      obtain ⟨_, rawFault, _⟩ :=
        (callbacks).rawDirectoryErrorAfterRead seed.directoryRef seed.activeRef seed.pendingRef loaded failed
      obtain ⟨rootEffect, parent, syncImage, syncVisible⟩ := syncEffect _ rawFault rootSlot.live bound
      have syncFrame := rootEffect.framesSelectedRetry parent (fun path selected => syncVisible path (.inl selected))
      exact LivePruneAt.afterBarrier folded loadImage loadNames loadKeeper rootEffect syncImage
        (syncVisible keeperPath (.inr rfl)) (loadFrame.trans syncFrame) NativeReadyState.SelectedRetryFrame.trans
  obtain ⟨trace, window, keeperAtError, suffix, repairFrame⟩ := atWorker
  obtain ⟨returned, frame, image, _⟩ := extents.finalizesFailedRepairWithFrame seals selected valid following accepted ordered
    (frame := retryFrame) sameStat flat marked keeperRead
    (fun atHeap => NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap))
    NativeReadyState.SelectedRetryFrame.trans readerFrames listingFrames keeperFrame repair
    repairFrame dispose sameDisposal owner finalized cleanup
  obtain ⟨keeper, names⟩ := cleanupWal.afterWorker (fun earlier later =>
    ⟨earlier.1.trans later.1, fun start => (later.2 start).trans (earlier.2 start)⟩)
  refine ⟨returned, before.appendsFinalizedRepair returned image trace frame keeperAtError keeper
    (fun initial => initial.2.2.1) ?_⟩
  intro keeperAt durable _
  exact ⟨window.frame (fun start _ _ => names start), keeperAt, durable,
    suffix.framePresence (congrArg (fun image : FileImage => image.later.visible) image) (fun start _ => names start)⟩

local notation "scratch" => DiskDirectory.file dir DiskFile.stagedWal
local notation "scratchFrame" => fun start finish =>
  CheckpointSurvivingFiles.Frames (· = keeperPath) (liveFiles start) (liveFiles finish) ∧
  walNameFrame start finish ∧ retryFrame start finish

private def withoutScratch (files : LockedFileState FileImage) : LockedFileState FileImage :=
  { files with image := files.image.withScratch none }

omit extents in
private theorem restoresScratch {before after : LockedFileState FileImage} {staged : Option (ByteArray × Bool)}
    (others : withoutScratch after = withoutScratch before) (scratchContents : after.image.keeper.staged = staged) :
    after = { before with image := before.image.withScratch staged } := by
  subst staged
  exact congrArg (fun f : LockedFileState FileImage =>
    { f with image := f.image.withScratch after.image.keeper.staged }) others

local notation "stagePaths" => fun path => path = keeperPath ∨
  (NativeReadyState.selectedRetryPath state path ∧ path ≠ DiskDirectory.path dir) ∨
  ∃ n, ((firstOffset ≤ n ∧ n ≤ through) ∨ n ∈ Plan.newer (CanonicalKeeperLayout.boundedPlan layout)) ∧
    path = DiskDirectory.file dir (DiskFile.walSegment n)
local notation "stageSurvivors" => fun before after =>
  CheckpointStorageObservation.NameFrame stagePaths (storage before) (storage after) ∧ durableKeeperFile before after

/-- A failed fsync of the freshly written WAL.next stops before keeper rename.
The actual pending lookup and filtered removal select its descriptor. Cleanup
then extends the same public retry ledger for either observed durability result. -/
theorem MarkedWalExtentReports.extendsStageSyncError
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (firstValid : (view.files first).image.Valid target)
    (firstSelected : selectedWal first)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper authorized pruned created written flushed recorded loaded consumed worker : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (liveImage entry).directory.active.manifest checkpoint)
    (valid : Prepared (liveImage entry) layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1, layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (liveImage entry).directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFiles : source.fileCalls.ScopeFrames (fun before after => liveImage after = liveImage before))
    (within : through ≤ target.range.through)
    (longer : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (authorize : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (authorizationImage : liveImage authorized = (liveImage afterKeeper).syncDirectory)
    (authorizationNames : walNameFrame entry authorized)
    (authorizationKeeper : keeperPayload authorized = keeperPayload entry)
    (authorizationFrame : retryFrame afterKeeper authorized)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (unlink : ∀ {ordinal start finish result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      RawOpenRetryTrace.WalUnlinkEffect view state target storage visible retryFrame ordinal start finish true)
    (pruneBarrier : ∀ {unlinked}, pruneUnlinks layout.boundedPlan.newer authorized = .ok () unlinked →
      groupSync #[(dir).path] unlinked = .ok () pruned →
      liveImage pruned = (liveImage unlinked).syncDirectory ∧ scratchFrame unlinked pruned)
    {file : IO.FS.Handle}
    (acquired : source.stage.acquire scratch pruned = .ok file created)
    (wrote : source.stage.write file layout.keeper.bytes created = .ok () written)
    (flushedBytes : source.stage.flush file written = .ok () flushed)
    (remembered : (callbacks).modifyPending seed.pendingRef (pushPending scratch file) flushed = .ok () recorded)
    (stored : view.pending recorded seed.pendingRef = pushPending scratch file (view.pending flushed seed.pendingRef))
    (stageFrames : source.stage.StagingWriteFrames callbacks scratch (· = keeperPath) view storage seed.pendingRef
      (fun a b => withoutScratch (view.files b) = withoutScratch (view.files a) ∧ scratchFrame a b))
    (flushImage : ∀ {slot inode}, ScopedStagingFile scratch (· = keeperPath) view storage file slot inode written →
      source.stage.flush file written = .ok () flushed →
      (liveImage flushed).keeper.staged = some (visible flushed inode, false))
    (recordImage : (callbacks).modifyPending seed.pendingRef (pushPending scratch file) flushed = .ok () recorded →
      (liveImage recorded).keeper.staged = (liveImage flushed).keeper.staged)
    {entries : List (FilePath × IO.FS.Handle)}
    (read : (callbacks).getPending seed.pendingRef recorded = .ok entries loaded)
    (loadEffect : entries = view.pending recorded seed.pendingRef ∧ view.files loaded = view.files recorded ∧
      scratchFrame recorded loaded)
    (cleared : (callbacks).setPending seed.pendingRef (entries.filter (fun item => item.1 != scratch)) loaded = .ok () consumed)
    (clearEffect : view.files consumed = view.files loaded ∧ scratchFrame loaded consumed)
    {cause : IO.Error} {effective : Bool}
    (failed : (callbacks).sync file consumed = .error cause worker)
    {buffered : heap → IO.FS.Handle → ByteArray}
    (staging : source.stage.StagingPrefixEffects callbacks scratch (· = keeperPath) view storage visible buffered
      seed.pendingRef)
    (captured : (view.handle created file).1.inode (view.handle created file).2.1.description =
      (view.descriptors created).inode (view.handle created file).2.1.description)
    (fsync : let inode := (view.descriptors consumed).inode (view.handle consumed file).2.1.description
      FsyncResult (view.files consumed, visible consumed inode, (storage consumed).files.bytes inode)
        ({ view.files consumed with image := (liveImage consumed).withScratch (some (layout.keeper.bytes, true)) },
          visible consumed inode, [visible consumed inode]) effective
        (projectResult (fun h => (view.files h, visible h inode, (storage h).files.bytes inode))
          ((callbacks).sync file consumed)))
    (fsyncFrame : retryNames worker scratch = retryNames consumed scratch ∧ scratchFrame consumed worker)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed worker)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files pruned).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (cleanupWal : dispose.ScopeFrames finalized (fun start finish =>
      (liveFiles start).Frames (· = keeperPath) (liveFiles finish) ∧ walNameFrame start finish)) :
    let inode := (view.handle created file).1.inode (view.handle created file).2.1.description
    ∃ returned : source.openTable input entry =
        .error (dispose.diagnostic (IO.userError s!"sync failed for '{scratch}': {cause}")) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) ∧
      liveImage finalized.reached = (liveImage pruned).withScratch (some (layout.keeper.bytes, effective)) ∧
      (liveFiles pruned).Frames (· = keeperPath) (liveFiles finalized.reached) ∧
      retryNames worker scratch = some inode ∧ visible worker inode = layout.keeper.bytes ∧
      (storage worker).files.bytes inode = (if effective then [layout.keeper.bytes] else (storage consumed).files.bytes inode) ∧
      (∀ {failedBefore} (firstBoot : RawWriteRebootEntry state view storage retryNames visible failedBefore first),
        firstBoot.DurableReset → RawOpenRetryTrace.SelectedEntry view state target retryNames visible first →
        target.first = state.writer.wal.active.first →
        (∀ {previous : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
          source.FailedCalls first previous before → List.IsPrefix (previous ++ [(path, cause)]) earlier →
          source.openTable path before = .error cause after → durableKeeperFile before after) →
        raw.CacheFrames seed durableKeeperFile → source.fileCalls.ScopeFrames durableKeeperFile →
        source.directoryCalls.ScopeFrames dir durableKeeperFile →
        (groupSync #[(dir).path] afterKeeper = .ok () authorized → durableKeeperFile afterKeeper authorized) →
        (∀ {n start finish result}, n ∈ layout.boundedPlan.newer →
          source.remove ((dir).file (.walSegment n)) start = .ok result finish →
          RunCollection.ownedUnlinkResult result = .ok () → durableKeeperFile start finish) →
        (∀ {unlinked loadedRoot root}, pruneUnlinks layout.boundedPlan.newer authorized = .ok () unlinked →
          (callbacks).getDirectory seed.directoryRef unlinked = .ok (some root) loadedRoot →
          durableKeeperFile unlinked loadedRoot ∧ ∀ n ∈ layout.boundedPlan.newer,
            retryNames loadedRoot ((dir).file (.walSegment n)) = retryNames unlinked ((dir).file (.walSegment n))) →
        (∀ {unlinked loadedRoot root}, pruneUnlinks layout.boundedPlan.newer authorized = .ok () unlinked →
          (callbacks).getDirectory seed.directoryRef unlinked = .ok (some root) loadedRoot →
          (callbacks).sync root loadedRoot = .ok () pruned → WalRootSyncEffect dir true (storage loadedRoot) (storage pruned)) →
        source.stage.StagingFileFrames callbacks scratch (· = keeperPath) view storage seed.pendingRef stageSurvivors →
        ((callbacks).sync file consumed = .error cause worker → RegularFileSyncEffect inode
          ((storage worker).files.bytes inode) (storage consumed) (storage worker)) →
        dispose.ScopeFrames finalized stageSurvivors →
        ∀ {rebooted} (boot : RawWriteRebootEntry state view storage retryNames visible finalized.reached rebooted),
          target.pair.manifest = state.writer.target.pair.manifest →
          ∃ old, retryNames afterKeeper keeperPath = some old ∧ retryNames rebooted keeperPath = some old ∧
            target.Accepts (some (visible rebooted old)) ∧
            (∀ n ∈ layout.boundedPlan.newer, retryNames rebooted ((dir).file (.walSegment n)) = none) ∧
            RawOpenRetryTrace.SelectedEntry view state target retryNames visible rebooted ∧
            TryLockObserves (view.files rebooted).owners dir (.ok true) ∧ (view.descriptors rebooted).slots = [] ∧
            (boot.DurableReset → selectedWal rebooted) ∧
            (target.range.through ≤ through → boot.DurableReset →
              ∀ {opened : NativeOpenedHandle heap} (last : NativeOpenedPosition opened)
                (sameState : state = last.current.ready.state)
                {request : WriteRequest} {batch : List WAL.Write} {table : PackedTable}
                (handoff : last.current.SelectedWriteReboot view storage visible firstOffset
                  request batch table target failedBefore first)
                {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer} {writeCause : IO.Error}
                (_reportedWrite : (NativeReturnedCall.write request (.error (.commitUnknown writeCause))).Reaches
                  writes issuer (last.pins.map NativeOpenedPin.raw) last.reached failedBefore)
                {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
                (_ledger : origin.LedgerSuffix events last.current),
                NativeExecutionPosition.SelectedWriteReboot.OpenContinuation last view storage visible
                  firstOffset request batch target rebooted source origin events writeCause)) := by
  intro inode
  have compose {a b c : heap} (left : scratchFrame a b) (right : scratchFrame b c) : scratchFrame a c :=
    ⟨left.1.trans right.1, fun start => (right.2.1 start).trans (left.2.1 start), left.2.2.trans right.2.2⟩
  have startImage := listing.imageAfterLongKeeper selected seals keeperFiles _ longer keeperRead
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have checked := layout.boundedPlan_valid ((Plan.valid_iff layout.plan).mp valid.valid).2.2
  have later (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) : target.range.through < ordinal :=
    sameTarget ▸ ((Plan.valid_iff _).mp checked |>.2.2 ordinal member)
  let invariant := LivePruneAt view state target storage visible entry afterKeeper firstOffset through retryFrame
  have initial := (before.preserves firstValid).2.2.2 firstSelected
  have entered : invariant authorized := LivePruneAt.authorized initial
    (authorizationImage.trans (congrArg FileImage.syncDirectory startImage)) authorizationNames authorizationKeeper authorizationFrame
  obtain ⟨unlinked, unlinks, barrier, unlinkedKeeper⟩ := foldReturnedPrune dir layout.boundedPlan source.remove
    stageWrite groupSync source.rename (fun (_ : Unit) h => invariant h) (fun _ _ => ()) (initial := ()) entered
    (fun member called accepted earlier => LivePruneAt.afterUnlink earlier within (later _ member)
      NativeReadyState.SelectedRetryFrame.trans (unlink member called accepted)) prune
  obtain ⟨pruneImage, pruneFrame⟩ := pruneBarrier unlinks barrier
  have atPrune : invariant pruned := LivePruneAt.framed unlinkedKeeper
    (pruneImage.symm ▸ unlinkedKeeper.1.syncPruned)
    (congrArg (fun image => image.keeper.active) pruneImage)
    (congrArg (fun image => image.later.visible) pruneImage)
    pruneFrame.2.1 (pruneFrame.1.visiblePayload (names := retryNames) (bytes := visible) rfl)
    pruneFrame.2.2 NativeReadyState.SelectedRetryFrame.trans
  have chosen : entries.find? (fun entry => entry.1 == scratch) = some (scratch, file) := by
    rw [loadEffect.1, stored]
    simp [pushPending]
  obtain ⟨slot, replacement, opened, afterWrite, _, issued, payload, flushedPayload, registeredFrames, prefixFrames, _⟩ :=
    source.stage.issuesStagedFile callbacks staging (fun result _ => result)
      acquired wrote flushedBytes remembered read chosen cleared
  obtain ⟨otherFiles, stagedFrame⟩ := registeredFrames stageFrames
    (fun h => ⟨rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ => rfl,
      NativeReadyState.SelectedRetryFrame.refl state (storage h) (visible h)⟩)
    (fun left right => ⟨right.1.trans left.1, compose left.2 right.2⟩)
  have scratchContents := (recordImage remembered).trans (flushImage afterWrite flushedBytes)
  rw [flushedPayload] at scratchContents
  have writtenImage := restoresScratch otherFiles scratchContents
  have capturedInode : inode = replacement := captured.trans (opened.1.1.symm ▸ opened.1.2.2)
  have descriptor : RawFsyncTarget view created consumed file :=
    ⟨issued.1.1.trans opened.1.1.symm, issued.1.1.symm ▸ issued.1.2.1,
      (issued.1.1.symm ▸ issued.1.2.2).trans capturedInode.symm⟩
  have atIssue : retryNames consumed scratch = some inode ∧ visible consumed inode = layout.keeper.bytes :=
    capturedInode.symm ▸ ⟨issued.2.1, payload⟩
  have separate : retryNames consumed keeperPath ≠ some inode := capturedInode.symm ▸ issued.2.2 _ rfl
  obtain ⟨repair, files, trace, named, bytes, durable⟩ := (callbacks).longRepairStageSyncFails
    layout.boundedPlan _ source.stage seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename
    checked size (size ▸ longer) view retryNames visible (fun h => (storage h).files.bytes) authorize prune acquired
    wrote flushedBytes remembered stored read loadEffect.1 cleared failed descriptor atIssue
    (clearEffect.1.trans (loadEffect.2.1.trans writtenImage)) fsyncFrame.1 fsync atPrune.1
  have throughError := compose (compose stagedFrame loadEffect.2.2) (compose clearEffect.2 fsyncFrame.2)
  have atWorker : invariant worker := LivePruneAt.framed atPrune trace
    (congrArg (fun files => files.image.keeper.active) files)
    (congrArg (fun files => files.image.later.visible) files)
    throughError.2.1 (throughError.1.visiblePayload (names := retryNames) (bytes := visible) rfl)
    throughError.2.2 NativeReadyState.SelectedRetryFrame.trans
  have kept := source.fileCalls.longKeeperReadFrames readerFrames
    (fun h => NativeReadyState.SelectedRetryFrame.refl state (storage h) (visible h))
    NativeReadyState.SelectedRetryFrame.trans _ _ longer keeperRead
  have finalFrame := cleanupWal.afterWorker (fun left right =>
    ⟨left.1.trans right.1, fun start => (right.2 start).trans (left.2 start)⟩)
  obtain ⟨returned, effects, finalImage⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following
    accepted ordered sameStat flat marked keeperRead readerFrames listingFrames kept repair (sameTarget.symm ▸ trace)
    atWorker.2.2.2.2 atWorker.2.2.1 dispose sameDisposal ((congrArg LockedFileState.owners files).trans owner) finalized
    scope finalFrame.1 (fun selected => selected.2.2.1) (by
      intro image keeper durability _
      exact ⟨atWorker.2.1.frame (fun start _ _ => finalFrame.2 start), keeper, durability,
        atWorker.2.2.2.1.framePresence (congrArg (fun i : FileImage => i.later.visible) image)
          (fun start _ => finalFrame.2 start)⟩)
  refine ⟨returned, effects, finalImage.trans (congrArg LockedFileState.image files),
    throughError.1.trans finalFrame.1, named, bytes, durable, ?_⟩

  intro firstFailure firstBoot reset atBoot sameFirst failedKeeper cacheKeeper readKeeper listKeeper
    authKeeper unlinkKeeper readRoot rootEffect stageCrash fileEffect cleanupCrash
    rebooted boot manifest
  obtain ⟨old, oldAtStart, accepts⟩ := listing.keepsLiveKeeperBeforeRepair prior firstBoot reset atBoot sameFirst
    failedKeeper cacheKeeper readKeeper listKeeper selected seals longer keeperRead
  have beforeLoad := foldReturnedWalUnlinks dir layout.boundedPlan source.remove stageWrite groupSync source.rename
    (fun (_ : Unit) h => durableKeeperFile afterKeeper h) (fun _ _ => ()) (initial := ()) (authKeeper authorize)
    (fun member called accepted frame => frame.trans (unlinkKeeper member called accepted)) unlinks
  let syncer : RawSyncCalls heap :=
    ⟨⟨(callbacks).getDirectory, (callbacks).getPending, (callbacks).setPending, (callbacks).getActive,
      (callbacks).openRead⟩, (callbacks).sync⟩
  obtain ⟨root, issued, rootRead, rootSynced⟩ := syncer.rootGroupReturned barrier
  obtain ⟨rootLoad, loadNames⟩ := readRoot unlinks rootRead
  have rootSync := rootEffect unlinks rootRead rootSynced
  obtain ⟨removed, _⟩ := namesOfReturnedWalUnlinks dir layout.boundedPlan source.remove stageWrite groupSync source.rename
    retryNames (fun path => ∃ n, path = (dir).file (.walSegment n)) (fun n _ => ⟨n, rfl⟩)
    (fun member called accepted => by
      obtain ⟨_, victim, others, _⟩ := unlink member called accepted
      refine ⟨victim, ?_⟩
      intro path ⟨n, eq⟩ apart
      subst path
      exact others n (fun same => apart (same ▸ rfl))) unlinks
  have ⟨toIssue, issueBytes⟩ := (beforeLoad.trans rootLoad) keeperPath rfl
  have atPrunedOld := (rootSync.visible (.walSegment target.first)).trans (toIssue.trans oldAtStart)
  have composeSurvivors {a b c : heap} (left : stageSurvivors a b) (right : stageSurvivors b c) :
      stageSurvivors a c := ⟨left.1.trans right.1, left.2.trans right.2⟩
  have throughClear := prefixFrames stageCrash
    (fun h => ⟨(CheckpointStorageObservation.Frames.refl _ _).nameFrame, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩)
    composeSurvivors
  have fs := fileEffect failed
  have fsNames : (storage consumed).NameFrame stagePaths (storage worker) :=
    ⟨fun path _ => congrFun fs.names path, fun names possible =>
      ⟨names, .inr (fs.crashNames ▸ possible), fun _ _ => rfl⟩⟩
  have fsKeeper : durableKeeperFile consumed worker := (fs.frames (footprint := (· = keeperPath))
    (fun path eq other bound same => separate (eq ▸ same ▸ bound))).visible
  have afterWorker := cleanupCrash.afterWorker composeSurvivors
  have ⟨ns, byteFrame⟩ := composeSurvivors throughClear (composeSurvivors ⟨fsNames, fsKeeper⟩ afterWorker)
  have settled (names) (possible : names ∈ (storage pruned).crashNames) (path) (inside : stagePaths path) :
      names path = retryNames pruned path := by
    rcases inside with rfl | ⟨selected, notRoot⟩ | ⟨n, _, rfl⟩
    · exact rootSync.settled rfl names possible (.walSegment target.first)
    · obtain ⟨file, rfl⟩ := (NativeReadyState.selectedRetryPath_rootOrChild selected).resolve_left notRoot
      exact rootSync.settled rfl names possible file
    · exact rootSync.settled rfl names possible (.walSegment n)
  have fromPrune := ns.settledFrom settled
  have oldChoice (names) (possible : names ∈ (storage finalized.reached).crashNames) :=
    (fromPrune names possible keeperPath (.inl rfl)).trans atPrunedOld
  have oldBytes : ∀ payload ∈ (storage finalized.reached).files.bytes old, target.Accepts (some payload) := by
    intro payload possible
    have preserved := (byteFrame keeperPath rfl).2 old atPrunedOld
    rw [preserved, rootSync.bytes _ (.inl rfl) (.walSegment target.first) old atPrunedOld,
      issueBytes old oldAtStart] at possible
    exact accepts payload possible
  have immutable path selected notRoot :=
    (fromPrune _ boot.chosen path (.inr (.inl ⟨selected, notRoot⟩))).trans
      (ns.live path (.inr (.inl ⟨selected, notRoot⟩))).symm
  have retained := ((effects.preserves firstValid).2.2.2 firstSelected).2.2.1
  obtain ⟨namedOnBoot, acceptedOnBoot, next, vacant, empty⟩ :=
    boot.selectsSettledKeeper sameFirst manifest retained oldChoice oldBytes immutable
  have rebootWindow : catalog rebooted := atPrune.2.1.frame (fun n low high =>
    congrArg Option.isSome (fromPrune _ boot.chosen _ (.inr (.inr ⟨n, .inl ⟨low, high⟩, rfl⟩))))
  refine ⟨old, oldAtStart, namedOnBoot, acceptedOnBoot, ?_, next, vacant, empty,
    fun reset => boot.startsRecoveryObservations reset next rebootWindow, ?_⟩
  · intro n member
    exact (fromPrune _ boot.chosen _ (.inr (.inr ⟨n, .inr member, rfl⟩))).trans
      ((rootSync.visible (.walSegment n)).trans ((loadNames n member).trans (removed n member)))
  · intro covered reset opened last sameState request batch table handoff writes issuer writeCause
      reportedWrite origin events ledger
    have recovery := boot.startsRecoveryObservations reset next (rebootWindow.restrict (Nat.le_refl _) covered)
    intro returns afterCalls attempts
    exact handoff.opensReadyAfterRetryReboot reportedWrite ledger prior returned sameState boot next vacant recovery
      (returns := returns) (reached := afterCalls) (attempts := attempts)

end FailedPruneBlock

local notation "unlinkLoop" => List.forM (List.map Step.unlink layout.boundedPlan.newer)
  (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)

omit extents in
private theorem settlesPrunedWindow {unlinked pruned : heap}
    (live : catalog unlinked)
    (namesKept : ∀ start, retryNames pruned ((dir).file (.walSegment start)) =
      retryNames unlinked ((dir).file (.walSegment start)))
    (settled : ∀ names ∈ (storage pruned).crashNames, ∀ file,
      names ((dir).file file) = retryNames pruned ((dir).file file)) :
    state.writer.wal.SettledNamespaceWindow dir firstOffset through (storage pruned) := by
  have reached := live.frame (fun start _ _ => congrArg Option.isSome (namesKept start))
  exact ⟨reached, fun names allowed =>
    reached.frame (fun start _ _ => congrArg Option.isSome (settled names allowed (.walSegment start)))⟩

omit extents in
/-- Read and prune the live catalog once. The same accepted unlink loop
supports the returned live catalog and settlement at the actual
post-prune root barrier. -/
private theorem MarkedDirectoryReadReport.carriesPrunedCatalog
    (listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf)
    {checkpoint : Option (PackedTable × UInt64)}
    {beforeKeeper afterKeeper authorized unlinked synced reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (unlinks : unlinkLoop authorized = .ok () unlinked)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (keeperNames : walNameFrame beforeKeeper afterKeeper)
    (authorizationNames : walNameFrame afterKeeper authorized)
    (namesThroughStage : walNameFrame unlinked synced)
    (namesOfError : walNameFrame synced reached)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (later : ∀ ordinal ∈ layout.boundedPlan.newer, target.range.through < ordinal)
    (listed : ∀ start, target.range.through < start →
      ((retryNames authorized ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start)))
    (initial : catalog entry) (gone : (view.files finalized.reached).image.later.visible = []) :
    catalog finalized.reached ∧ RawOpenRetryTrace.LaterWalAt view dir target retryNames finalized.reached ∧
    catalog unlinked := by
  have trans {first middle last : heap} (before : walNameFrame first middle)
      (after : walNameFrame middle last) : walNameFrame first last := fun start => (after start).trans (before start)
  obtain ⟨throughListing, throughSeals⟩ :=
    listing.framesThroughSeals selected seals walNameFrame (fun _ _ => rfl) trans readerNames listingNames
  have admission := raw.framesThroughCache seed (frame := walNameFrame) trans namesOfCleanup.admission
  have beforePrune := trans (trans admission (trans throughListing throughSeals))
    (trans keeperNames authorizationNames)
  have atAuthorization := (initial.restrict (Nat.le_refl firstOffset) cutoffCovered).frame
    (fun start _ _ => beforePrune start)
  have prunedWindow := atAuthorization.afterAcceptedUnlinks (names := retryNames) bounded later
    (fun start beyond => (listed start beyond).mp)
    source.remove stageWrite groupSync source.rename unlinkNames unlinks
  have afterPrune := trans namesThroughStage
    (trans namesOfError (namesOfCleanup.afterWorker trans))
  obtain ⟨next, suffix⟩ := RawOpenRetryTrace.keepsCatalogAfterPruning (view := view) (target := target)
    (names := retryNames) prunedWindow firstCovered bounded (fun start _ => afterPrune start) gone
  exact ⟨next, suffix, prunedWindow through⟩

omit extents in
private theorem laterWalOutsideRepairScope (ready : state.Valid) {ordinal : Nat}
    (past : state.writer.wal.active.first < ordinal) :
    ¬ state.crashPath ((dir).file (.walSegment ordinal)) := by
  intro hit
  rcases NativeReadyState.crashPath_iff_write.mp hit with mark | keep | protectedPath
  · exact state.protectedPathNeWalFromActive ready (.inl mark) (Nat.le_of_lt past) rfl
  · exact (Nat.ne_of_gt past) ((dir).walSegment_path_injective keep)
  · exact state.protectedPathNeWalFromActive ready (.inr protectedPath) (Nat.le_of_lt past) rfl

local notation "stagedFrom" => LongKeeperRepair.StagedFrom dir layout.boundedPlan source.remove
  stageWrite groupSync source.rename

section FinalDirectorySync

variable {renamedHeap : heap}

local notation "rootInode" => DescriptorInventory.inode (CensusOpenAdmissionReports.reached admission)
  (DescriptorSlot.description (CensusOpenAdmissionReports.cached admission))
local notation "attachedRoot" => attachedReadSlot view seed.handle admission.cached rootInode
local notation "rootAt" => CachedKeeperReplacementRoot (NativeReadyState.repairDirectoryScope state
  (CensusOpenAdmissionReports.reached admission) (CensusOpenAdmissionReports.cached admission))
  view seed.directoryRef seed.handle
local notation "rootFrame" => fun before after => rootAt before → rootAt after
local notation "finalIssue" => reachedState (AlignedKeeperCacheCallbacks.getDirectory callbacks seed.directoryRef renamedHeap)

set_option maxHeartbeats 1200000 in
/-- Feed the actual repair stopped by the final directory fsync into
the same fixed opener's cleanup and failed-call prefix. With the
protected child frame, any later sampled reboot re-enters that same
target, whether it names the old keeper or the trimmed replacement.
The scoped catalog frames preserve presence and absence through that
same sample, starting at the returned post-prune root barrier. -/
theorem MarkedWalExtentReports.extendsFinalSyncError
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFiles : source.fileCalls.ScopeFrames (fun before after => liveImage after = liveImage before))
    {publicError : IO.Error} {effective : Bool}
    (workerStopped : source.workerObservingRepairRename seed.directoryRef seed.activeRef seed.pendingRef dir raw.lock
      (RawMarkedOpenInterpreter.makeCache dir seed.directoryRef seed.activeRef seed.pendingRef) seed.afterPending =
      .error publicError (reached, some renamedHeap))
    (readerRoot : source.fileCalls.ScopeFrames rootFrame)
    (renameRoot : ∀ {before}, source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      before = .ok () renamedHeap → rootFrame before renamedHeap)
    (readRef : ∃ after, (callbacks).getDirectory seed.directoryRef renamedHeap =
      .ok (view.directory renamedHeap seed.directoryRef) after)
    (readTarget : ∀ {issued}, (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) issued →
      attachedRoot renamedHeap → attachedRoot issued)
    (authorizationImage : ∀ {authorized}, groupSync #[(dir).path] afterKeeper = .ok () authorized →
      liveImage authorized = (liveImage afterKeeper).syncDirectory)
    (pruneImage : ∀ {authorized unlinked pruned}, groupSync #[(dir).path] afterKeeper = .ok () authorized →
      unlinkLoop authorized = .ok () unlinked → groupSync #[(dir).path] unlinked = .ok () pruned →
      liveImage pruned = (liveImage unlinked).syncDirectory)
    (unlinkImage : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () → liveImage after = (liveImage before).unlinkLater ordinal)
    (writeImage : ∀ {before after}, stageWrite ((dir).file .stagedWal) layout.target.trimmed before = .ok () after →
      liveImage after = (liveImage before).withScratch (some (layout.target.trimmed, false)))
    (stageSyncImage : ∀ {before after}, groupSync #[((dir).file .stagedWal)] before = .ok () after →
      (liveImage before).keeper.staged = some (layout.target.trimmed, false) →
      liveImage after = (liveImage before).withScratch (some (layout.target.trimmed, true)))
    (renameImage : ∀ {before}, source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      before = .ok () renamedHeap → (liveImage before).keeper.staged = some (layout.target.trimmed, true) →
      (liveImage before).effect layout.target (.replace .renameStaged) = some (liveImage renamedHeap))
    (loadImage : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue →
      liveImage finalIssue = liveImage renamedHeap)
    (openedRoot : retryNames seed.afterPending (dir).path =
      some rootInode)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (physical : source.stage.ReplacementPrefixStorageEffects callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.pendingRef seed.handle)
    (unlinkStorage : ∀ {ordinal before after result}, ¬ state.crashPath ((dir).file (.walSegment ordinal)) →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (storage before).Frames state.crashPath (storage after) ∧
      (CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
        view seed.directoryRef seed.handle before →
        CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
          view seed.directoryRef seed.handle after))
    (records : ∀ {file before after},
      (callbacks).modifyPending seed.pendingRef (pushPending ((dir).file .stagedWal) file) before = .ok () after →
      view.pending after seed.pendingRef = pushPending ((dir).file .stagedWal) file (view.pending before seed.pendingRef))
    (readsPending : ∀ {before entries loaded}, (callbacks).getPending seed.pendingRef before = .ok entries loaded →
      entries = view.pending before seed.pendingRef)
    (readsRoot : ∀ {before result readHeap}, (callbacks).getDirectory seed.directoryRef before = .ok result readHeap →
      result = view.directory before seed.directoryRef)
    (renameEffect : ∀ {authorized pruned recorded synced replacement},
      stagedFrom afterKeeper authorized pruned recorded synced →
      source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      synced = .ok () renamedHeap →
      retryNames synced ((dir).file .stagedWal) = some replacement →
      retryNames synced ((dir).file (.walSegment layout.keeper.first)) ≠ some replacement →
      WalKeeperRenameEffect dir layout.keeper.first replacement true
        (storage synced) (storage renamedHeap) (visible synced) (visible renamedHeap))
    (loadKeeper : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue →
      ∀ inode, retryNames renamedHeap ((dir).file (.walSegment layout.keeper.first)) = some inode →
        retryNames finalIssue ((dir).file (.walSegment layout.keeper.first)) = some inode ∧
        visible finalIssue inode = visible renamedHeap inode ∧
        (storage finalIssue).files.bytes inode = (storage renamedHeap).files.bytes inode)
    (currentReady : state.Valid) (targetAtKeeper : layout.target.first = state.writer.wal.active.first)
    (readPendingFrames : source.fileCalls.ScopeFrames
      (fun before after => view.pending before seed.pendingRef = [] → view.pending after seed.pendingRef = []))
    (liveEffects : source.stage.ReplacementPrefixLiveEffects callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible
      seed.directoryRef seed.pendingRef seed.handle source.remove)
    (namesOfRename : ∀ {authorized pruned recorded synced}, stagedFrom afterKeeper authorized pruned recorded synced →
      source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
        synced = .ok () renamedHeap →
      walNameFrame synced renamedHeap)
    (loadFrames : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue →
      retryFrame renamedHeap finalIssue ∧ walNameFrame renamedHeap finalIssue)
    (effect : ∀ {diagnostic}, (callbacks).sync seed.handle finalIssue = .error diagnostic reached →
      (view.handle finalIssue seed.handle).2.1 ∈ (view.descriptors finalIssue).slots →
      retryNames finalIssue (dir).path =
        some ((view.descriptors finalIssue).inode (view.handle finalIssue seed.handle).2.1.description) →
      liveImage reached = (if effective then (liveImage finalIssue).syncDirectory.syncKeeper else liveImage finalIssue) ∧
      WalRootSyncEffect dir effective (storage finalIssue) (storage reached) ∧
      (storage finalIssue).Frames (· = (dir).path) (storage reached) ∧
      ∀ path, state.selectedRetryPath path ∨ path = (dir).file (.walSegment layout.keeper.first) →
        ∀ inode, retryNames finalIssue path = some inode → visible reached inode = visible finalIssue inode)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (namesOfDirectorySync : ∀ {before after}, groupSync #[(dir).path] before = .ok () after → walNameFrame before after)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (listed : ∀ start, target.range.through < start →
      ((retryNames afterKeeper ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start)))
    (keeperStorage : (storage reached).files.Frames (· = (dir).file (.walSegment layout.keeper.first))
      (storage finalized.reached).files) :
    ∃ returned : source.openTable input entry =
        .error (dispose.diagnostic publicError) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) ∧
      (∃ replacement,
        retryNames finalized.reached ((dir).file (.walSegment layout.keeper.first)) = some replacement ∧
        (storage finalized.reached).files.bytes replacement = [layout.target.trimmed] ∧
        visible finalized.reached replacement = target.trimmed ∧
        ∃ authorized pruned recorded synced created file slot,
          stagedFrom afterKeeper authorized pruned recorded synced ∧
          source.stage.acquire ((dir).file .stagedWal) pruned = .ok file created ∧
          attachedReadSlot view file slot replacement created ∧
          retryNames created ((dir).file .stagedWal) = some replacement) ∧
      (view.files finalized.reached).image.keeper.active = some target.trimmed ∧
      (view.files finalized.reached).image.later.DurablyEmpty ∧
      (∀ {failed} (reboot : RawWriteRebootEntry state view storage retryNames visible failed first),
        reboot.DurableReset →
        RawOpenRetryTrace.SelectedEntry view state target retryNames visible first →
        (∀ {previous : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
          source.FailedCalls first previous before → List.IsPrefix (previous ++ [(path, cause)]) earlier →
          source.openTable path before = .error cause after → durableKeeperFile before after) →
        raw.CacheFrames seed durableKeeperFile →
        source.fileCalls.ScopeFrames durableKeeperFile →
        source.directoryCalls.ScopeFrames dir durableKeeperFile →
        ((callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue →
          (storage renamedHeap).CrashFileFrame
            (fun path => path = (dir).file (.walSegment layout.keeper.first) ∨
              state.selectedRetryPath path ∧ path ≠ (dir).path) (storage finalIssue)) →
        dispose.ScopeFrames finalized (fun before after =>
          (storage before).CrashFileFrame
            (fun path => path = (dir).file (.walSegment layout.keeper.first) ∨
              state.selectedRetryPath path ∧ path ≠ (dir).path) (storage after)) →
        RawOpenRetryTrace.KeeperCrashChoices dir target (storage finalized.reached) ∧
        ∀ {rebooted} (seen : RawWriteRebootEntry state view storage retryNames visible finalized.reached rebooted),
          (view.files first).image.Valid target → selectedWal first →
          target.pair.manifest = state.writer.target.pair.manifest →
          RawOpenRetryTrace.SelectedEntry view state target retryNames visible rebooted ∧
            TryLockObserves (view.files rebooted).owners dir (.ok true) ∧ (view.descriptors rebooted).slots = [] ∧
            (source.stage.StagingWalNameFrames callbacks state firstOffset through view storage seed.pendingRef →
              ((callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue →
                WalNamePresenceFrame dir firstOffset through (storage renamedHeap) (storage finalIssue)) →
              dispose.ScopeFrames finalized (fun before after =>
                WalNamePresenceFrame dir firstOffset through (storage before) (storage after)) →
              seen.DurableReset →
              RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through rebooted)) := by
  have guard : rejectFlatWalWith dir (optionalMetadataWith (source.calls.lookup ((dir).file .wal)))
      seed.afterPending = .ok () seed.afterPending := by
    simp [← sameStat, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, Pure.pure, EStateM.pure]
  obtain ⟨plan, opened, extent, repairEntry, actual, observed⟩ :=
    (source.worker_observesRepairError_iff dir raw.lock seed.directoryRef seed.activeRef seed.pendingRef _
      guard (sameStat ▸ marked)).mp workerStopped
  obtain ⟨expected, measuredReads, _⟩ := extents.preparesMeasuredWal seals selected valid following accepted ordered
    _ keeperRead
  change source.markedPreparation seed.pendingRef dir seed.afterPending =
    .ok (layout.boundedPlan, expected, reads.wal.keeper.calls.metadata.byteSize.toNat) afterKeeper at measuredReads
  cases measuredReads.symm.trans actual
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have later := (Plan.valid_iff _).mp valid.valid |>.2.2
  have checked := layout.boundedPlan_valid later
  have long := LongKeeperRepair.longerOfObservedRenameError dir layout.boundedPlan _ source.remove stageWrite
    groupSync source.rename checked bytes observed
  obtain ⟨authorized, pruned, recorded, synced, staging, moved, groupFailed⟩ :=
    (LongKeeperRepair.observeRename_error_iff dir layout.boundedPlan _ source.remove stageWrite groupSync source.rename
      checked bytes long).mp observed
  have observedLong : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat := bytes ▸ long
  have startFiles := listing.imageAfterLongKeeper selected seals keeperFiles _ observedLong keeperRead
  have keeperFrame := source.fileCalls.longKeeperReadFrames readerFrames
    (fun h => NativeReadyState.SelectedRetryFrame.refl state (storage h) (visible h))
    (fun first last => first.trans last) _ _ observedLong keeperRead
  have keeperNames := source.fileCalls.longKeeperReadFrames readerNames (fun _ _ => rfl)
    (fun first last start => (last start).trans (first start)) _ _ observedLong keeperRead
  have preparedRoot := listing.invariantAfterLongKeeper selected seals rootAt (by
    intro census cache
    refine ⟨cache.directoryCell.trans (seed.directoryKept.trans seed.directorySet), ?_, ?_, ?_⟩
    · exact congrArg (fun handle => handle.2.1) (cache.directoryHandle.trans (seed.sameHandle.trans seed.openedHandle))
    · rw [census]
      exact List.mem_filter.mpr ⟨reads.listing.custody.cacheRetained, List.all_eq_true.mpr fun event member => by
        rw [(chronology.retained event member).2]; rfl⟩
    · rw [census]
      rfl) readerRoot _ observedLong keeperRead
  have ⟨authorize, prune, written, persisted⟩ := staging
  obtain ⟨throughListing, throughSeals⟩ := listing.framesThroughSeals selected seals retryFrame
    (fun h => NativeReadyState.SelectedRetryFrame.refl state (storage h) (visible h))
    (fun first last => first.trans last) readerFrames listingFrames
  have throughPreparation := throughListing.trans (throughSeals.trans keeperFrame)
  let keeperPath := (dir).file (.walSegment layout.keeper.first)
  obtain ⟨unlinked, unlinks, suffixSync⟩ :=
    returnedWalUnlinksAndBarrier dir layout.boundedPlan source.remove stageWrite groupSync source.rename prune
  have heldRoot : CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
      view seed.directoryRef seed.handle afterKeeper :=
    ⟨preparedRoot.1, preparedRoot.2.1, preparedRoot.2.2.1, rfl⟩
  have rootNamed : retryNames afterKeeper (dir).path = some ((view.descriptors afterKeeper).inode admission.cached.description) :=
    (throughPreparation.parent.visible (dir).path rfl).1.trans (openedRoot.trans (congrArg some preparedRoot.2.2.2.symm))
  have away (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) :
      ¬ state.crashPath ((dir).file (.walSegment ordinal)) :=
    laterWalOutsideRepairScope currentReady
      (targetAtKeeper ▸ Nat.lt_of_le_of_lt layout.target.firstCovered (later ordinal member))
  have writtenPrefix : stageWrite ((dir).file .stagedWal)
      (layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize) pruned = .ok () recorded := by
    rw [layout.boundedPlan_extractKeeper]
    exact written
  obtain ⟨durableFrame, _, syncedRoot, _, stageWalNames, keeperUnchanged, childrenSettled, ⟨prunedNames, prunedSettled⟩,
    stageIssued, file, slot, replacement, ⟨created, acquired, attachedStage, boundStage⟩, stageSynced, stageSlot, separate, stageAtIssue, bytesAtIssue, fileSync, liveAtFileSync, stageNamesFrame, protects⟩ :=
    source.stage.prunedAndSyncedReplacement callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename seed.handle physical
      layout.boundedPlan targetAtKeeper heldRoot rootNamed away unlinkStorage records readsPending readsRoot
      authorize unlinks suffixSync writtenPrefix persisted
  have stageNamed := (congrFun fileSync.names ((dir).file .stagedWal)).trans stageAtIssue
  have bytePrefix : visible stageIssued replacement = layout.target.trimmed := by
    rw [bytesAtIssue, layout.boundedPlan_extractKeeper]
    rfl
  have stagedAtSync : (storage synced).files.bytes replacement = [layout.target.trimmed] := by
    simpa [bytePrefix] using fileSync.bytes replacement
  have inodeMove := renameEffect staging moved stageNamed separate
  have afterStage : rootAt synced :=
    ⟨syncedRoot.1, syncedRoot.2.1, syncedRoot.2.2.1, syncedRoot.2.2.2.trans preparedRoot.2.2.2⟩
  obtain ⟨attached, retained⟩ := renameRoot moved afterStage
  obtain ⟨afterRead, read⟩ := readRef
  have loaded : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some seed.handle) finalIssue := by
    rw [read, attached]
    rfl
  obtain ⟨atIssue, liveRoot, sameInode⟩ := readTarget loaded retained
  obtain ⟨diagnostic, failed, reported⟩ := (callbacks).rawDirectoryErrorAfterRead
    seed.directoryRef seed.activeRef seed.pendingRef loaded groupFailed
  subst publicError
  have stageNames : walNameFrame pruned synced := fun start =>
    congrArg Option.isSome ((stageWalNames start).trans (prunedNames start).symm)
  have renameFrame := inodeMove.framesRetry (state := state) rfl (fun path inside =>
    ⟨state.protectedPathNeWalFromActive currentReady inside (by rw [← targetAtKeeper]; exact Nat.le_refl _),
      state.stagedWalOutsideRetryFootprint path inside⟩)
  obtain ⟨loadFrame, namesOfLoad⟩ := loadFrames loaded
  have emptyPending := listing.invariantAfterLongKeeper selected seals (fun h => view.pending h seed.pendingRef = [])
    (fun _ cache => cache.pendingCell.trans seed.pendingSet) readPendingFrames _ observedLong keeperRead
  have reachedIssue := (protects liveEffects emptyPending).2.fromRepairDirectoryScope.trans (renameFrame.trans loadFrame)
  have throughIssue := throughPreparation.trans reachedIssue
  have rootBinding : retryNames finalIssue (dir).path =
      some ((view.descriptors finalIssue).inode (view.handle finalIssue seed.handle).2.1.description) := by
    rw [atIssue, sameInode]
    exact (throughIssue.parent.visible (dir).path rfl).1.trans openedRoot
  obtain ⟨prunedTrace, prunedImage, syncedImage⟩ := longKeeperSyncPrefix (fun h => (view.files h).image) dir layout.target
    layout.boundedPlan source.remove stageWrite groupSync source.rename authorize prune written persisted
    (fun ordinal member => (startFiles ▸ member : ordinal ∈ (view.files entry).image.later.visible))
    later authorizationImage (pruneImage authorize) unlinkImage writeImage
    (fun wrote fsynced => stageSyncImage fsynced (by rw [writeImage wrote]; rfl))
  have movedImage := renameImage moved (by dsimp only; rw [syncedImage]; rfl)
  have renamedImage : liveImage renamedHeap = { liveImage pruned with keeper :=
      ⟨some layout.target.trimmed, some layout.target.trimmed :: (liveImage pruned).keeper.crashImages, none⟩ } := by
    apply Option.some.inj
    rw [← movedImage]
    dsimp only
    rw [syncedImage]
    rfl
  have ⟨fsyncImage, physicalEffect⟩ := effect failed (atIssue.symm ▸ liveRoot) rootBinding
  have emptyPrune : (liveImage pruned).later.DurablyEmpty := by dsimp only; rw [prunedImage]; exact ⟨rfl, rfl⟩
  have trace : EffectTrace layout.target (liveImage afterKeeper) (liveImage reached) := by
    rw [fsyncImage, loadImage loaded, renamedImage]
    cases effective
    · exact .replace prunedTrace emptyPrune (cut := 3) rfl
    · exact .replace prunedTrace emptyPrune (cut := 4) rfl
  have workerFields : (liveImage reached).keeper.active = some layout.target.trimmed ∧
      (liveImage reached).later.DurablyEmpty := by
    rw [fsyncImage, loadImage loaded, renamedImage]
    dsimp only
    rw [prunedImage]
    cases effective <;> exact ⟨rfl, rfl, rfl⟩
  have atRename : (storage renamedHeap).files.names keeperPath = some replacement := by
    simpa [keeperPath, WalKeeperRenameEffect.rebind] using
      inodeMove.visible keeperPath (.inr ⟨.walSegment layout.keeper.first, rfl⟩)
  have managed : WalKeeperRenameEffect.ManagedPath dir keeperPath := .inr ⟨.walSegment layout.keeper.first, rfl⟩
  obtain ⟨keeperAtIssue, loadedBytes, loadedDurable⟩ := loadKeeper loaded replacement atRename
  have keeperBytes := loadedBytes.trans ((inodeMove.liveBytes keeperPath managed replacement atRename).trans
    (liveAtFileSync.trans bytePrefix))
  have keeperDurable := loadedDurable.trans ((inodeMove.durableBytes _ (.inl rfl) keeperPath managed replacement atRename).trans stagedAtSync)
  have repair : finishBoundedMarkedOpen dir layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      source.remove stageWrite groupSync source.rename afterKeeper =
        .error (IO.userError s!"sync failed for '{(dir).path}': {diagnostic}") reached := by
    rw [← LongKeeperRepair.forget_observeRename, observed]
    rfl
  obtain ⟨children, parentFrame, unchanged⟩ := physicalEffect
  have carried := reachedIssue.trans (children.framesSelectedRetry parentFrame (fun p hp => unchanged p (.inl hp)))
  have named := (children.visible (.walSegment layout.keeper.first)).trans keeperAtIssue
  have durable := (children.bytes _ (.inl rfl) (.walSegment layout.keeper.first) replacement named).trans keeperDurable
  have liveWorker := (unchanged _ (.inr rfl) replacement keeperAtIssue).trans keeperBytes
  have kept : RawOpenRetryTrace.KeeperAt view dir layout.target retryNames visible reached := by
    change (liveImage reached).keeper.active = (retryNames reached _).map (visible reached)
    rw [workerFields.1]
    change some layout.target.trimmed = ((storage reached).files.names ((dir).file (.walSegment layout.keeper.first))).map (visible reached)
    rw [named, Option.map_some, liveWorker]
  have errorNames : walNameFrame synced reached := fun start =>
    (congrArg Option.isSome (children.visible (.walSegment start))).trans
      ((namesOfLoad start).trans (namesOfRename staging moved start))
  have laterBound (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) : target.range.through < ordinal :=
    sameTarget ▸ later ordinal member
  have retainCatalog (atEntry : catalog entry)
      (gone : (view.files finalized.reached).image.later.visible = []) :=
    listing.carriesPrunedCatalog seals selected unlinks dispose finalized readerNames listingNames keeperNames
      (namesOfDirectorySync authorize)
      (fun start => (stageNames start).trans ((namesOfDirectorySync suffixSync) start))
      errorNames namesOfCleanup firstCovered cutoffCovered bounded laterBound
      (fun start beyond => (namesOfDirectorySync authorize start) ▸ listed start beyond) unlinkNames atEntry gone
  dsimp only at trace
  rw [startFiles] at trace
  obtain ⟨returned, selectedEffects, finalImage⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair trace carried (sameTarget ▸ kept) dispose sameDisposal owner
    finalized scope keeperCleanup (fun initial => initial.2.2.1) (by
      intro image finalKeeper finalDurability initial
      have gone : (view.files finalized.reached).image.later.visible = [] := by
        rw [image]
        exact workerFields.2.1
      obtain ⟨nextWindow, nextSuffix, _⟩ := retainCatalog initial.1 gone
      exact ⟨nextWindow, finalKeeper, finalDurability, nextSuffix⟩)
  obtain ⟨sameName, sameBytes⟩ := keeperStorage _ rfl
  have afterCleanup := (keeperCleanup _ (congrArg (fun start => (dir).file (.walSegment start))
    (congrArg Target.first sameTarget))).2 _ named
  have live := (List.cons.inj afterCleanup).1.trans (liveWorker.trans (congrArg Target.trimmed sameTarget))
  have ⟨active, laterEmpty⟩ : (view.files finalized.reached).image.keeper.active = some target.trimmed ∧
      (view.files finalized.reached).image.later.DurablyEmpty := finalImage.symm ▸ sameTarget ▸ workerFields
  refine ⟨returned, selectedEffects, ⟨replacement, sameName.trans named, (sameBytes _ named).trans durable,
    live, authorized, pruned, recorded, synced, created, file, slot, staging, acquired, attachedStage, boundStage⟩,
    active, laterEmpty, ?_⟩
  intro beforeReboot reboot reset atBoot failedKeeper cacheKeeper readKeeper listKeeper
    loadSurvivors cleanupSurvivors
  have liveBeforeRepair : RawOpenRetryTrace.LiveKeeperCrashChoices dir layout.target (storage afterKeeper) :=
    sameTarget.symm ▸ listing.keepsLiveKeeperBeforeRepair prior reboot reset atBoot (sameTarget ▸ targetAtKeeper)
      failedKeeper cacheKeeper readKeeper listKeeper selected seals observedLong keeperRead
  let immutableChild : FilePath → Prop := fun path => state.selectedRetryPath path ∧ path ≠ (dir).path
  let crashScope : FilePath → Prop := fun path => path = keeperPath ∨ immutableChild path
  obtain ⟨old, oldAtEntry, acceptedAtEntry⟩ := liveBeforeRepair
  have keeperInScope : state.crashPath keeperPath :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl
      (congrArg (fun start => (dir).file (.walSegment start)) targetAtKeeper)))
  have oldPayload : ∀ payload ∈ (storage synced).files.bytes old, layout.target.Accepts (some payload) := by
    intro payload present
    exact acceptedAtEntry payload (((durableFrame _ keeperInScope).2 old oldAtEntry) ▸ present)
  have oldNamed := keeperUnchanged.trans oldAtEntry
  have settled : ∀ names ∈ (storage synced).crashNames, names keeperPath = some old :=
    fun names possible => (childrenSettled names possible (.walSegment layout.keeper.first) keeperInScope).trans oldNamed
  have loadedFrame : (storage renamedHeap).CrashFileFrame crashScope (storage finalIssue) := loadSurvivors loaded
  have atIssueSurvivors : RawOpenRetryTrace.KeeperCrashChoices dir layout.target (storage finalIssue) :=
    (inodeMove.acceptsKeeperSurvivors (target := layout.target) settled stagedAtSync oldPayload).frame loadedFrame (.inl rfl)
  have atErrorSurvivors : RawOpenRetryTrace.KeeperCrashChoices dir layout.target (storage reached) :=
    children.acceptsKeeperSurvivors atIssueSurvivors keeperAtIssue keeperDurable
  have afterWorker : (storage reached).CrashFileFrame crashScope (storage finalized.reached) :=
    cleanupSurvivors.afterWorker (fun first last => first.trans last)
  have survivesCleanup : RawOpenRetryTrace.KeeperCrashChoices dir target (storage finalized.reached) :=
    sameTarget ▸ atErrorSurvivors.frame afterWorker (.inl rfl)
  refine ⟨survivesCleanup, ?_⟩
  intro rebooted seen initial priorStorage sameManifest
  have immutableAtStage (names : FilePath → Option Nat) (possible : names ∈ (storage synced).crashNames)
      (path : FilePath) (protectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      names path = retryNames synced path := by
    rcases NativeReadyState.selectedRetryPath_rootOrChild protectedPath with rootPath | ⟨file, rfl⟩
    · exact False.elim (notRoot rootPath)
    exact childrenSettled names possible file (NativeReadyState.crashPath_iff_write.mpr
      (protectedPath.imp id Or.inr))
  have immutableAtRename := inodeMove.keepsSelectedChildren currentReady targetAtKeeper immutableAtStage
  have loadChildren := loadedFrame.toFrames.weaken (scope := immutableChild) (fun _ child => .inr child)
  have immutableAtIssue (names : FilePath → Option Nat) (possible : names ∈ (storage finalIssue).crashNames)
      (path : FilePath) (selectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      names path = retryNames finalIssue path :=
    loadChildren.settledFrom (fun prior possible path child => immutableAtRename prior possible path child.1 child.2)
      names possible path ⟨selectedPath, notRoot⟩
  have immutableAtError := children.keepsSelectedChildren immutableAtIssue
  have cleanupChildren := afterWorker.toFrames.weaken (scope := immutableChild) (fun _ child => .inr child)
  have immutableAtReboot (path : FilePath) (selectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      retryNames rebooted path = retryNames finalized.reached path :=
    cleanupChildren.settledFrom (fun prior possible path child => immutableAtError prior possible path child.1 child.2)
      _ seen.chosen path ⟨selectedPath, notRoot⟩
  have actualDurability := ((selectedEffects.preserves initial).2.2.2 priorStorage).2.2.1
  obtain ⟨nextEntry, vacant, empty⟩ := seen.selectsRetryAfterRepair (sameTarget ▸ targetAtKeeper)
    sameManifest actualDurability immutableAtReboot survivesCleanup
  refine ⟨nextEntry, vacant, empty, ?_⟩
  intro stageCatalog loadCatalog cleanupCatalog reset
  have atEntry := ((before.preserves initial).2.2.2 priorStorage).1
  have atPrune := settlesPrunedWindow (retainCatalog atEntry laterEmpty.1).2.2 prunedNames prunedSettled
  have throughStage := stageNamesFrame stageCatalog
  have throughRename := throughStage.trans (inodeMove.walNames oldNamed settled firstOffset through)
  have throughError := (throughRename.trans (loadCatalog loaded)).trans (WalNamePresenceFrame.ofRootSync children)
  have throughCleanup := throughError.trans (cleanupCatalog.afterWorker (fun earlier later => earlier.trans later))
  have window := (throughCleanup.preservesNamespaceWindow atPrune).2 _ seen.chosen
  exact seen.startsRecoveryObservations reset nextEntry window

end FinalDirectorySync

/-- The actual failed replacement rename, including a reported move
before EIO, enters the shared failed-call fold with the original
selected catalog, the observed keeper, and the reached cleanup heap.
The crash candidates at that heap can still name the old keeper.
The reboot can use the same bounded catalog as the final fsync
failure, since either rename outcome preserves WAL name presence. -/
theorem MarkedWalExtentReports.extendsLongRenameError
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFiles : source.fileCalls.ScopeFrames (fun before after => liveImage after = liveImage before))
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {authorized pruned recorded synced : heap} {cause : IO.Error} {effective : Bool} {old : Nat}
    (longer : layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (authorize : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (written : stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded)
    (persisted : groupSync #[((dir).file .stagedWal)] recorded = .ok () synced)
    (later : ∀ ordinal ∈ layout.boundedPlan.newer, target.range.through < ordinal)
    (covers : ∀ ordinal ∈ (view.files afterKeeper).image.later.visible, ordinal ∈ layout.boundedPlan.newer)
    (authorizationImage : groupSync #[(dir).path] afterKeeper = .ok () authorized →
      (view.files authorized).image = (view.files afterKeeper).image.syncDirectory)
    (pruneImage : ∀ {unlinked}, ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () unlinked →
      groupSync #[(dir).path] unlinked = .ok () pruned →
      (view.files pruned).image = (view.files unlinked).image.syncDirectory)
    (unlinkImage : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (view.files after).image = (view.files before).image.unlinkLater ordinal)
    (writeStage : (view.files recorded).image = (view.files pruned).image.withScratch (some (target.trimmed, false)))
    (syncStage : (view.files synced).image = (view.files recorded).image.withScratch (some (target.trimmed, true)))
    (currentReady : state.Valid) (targetAtKeeper : target.first = state.writer.wal.active.first)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (physical : source.stage.ReplacementPrefixStorageEffects callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.pendingRef seed.handle)
    (root : CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
      view seed.directoryRef seed.handle afterKeeper)
    (rootNamed : retryNames afterKeeper (dir).path = some ((view.descriptors afterKeeper).inode admission.cached.description))
    (oldNamed : retryNames afterKeeper ((dir).file (.walSegment target.first)) = some old)
    (unlinkStorage : ∀ {ordinal before after result}, ¬ state.crashPath ((dir).file (.walSegment ordinal)) →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (storage before).Frames state.crashPath (storage after) ∧
      (CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
        view seed.directoryRef seed.handle before →
        CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
          view seed.directoryRef seed.handle after))
    (records : ∀ {file before after},
      (callbacks).modifyPending seed.pendingRef (pushPending ((dir).file .stagedWal) file) before = .ok () after →
      view.pending after seed.pendingRef = pushPending ((dir).file .stagedWal) file (view.pending before seed.pendingRef))
    (readsPending : ∀ {before entries loaded}, (callbacks).getPending seed.pendingRef before = .ok entries loaded →
      entries = view.pending before seed.pendingRef)
    (readsRoot : ∀ {before result issued}, (callbacks).getDirectory seed.directoryRef before = .ok result issued →
      result = view.directory before seed.directoryRef)
    (readPendingFrames : source.fileCalls.ScopeFrames
      (fun before after => view.pending before seed.pendingRef = [] → view.pending after seed.pendingRef = []))
    (liveEffects : source.stage.ReplacementPrefixLiveEffects callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible
      seed.directoryRef seed.pendingRef seed.handle source.remove)
    (keeper : RawOpenRetryTrace.KeeperAt view (dir) target retryNames visible afterKeeper)
    (failed : source.rename ((dir).file .stagedWal)
      ((dir).file (.walSegment target.first)) synced = .error cause reached)
    (observation : ∀ {replacement}, source.rename ((dir).file .stagedWal)
      ((dir).file (.walSegment target.first)) synced = .error cause reached →
      retryNames synced ((dir).file .stagedWal) = some replacement →
      retryNames synced ((dir).file (.walSegment target.first)) = some old →
      replacement ≠ old →
      WalKeeperRenameEffect state.session.directory target.first replacement effective
        (storage synced) (storage reached) (visible synced) (visible reached) ∧
      (if effective then (view.files synced).image.effect target (.replace .renameStaged)
        else some (view.files synced).image) = some (view.files reached).image)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (keeperNames : walNameFrame beforeKeeper afterKeeper)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (listed : ∀ start, target.range.through < start →
      ((retryNames authorized ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start))) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) ∧
      (∀ {failed} (reboot : RawWriteRebootEntry state view storage retryNames visible failed first),
        reboot.DurableReset →
        RawOpenRetryTrace.SelectedEntry view state target retryNames visible first →
        (∀ {previous : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
          source.FailedCalls first previous before → List.IsPrefix (previous ++ [(path, cause)]) earlier →
          source.openTable path before = .error cause after → durableKeeperFile before after) →
        raw.CacheFrames seed durableKeeperFile →
        source.fileCalls.ScopeFrames durableKeeperFile →
        source.directoryCalls.ScopeFrames dir durableKeeperFile →
        dispose.ScopeFrames finalized (fun before after =>
          (storage before).CrashFileFrame
            (fun path => path = (dir).file (.walSegment target.first) ∨
              state.selectedRetryPath path ∧ path ≠ (dir).path) (storage after)) →
        RawOpenRetryTrace.KeeperCrashChoices dir target (storage finalized.reached) ∧
        (∀ names ∈ (storage finalized.reached).crashNames, ∀ path, state.selectedRetryPath path → path ≠ (dir).path →
          names path = retryNames finalized.reached path) ∧
        ∀ {rebooted} (seen : RawWriteRebootEntry state view storage retryNames visible finalized.reached rebooted),
          (view.files first).image.Valid target → selectedWal first →
          target.pair.manifest = state.writer.target.pair.manifest →
          RawOpenRetryTrace.SelectedEntry view state target retryNames visible rebooted ∧
            TryLockObserves (view.files rebooted).owners dir (.ok true) ∧ (view.descriptors rebooted).slots = [] ∧
            (source.stage.StagingWalNameFrames callbacks state firstOffset through view storage seed.pendingRef →
              dispose.ScopeFrames finalized (fun before after =>
                WalNamePresenceFrame dir firstOffset through (storage before) (storage after)) →
              seen.DurableReset →
              RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through rebooted)) := by
  have path : layout.boundedPlan.keeper = target.first := congrArg Target.first sameTarget
  have payload : layout.keeper.bytes = target.trimmed := congrArg Target.trimmed sameTarget
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have checked : layout.boundedPlan.valid = true :=
    layout.boundedPlan_valid fun ordinal member =>
      show layout.target.range.through < ordinal from sameTarget.symm ▸ later ordinal member
  have actualWrite : stageWrite ((dir).file .stagedWal) target.trimmed pruned = .ok () recorded := payload ▸ written
  obtain ⟨prunedTrace, prunedImage, syncedImage⟩ :=
    longKeeperSyncPrefix (fun atHeap => (view.files atHeap).image) dir target layout.boundedPlan
      source.remove stageWrite groupSync source.rename authorize prune actualWrite persisted covers later
      authorizationImage pruneImage unlinkImage (fun _ => writeStage) (fun _ _ => syncStage)
  have prunedEmpty : (liveImage pruned).later.DurablyEmpty := by
    dsimp only
    rw [prunedImage]
    exact ⟨rfl, rfl⟩
  have keeperActive : (liveImage synced).keeper.active = (liveImage afterKeeper).keeper.active := by
    dsimp only
    rw [syncedImage, prunedImage]
    rfl
  obtain ⟨unlinked, unlinks, suffixSync⟩ :=
    returnedWalUnlinksAndBarrier dir layout.boundedPlan source.remove stageWrite groupSync source.rename prune
  have away (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) :
      ¬ state.crashPath ((dir).file (.walSegment ordinal)) := by
    exact laterWalOutsideRepairScope currentReady
      (targetAtKeeper ▸ Nat.lt_of_le_of_lt target.firstCovered (later ordinal member))
  have writtenPrefix : stageWrite ((dir).file .stagedWal)
      (layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize) pruned = .ok () recorded := by
    rw [layout.boundedPlan_extractKeeper]
    exact written
  obtain ⟨durableFrame, _, _, authorizedScope, stageScope, oldAtRename, childrenSettled,
    ⟨prunedNames, prunedSettled⟩, issued, file, slot, replacement, _, _, _, separate, stageAtIssue, bytesAtIssue, fileSync, liveAtSync, stageNamesFrame, protects⟩ :=
    source.stage.prunedAndSyncedReplacement callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename seed.handle physical
      layout.boundedPlan (path.trans targetAtKeeper) root rootNamed
      away unlinkStorage records readsPending readsRoot
      authorize unlinks suffixSync writtenPrefix persisted
  have renamedOld : retryNames synced ((dir).file (.walSegment target.first)) = some old := by
    simpa only [NativeReadyState.repairDirectoryScope, path] using oldAtRename.trans
      (show retryNames afterKeeper ((dir).file (.walSegment layout.boundedPlan.keeper)) = some old from path.symm ▸ oldNamed)
  have apart : replacement ≠ old := fun same => separate (path.symm ▸ same.symm ▸ renamedOld)
  have keeperPath : state.crashPath ((dir).file (.walSegment target.first)) :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl
      (congrArg (fun start => (dir).file (.walSegment start)) targetAtKeeper)))
  have oldChoices : ∀ names ∈ (storage synced).crashNames, names ((dir).file (.walSegment target.first)) = some old := by
    intro names possible
    exact (childrenSettled names possible (.walSegment target.first) keeperPath).trans renamedOld
  have stagedNamed := (congrFun fileSync.names ((dir).file .stagedWal)).trans stageAtIssue
  have atIssueBytes : visible issued replacement = target.trimmed := by
    rw [bytesAtIssue, layout.boundedPlan_extractKeeper]
    exact payload
  have stagedLive := liveAtSync.trans atIssueBytes
  have stagedDurable : (storage synced).files.bytes replacement = [target.trimmed] := by
    simpa [atIssueBytes] using fileSync.bytes replacement
  have observedLong : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat := by
    change layout.boundedPlan.keeperBytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [size]
    exact longer
  have startFiles := listing.imageAfterLongKeeper selected seals keeperFiles _ observedLong keeperRead
  have emptyPending := listing.invariantAfterLongKeeper selected seals (fun h => view.pending h seed.pendingRef = [])
    (fun _ cache => cache.pendingCell.trans seed.pendingSet) readPendingFrames _ observedLong keeperRead
  obtain ⟨live, toRename⟩ := protects liveEffects emptyPending
  have sameOld : visible synced old = visible afterKeeper old :=
    (List.cons.inj ((live _ keeperPath).2 old oldNamed)).1
  have atRename : RawOpenRetryTrace.KeeperAt view dir target retryNames visible synced := by
    unfold RawOpenRetryTrace.KeeperAt at keeper ⊢
    rw [keeperActive, keeper, renamedOld, oldNamed]
    exact congrArg some sameOld.symm
  have safe (path : FilePath) (selectedPath : state.selectedRetryPath path) :
      path ≠ (dir).file (.walSegment target.first) ∧ path ≠ (dir).file .stagedWal := by
    refine ⟨?_, state.stagedWalOutsideRetryFootprint path selectedPath⟩
    rw [targetAtKeeper]
    exact state.protectedPathNeWalFromActive currentReady selectedPath (Nat.le_refl _)
  obtain ⟨repair, trace, framed, liveKeeper, _, renameNames, _, _, laterGone⟩ :=
    failedLongKeeperRename view state target layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      storage visible source.remove stageWrite groupSync source.rename checked size longer path payload authorize
      prune actualWrite persisted prunedTrace prunedEmpty syncedImage toRename.fromRepairDirectoryScope safe renamedOld oldChoices stagedNamed
      apart stagedLive stagedDurable atRename failed observation
  rw [startFiles] at trace
  have errorNames : walNameFrame synced reached := fun start => (renameNames start start).live start (Nat.le_refl _) (Nat.le_refl _)
  have retainCatalog (atEntry : catalog entry)
      (gone : (view.files finalized.reached).image.later.visible = []) :=
    listing.carriesPrunedCatalog seals selected unlinks dispose finalized readerNames listingNames keeperNames
      (fun start => congrArg Option.isSome (authorizedScope start))
      (fun start => congrArg Option.isSome (stageScope start))
      errorNames namesOfCleanup firstCovered cutoffCovered bounded later listed unlinkNames atEntry gone
  obtain ⟨returned, effects, finalImage⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair (sameTarget.symm ▸ trace) framed liveKeeper dispose
    sameDisposal owner finalized scope keeperCleanup (fun initial => initial.2.2.1) (by
      intro image finalKeeper finalDurability initial
      have gone : (view.files finalized.reached).image.later.visible = [] := image.symm ▸ laterGone.1
      obtain ⟨nextWindow, nextSuffix, _⟩ := retainCatalog initial.1 gone
      exact ⟨nextWindow, finalKeeper, finalDurability, nextSuffix⟩)
  refine ⟨returned, effects, ?_⟩
  intro beforeReboot reboot reset atBoot failedKeeper cacheKeeper readKeeper listKeeper cleanupSurvivors
  have acceptedBefore := listing.keepsLiveKeeperBeforeRepair prior reboot reset atBoot targetAtKeeper
    failedKeeper cacheKeeper readKeeper listKeeper selected seals observedLong keeperRead
  obtain ⟨inode, named, acceptedReady⟩ := acceptedBefore.frame durableFrame keeperPath
  have sameInode : inode = old := Option.some.inj (named.symm.trans renamedOld)
  subst inode
  have renamedEffect := (observation failed stagedNamed renamedOld apart).1
  have atError := renamedEffect.acceptsKeeperSurvivors oldChoices stagedDurable acceptedReady
  have cleanup := cleanupSurvivors.afterWorker (fun earlier later => earlier.trans later)
  have keeperAfterCleanup := atError.frame cleanup (.inl rfl)
  have immutableAtStage (names : FilePath → Option Nat) (possible : names ∈ (storage synced).crashNames)
      (path : FilePath) (protectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      names path = retryNames synced path := by
    rcases NativeReadyState.selectedRetryPath_rootOrChild protectedPath with rootPath | ⟨file, rfl⟩
    · exact False.elim (notRoot rootPath)
    exact childrenSettled names possible file (NativeReadyState.crashPath_iff_write.mpr
      (protectedPath.imp id Or.inr))
  have immutableAtError := renamedEffect.keepsSelectedChildren currentReady targetAtKeeper immutableAtStage
  let immutableChild : FilePath → Prop := fun path => state.selectedRetryPath path ∧ path ≠ (dir).path
  have cleanupChildren := cleanup.toFrames.weaken (scope := immutableChild) (fun _ child => .inr child)
  have immutableAfterCleanup (names : FilePath → Option Nat) (survives : names ∈ (storage finalized.reached).crashNames)
      (path : FilePath) (selectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      names path = retryNames finalized.reached path :=
    cleanupChildren.settledFrom (fun prior possible path child => immutableAtError prior possible path child.1 child.2)
      names survives path ⟨selectedPath, notRoot⟩
  refine ⟨keeperAfterCleanup, immutableAfterCleanup, ?_⟩
  intro rebooted seen initial priorStorage sameManifest
  have durableAtEnd := ((effects.preserves initial).2.2.2 priorStorage).2.2.1
  obtain ⟨nextEntry, vacant, empty⟩ := seen.selectsRetryAfterRepair targetAtKeeper sameManifest durableAtEnd
    (immutableAfterCleanup _ seen.chosen) keeperAfterCleanup
  refine ⟨nextEntry, vacant, empty, ?_⟩
  intro stageCatalog cleanupCatalog reset
  have atEntry := ((before.preserves initial).2.2.2 priorStorage).1
  have gone : (view.files finalized.reached).image.later.visible = [] := finalImage.symm ▸ laterGone.1
  have atPrune := settlesPrunedWindow (retainCatalog atEntry gone).2.2 prunedNames prunedSettled
  have throughStage := stageNamesFrame stageCatalog
  have throughError := throughStage.trans (renameNames firstOffset through)
  have throughCleanup := throughError.trans (cleanupCatalog.afterWorker (fun earlier later => earlier.trans later))
  have window := (throughCleanup.preservesNamespaceWindow atPrune).2 _ seen.chosen
  exact seen.startsRecoveryObservations reset nextEntry window

end SelectedRetry

end Alvoki.Storage.DiskSession
