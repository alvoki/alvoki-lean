import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperFinalSyncError
import Alvoki.Storage.Disk.NativeLongKeeperRenameError
import Alvoki.Storage.Disk.NativeLongKeeperStorage
import Alvoki.Storage.Disk.NativeLongKeeperPending
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeMarkedFirstUnlinkError
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail

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
    (parent : entry.Frames (· = state.session.directory.path) reached) (live : after = before) :
    state.SelectedRetryFrame entry reached before after := by
  have durable := effect.framesScopedFiles parent (scope := state.selectedRetryPath)
    (fun _ => NativeReadyState.selectedRetryPath_rootOrChild)
  exact ⟨fun path held => ⟨(durable path held).1, by rw [live]; intros; rfl⟩, durable, parent⟩

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

private theorem AlignedKeeperCacheCallbacks.rawPruneDirectoryError
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error}
    (loaded : calls.getDirectory cached before = .ok (some handle) issued)
    (returned : calls.syncPaths directory.path cached active pending #[directory.path] before = .error cause reached) :
    ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
      cause = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" := by
  rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single] at returned
  cases raw : calls.sync handle issued with
  | ok value after =>
    cases value
    simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, raw, Pure.pure, EStateM.pure] at returned
  | error diagnostic after =>
    simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, raw, Pure.pure, EStateM.pure] at returned
    obtain ⟨sameCause, rfl⟩ := returned
    exact ⟨diagnostic, rfl, sameCause.symm⟩

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
  obtain ⟨diagnostic, failed, reported⟩ := calls.rawPruneDirectoryError cached active pending loaded returned
  obtain ⟨children, parent, live⟩ := observation diagnostic failed target.live bound
  have durable := children.framesScopedFiles parent managed
  have atSync : SampledCheckpointRetryFrame directory scope through storage visible issued reached :=
    ⟨fun path selected => ⟨(durable path selected).1, fun inode named => congrArg (fun bytes => [bytes])
      (live path selected inode named)⟩,
      fun start _ => congrArg Option.isSome (children.visible (.walSegment start)), durable, parent⟩
  exact ⟨diagnostic, failed, reported, loadFrame.trans atSync, children⟩

end PruneDirectorySync

section DirectorySync

variable {heap : Type} {directory : DiskDirectory} {initial : LockedFileState FileImage}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout initial.image history}
  {operations : MarkedRetryChunkOperations
    (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {held : HeldDirectoryMarkedRetryReports operations published}
  {authorized : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorized}
  {stage : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename stage}

/-- The issued final sync connects the exact bounded repair error to
its reached storage frame and live keeper. Only the observed path from
authorization to this issued descriptor needs physical frames. An
effective sync settles the reached keeper inode in every crash map. -/
theorem ListedLongKeeperDirectoryIssue.returnsSelectedRepairError
    (issue : ListedLongKeeperDirectoryIssue renamed) (view : OpenCloseHeapView heap FileImage)
    (state : NativeReadyState) (sameDirectory : state.session.directory = directory)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (callbacks : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (stageCalls : LongKeeperStageCallbacks heap) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {effective : Bool} {physical : Nat}
    {start authorizedHeap pruned recorded synced renamedHeap issued reached : heap}
    {handle : IO.FS.Handle} {cause : IO.Error}
    (startFiles : (view.files start).image = initial.image)
    (measured : physical = authorized.keeper.metadata.byteSize.toNat)
    (authorize : callbacks.syncPaths directory.path cached active pending #[directory.path] start = .ok () authorizedHeap)
    (prune : let write := stageCalls.stage pending callbacks.modifyPending
      let sync := callbacks.syncPaths directory.path cached active pending
      ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
        (performPaths directory layout.boundedPlan remove throw write sync rename)) authorizedHeap = .ok () pruned)
    (written : stageCalls.stage pending callbacks.modifyPending (directory.file .stagedWal) layout.keeper.bytes pruned =
      .ok () recorded)
    (persisted : callbacks.syncPaths directory.path cached active pending #[directory.file .stagedWal] recorded = .ok () synced)
    (moved : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      synced = .ok () renamedHeap)
    (loaded : callbacks.getDirectory cached renamedHeap = .ok (some handle) issued)
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (issuedFiles : view.files issued = issue.files)
    (root : (storage issued).files.names directory.path = issue.bindings directory.path)
    (keeper : (storage issued).files.names (directory.file (.walSegment layout.keeper.first)) =
      issue.bindings (directory.file (.walSegment layout.keeper.first)))
    (scratch : (storage issued).files.names (directory.file .stagedWal) = issue.bindings (directory.file .stagedWal))
    (keeperBytes : visible issued (stage.inventory.inode stage.slot.description) = layout.target.trimmed)
    (keeperDurable : (storage issued).files.bytes (stage.inventory.inode stage.slot.description) = [layout.target.trimmed])
    (prefixFrame : state.SelectedRetryFrame (storage start) (storage issued) (visible start) (visible issued))
    (failed : callbacks.sync handle issued = .error cause reached)
    (effect : callbacks.sync handle issued = .error cause reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      view.files issued = issue.files →
      view.files reached = issue.stopped effective ∧
      WalRootSyncEffect directory effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = directory.path) (storage reached) ∧ visible reached = visible issued) :
    let write := stageCalls.stage pending callbacks.modifyPending
    let sync := callbacks.syncPaths directory.path cached active pending
    finishBoundedMarkedOpen directory layout.boundedPlan physical remove write sync rename start =
      .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached ∧
    (view.files reached).image = (issue.stopped effective).image ∧
    EffectTrace layout.target (view.files start).image (view.files reached).image ∧
    state.SelectedRetryFrame (storage start) (storage reached) (visible start) (visible reached) ∧
    RawOpenRetryTrace.KeeperAt view directory layout.target (fun atHeap => (storage atHeap).files.names) visible reached ∧
    (storage reached).files.names (directory.file (.walSegment layout.keeper.first)) =
      some (stage.inventory.inode stage.slot.description) ∧
    (storage reached).files.bytes (stage.inventory.inode stage.slot.description) = [layout.target.trimmed] ∧
    (effective = true → ∀ names ∈ (storage reached).crashNames,
      names (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description)) := by
  intro write sync
  let names atHeap := (storage atHeap).files.names
  obtain ⟨live, bound⟩ := issue.rawDirectoryTarget view names atIssue census root
  obtain ⟨files, children, parent, unchanged⟩ := effect failed live bound issuedFiles
  obtain ⟨returned, _, trace, activeKeeper, _, _, _, _, named, _⟩ :=
    issue.rawFinalSyncError callbacks cached active pending remove stageCalls rename view names startFiles measured
      authorize prune written persisted moved loaded atIssue census issuedFiles root keeper scratch failed
      (fun _ _ _ _ => files) children.visible
  have childScope : WalRootSyncEffect state.session.directory effective (storage issued) (storage reached) :=
    sameDirectory.symm ▸ children
  have parentScope : (storage issued).Frames (· = state.session.directory.path) (storage reached) := by
    rw [sameDirectory]
    exact parent
  have durable := (children.bytes (storage reached).files.names (.inl rfl)
    (.walSegment layout.keeper.first) (stage.inventory.inode stage.slot.description) named).trans keeperDurable
  refine ⟨returned, congrArg LockedFileState.image files, trace,
    prefixFrame.trans (childScope.framesSelectedRetry parentScope unchanged), ?_, named, durable, ?_⟩
  · unfold RawOpenRetryTrace.KeeperAt
    change (view.files reached).image.keeper.active =
      (names reached (directory.file (.walSegment layout.keeper.first))).map (visible reached)
    rw [activeKeeper, named, Option.map_some, unchanged, keeperBytes]
  · intro applied names survives
    exact (children.settled applied names survives (.walSegment layout.keeper.first)).trans named

end DirectorySync

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
    EffectTrace target (files entry) (files pruned) ∧ (files pruned).later.DurablyEmpty ∧
      files synced = (files pruned).withScratch (some (target.trimmed, true)) ∧
      (files synced).keeper.active = (files entry).keeper.active := by
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
  refine ⟨prunedTrace, ?_, stageImage, ?_⟩
  · rw [prunedImage, unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ allLater]
    exact ⟨rfl, rfl⟩
  · rw [stageImage, prunedImage, unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ allLater, authorizedImage]
    rfl

end ReplacementPrefix

/-- During repair, the directory slot belongs to the census of the
actual open attempt. -/
abbrev NativeReadyState.repairDirectoryScope (state : NativeReadyState) (current : DescriptorInventory)
    (cached : DescriptorSlot) : NativeReadyState :=
  { state with census := current, directorySlot := cached }

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
local notation "selectedWal" => fun atHeap => catalog atHeap ∧
  RawOpenRetryTrace.KeeperAt view dir target retryNames visible atHeap ∧
  state.SelectedRetryDurability target (storage atHeap) ∧
    RawOpenRetryTrace.LaterWalAt view dir target retryNames atHeap
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
  have keeperAt : RawOpenRetryTrace.KeeperAt view dir target retryNames visible finalized.reached := by
    unfold RawOpenRetryTrace.KeeperAt at keeperAtError ⊢
    rw [image, keeperAtError]
    exact (keeperCleanup.visiblePayload (names := retryNames) (bytes := visible) rfl).symm
  have trace : EffectTrace target (view.files entry).image (view.files finalized.reached).image := by
    rw [image, ← sameTarget]
    exact effects
  exact ⟨returned, .append (calls := .next .empty input returned) before (.inr trace) kept.live
    (fun selected => carries image keeperAt ((durability selected).frame kept.durable kept.parent) selected), image⟩

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "stageWrite" => LongKeeperStageCallbacks.stage source.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks (DiskDirectory.path dir) seed.directoryRef seed.activeRef seed.pendingRef

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

set_option maxHeartbeats 1200000 in
/-- Feed the actual repair stopped by the final directory fsync into
the same fixed opener's cleanup and failed-call prefix. With the
protected child frame, any later sampled reboot re-enters that same
target, whether it names the old keeper or the trimmed replacement.
The scoped catalog frames preserve presence and absence through that
same sample, starting at the returned post-prune root barrier. -/
theorem MarkedWalExtentReports.extendsFinalSyncError
    {operations : MarkedRetryChunkOperations
      (SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot × Nat)) dir layout}
    {held : HeldDirectoryMarkedRetryReports operations published}
    {authorization : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorization}
    {staged : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename staged}
    (issue : ListedLongKeeperDirectoryIssue renamed)
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
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {authorized pruned recorded synced renamedHeap issued : heap}
    {handle : IO.FS.Handle} {cause : IO.Error} {effective : Bool}
    (startFiles : (view.files afterKeeper).image = (view.files entry).image)
    (measured : reads.wal.keeper.calls.metadata.byteSize.toNat = authorization.keeper.metadata.byteSize.toNat)
    (authorize : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (written : stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded)
    (persisted : groupSync #[((dir).file .stagedWal)] recorded = .ok () synced)
    (moved : source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      synced = .ok () renamedHeap)
    (loaded : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some handle) issued)
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (issuedFiles : view.files issued = issue.files)
    (root : retryNames issued (dir).path = issue.bindings (dir).path)
    (keeper : retryNames issued ((dir).file (.walSegment layout.keeper.first)) =
      issue.bindings ((dir).file (.walSegment layout.keeper.first)))
    (scratch : retryNames issued ((dir).file .stagedWal) = issue.bindings ((dir).file .stagedWal))
    (keeperBytes : visible issued (staged.inventory.inode staged.slot.description) = layout.target.trimmed)
    (keeperDurable : (storage issued).files.bytes (staged.inventory.inode staged.slot.description) = [layout.target.trimmed])
    (authorizedFrame : retryFrame afterKeeper authorized)
    (currentReady : state.Valid) (targetAtKeeper : layout.target.first = state.writer.wal.active.first)
    (unlinkFrame : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (liveFiles before).Frames (· ≠ (dir).file (.walSegment ordinal)) (liveFiles after) ∧
      (storage before).files.Frames (· ≠ (dir).file (.walSegment ordinal)) (storage after).files ∧
      (storage before).Frames (· = (dir).path) (storage after))
    (suffixSyncFrame : ∀ {before after}, groupSync #[(dir).path] before = .ok () after → retryFrame before after)
    (stageFrame : retryFrame pruned synced) (renameFrame : retryFrame synced renamedHeap)
    (loadFrame : retryFrame renamedHeap issued)
    (failed : (callbacks).sync handle issued = .error cause reached)
    (effect : (callbacks).sync handle issued = .error cause reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      retryNames issued (dir).path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      view.files issued = issue.files →
      view.files reached = issue.stopped effective ∧
      WalRootSyncEffect dir effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = (dir).path) (storage reached) ∧ visible reached = visible issued)
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
    (namesOfDirectorySync : ∀ {before after}, groupSync #[(dir).path] before = .ok () after → walNameFrame before after)
    (namesOfStageWrite : walNameFrame pruned recorded)
    (namesOfStageSync : walNameFrame recorded synced)
    (namesOfRename : walNameFrame synced renamedHeap)
    (namesOfLoad : walNameFrame renamedHeap issued)
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
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start)))
    (keeperStorage : (storage reached).files.Frames (· = (dir).file (.walSegment layout.keeper.first))
      (storage finalized.reached).files) :
    ∃ returned : source.openTable input entry =
        .error (dispose.diagnostic (IO.userError s!"sync failed for '{(dir).path}': {cause}")) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) ∧
      retryNames finalized.reached ((dir).file (.walSegment layout.keeper.first)) =
        some (staged.inventory.inode staged.slot.description) ∧
      (storage finalized.reached).files.bytes (staged.inventory.inode staged.slot.description) = [layout.target.trimmed] ∧
      visible finalized.reached (staged.inventory.inode staged.slot.description) = target.trimmed ∧
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
        ∀ (buffered : heap → IO.FS.Handle → ByteArray),
        source.stage.ReplacementPrefixStorageEffects callbacks
          (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
          seed.directoryRef seed.pendingRef seed.handle →
        CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
          view seed.directoryRef seed.handle afterKeeper →
        retryNames afterKeeper (dir).path = some ((view.descriptors afterKeeper).inode admission.cached.description) →
        (∀ {ordinal before after result}, ¬ state.crashPath ((dir).file (.walSegment ordinal)) →
          source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
          RunCollection.ownedUnlinkResult result = .ok () →
          (storage before).Frames state.crashPath (storage after) ∧
          (CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
            view seed.directoryRef seed.handle before →
            CachedKeeperReplacementRoot (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached)
              view seed.directoryRef seed.handle after)) →
        (∀ {file before after},
          (callbacks).modifyPending seed.pendingRef (pushPending ((dir).file .stagedWal) file) before = .ok () after →
          view.pending after seed.pendingRef = pushPending ((dir).file .stagedWal) file (view.pending before seed.pendingRef)) →
        (∀ {before entries loaded}, (callbacks).getPending seed.pendingRef before = .ok entries loaded →
          entries = view.pending before seed.pendingRef) →
        (∀ {before result issued}, (callbacks).getDirectory seed.directoryRef before = .ok result issued →
          result = view.directory before seed.directoryRef) →
        (∀ {replacement old}, source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
          synced = .ok () renamedHeap →
          retryNames synced ((dir).file .stagedWal) = some replacement →
          retryNames synced ((dir).file (.walSegment layout.keeper.first)) = some old →
          replacement ≠ old →
          WalKeeperRenameEffect dir layout.keeper.first replacement true
            (storage synced) (storage renamedHeap) (visible synced) (visible renamedHeap)) →
        ((callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some handle) issued →
          (storage renamedHeap).CrashFileFrame
            (fun path => path = (dir).file (.walSegment layout.keeper.first) ∨
              state.selectedRetryPath path ∧ path ≠ (dir).path) (storage issued)) →
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
            ((stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded →
                WalNamePresenceFrame dir firstOffset through (storage pruned) (storage recorded)) →
              (groupSync #[((dir).file .stagedWal)] recorded = .ok () synced →
                WalNamePresenceFrame dir firstOffset through (storage recorded) (storage synced)) →
              ((callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some handle) issued →
                WalNamePresenceFrame dir firstOffset through (storage renamedHeap) (storage issued)) →
              dispose.ScopeFrames finalized (fun before after =>
                WalNamePresenceFrame dir firstOffset through (storage before) (storage after)) →
              seen.DurableReset →
              RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset through rebooted)) := by
  have prunedFrame := framesReturnedPrune dir layout.boundedPlan source.remove stageWrite groupSync source.rename
    retryFrame (fun atHeap => NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap))
    (fun first last => first.trans last) (unlink := by
      intro ordinal before after result member removed accepted
      obtain ⟨live, durable, parent⟩ := unlinkFrame member removed accepted
      have afterTarget : layout.range.through < ordinal := pruning.later ordinal member
      have covers : state.writer.wal.active.first ≤ layout.range.through :=
        targetAtKeeper ▸ layout.target.firstCovered
      have separate (path : FilePath) (inside : state.selectedRetryPath path) :
          path ≠ (dir).file (.walSegment ordinal) :=
        state.protectedPathNeWalFromActive currentReady inside (Nat.le_trans covers (Nat.le_of_lt afterTarget))
      exact ⟨fun path inside => live path (separate path inside),
        fun path inside => durable path (separate path inside), parent⟩)
    suffixSyncFrame prune
  have reachedIssue := authorizedFrame.trans (prunedFrame.trans (stageFrame.trans (renameFrame.trans loadFrame)))
  obtain ⟨repair, workerImage, trace, carried, kept, named, durable, _⟩ :=
    issue.returnsSelectedRepairError view state rfl storage visible callbacks seed.directoryRef seed.activeRef seed.pendingRef
      source.remove source.stage source.rename startFiles measured authorize prune written persisted moved loaded atIssue
      census issuedFiles root keeper scratch keeperBytes keeperDurable reachedIssue failed effect
  obtain ⟨liveRoot, rootBinding⟩ := issue.rawDirectoryTarget view retryNames atIssue census root
  have errorEffect := effect failed liveRoot rootBinding issuedFiles
  have errorNames : walNameFrame synced reached := fun start =>
    (congrArg Option.isSome (errorEffect.2.1.visible (.walSegment start))).trans
      ((namesOfLoad start).trans (namesOfRename start))
  have laterBound (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) : target.range.through < ordinal :=
    sameTarget ▸ pruning.later ordinal member
  obtain ⟨unlinked, unlinks, suffixSync⟩ :=
    returnedWalUnlinksAndBarrier dir layout.boundedPlan source.remove stageWrite groupSync source.rename prune
  have retainCatalog (atEntry : catalog entry)
      (gone : (view.files finalized.reached).image.later.visible = []) :=
    listing.carriesPrunedCatalog seals selected unlinks dispose finalized readerNames listingNames keeperNames
      (namesOfDirectorySync authorize)
      (fun start =>
        (namesOfStageSync start).trans ((namesOfStageWrite start).trans ((namesOfDirectorySync suffixSync) start)))
      errorNames namesOfCleanup firstCovered cutoffCovered bounded laterBound listed unlinkNames atEntry gone
  rw [startFiles] at trace
  obtain ⟨returned, selectedEffects, finalImage⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair trace carried (sameTarget ▸ kept) dispose sameDisposal owner
    finalized scope keeperCleanup (fun initial => initial.2.2.1) (by
      intro image finalKeeper finalDurability initial
      have gone : (view.files finalized.reached).image.later.visible = [] := by
        rw [image, workerImage]
        exact (issue.visibleAfterRename effective).2.1
      obtain ⟨nextWindow, nextSuffix, _⟩ := retainCatalog initial.1 gone
      exact ⟨nextWindow, finalKeeper, finalDurability, nextSuffix⟩)
  obtain ⟨sameName, sameBytes⟩ := keeperStorage _ rfl
  have afterCleanup := (keeperCleanup _ (congrArg (fun start => (dir).file (.walSegment start))
    (congrArg Target.first sameTarget))).2 _ named
  have liveAtSync := errorEffect.2.2.2
  have live := (List.cons.inj afterCleanup).1.trans
    ((congrFun liveAtSync _).trans (keeperBytes.trans (congrArg Target.trimmed sameTarget)))
  have ⟨active, later⟩ : (view.files finalized.reached).image.keeper.active = some target.trimmed ∧
      (view.files finalized.reached).image.later.DurablyEmpty := by
    rw [finalImage, workerImage, ← sameTarget]
    exact issue.visibleAfterRename effective
  refine ⟨returned, selectedEffects, sameName.trans named, (sameBytes _ named).trans durable, live, active, later, ?_⟩
  intro beforeReboot reboot reset atBoot failedKeeper cacheKeeper readKeeper listKeeper
    buffered physical heldRoot rootNamed unlinkStorage records readsPending readsRoot renameEffect loadSurvivors cleanupSurvivors
  have observedLong : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [measured]
    exact pruning.longer
  have liveBeforeRepair : RawOpenRetryTrace.LiveKeeperCrashChoices dir layout.target (storage afterKeeper) :=
    sameTarget.symm ▸ listing.keepsLiveKeeperBeforeRepair prior reboot reset atBoot (sameTarget ▸ targetAtKeeper)
      failedKeeper cacheKeeper readKeeper listKeeper selected seals observedLong keeperRead
  let keeperPath := (dir).file (.walSegment layout.keeper.first)
  let immutableChild : FilePath → Prop := fun path => state.selectedRetryPath path ∧ path ≠ (dir).path
  let crashScope : FilePath → Prop := fun path => path = keeperPath ∨ immutableChild path
  let replacement := staged.inventory.inode staged.slot.description
  obtain ⟨old, oldAtEntry, acceptedAtEntry⟩ := liveBeforeRepair
  have away (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) :
      ¬ state.crashPath ((dir).file (.walSegment ordinal)) :=
    laterWalOutsideRepairScope currentReady
      (targetAtKeeper ▸ Nat.lt_of_le_of_lt layout.target.firstCovered (pruning.later ordinal member))
  have writtenPrefix : stageWrite ((dir).file .stagedWal)
      (layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize) pruned = .ok () recorded := by
    rw [layout.boundedPlan_extractKeeper]
    exact written
  obtain ⟨durableFrame, _, _, _, _, oldNamed, childrenSettled, ⟨prunedNames, prunedSettled⟩,
    stageIssued, file, slot, literalReplacement, _, _, apart, stageAtIssue, bytesAtIssue, fileSync, _, _⟩ :=
    source.stage.prunedAndSyncedReplacement callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename seed.handle physical
      layout.boundedPlan targetAtKeeper heldRoot rootNamed oldAtEntry away unlinkStorage records readsPending readsRoot
      authorize unlinks suffixSync writtenPrefix persisted
  have keeperInScope : state.crashPath keeperPath :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl
      (congrArg (fun start => (dir).file (.walSegment start)) targetAtKeeper)))
  have oldPayload : ∀ payload ∈ (storage synced).files.bytes old, layout.target.Accepts (some payload) := by
    intro payload present
    exact acceptedAtEntry payload (((durableFrame _ keeperInScope).2 old oldAtEntry) ▸ present)
  have settled : ∀ names ∈ (storage synced).crashNames, names keeperPath = some old :=
    fun names possible => (childrenSettled names possible (.walSegment layout.keeper.first) keeperInScope).trans oldNamed
  have stageNamed := (congrFun fileSync.names ((dir).file .stagedWal)).trans stageAtIssue
  have bytePrefix : visible stageIssued literalReplacement = layout.target.trimmed := by
    rw [bytesAtIssue, layout.boundedPlan_extractKeeper]
    rfl
  have stagedAtSync : (storage synced).files.bytes literalReplacement = [layout.target.trimmed] := by
    simpa [bytePrefix] using fileSync.bytes literalReplacement
  have inodeMove := renameEffect moved stageNamed oldNamed apart
  have atRename : (storage renamedHeap).files.names keeperPath = some literalReplacement := by
    simpa [keeperPath, WalKeeperRenameEffect.rebind] using
      inodeMove.visible keeperPath (.inr ⟨.walSegment layout.keeper.first, rfl⟩)
  have loadedFrame : (storage renamedHeap).CrashFileFrame crashScope (storage issued) := loadSurvivors loaded
  have keeperAtIssue : retryNames issued keeperPath = some literalReplacement :=
    (loadedFrame.toFrames.visible keeperPath (.inl rfl)).1.trans atRename
  have keeperAsReported : retryNames issued keeperPath = some replacement :=
    (errorEffect.2.1.visible (.walSegment layout.keeper.first)).symm.trans named
  have sameReplacement : literalReplacement = replacement := Option.some.inj (keeperAtIssue.symm.trans keeperAsReported)
  have atIssueSurvivors : RawOpenRetryTrace.KeeperCrashChoices dir layout.target (storage issued) :=
    (inodeMove.acceptsKeeperSurvivors (target := layout.target) settled stagedAtSync oldPayload).frame loadedFrame (.inl rfl)
  have atErrorSurvivors : RawOpenRetryTrace.KeeperCrashChoices dir layout.target (storage reached) :=
    errorEffect.2.1.acceptsKeeperSurvivors atIssueSurvivors keeperAtIssue (sameReplacement.symm ▸ keeperDurable)
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
  have immutableAtIssue (names : FilePath → Option Nat) (possible : names ∈ (storage issued).crashNames)
      (path : FilePath) (selectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      names path = retryNames issued path :=
    loadChildren.settledFrom (fun prior possible path child => immutableAtRename prior possible path child.1 child.2)
      names possible path ⟨selectedPath, notRoot⟩
  have immutableAtError := errorEffect.2.1.keepsSelectedChildren immutableAtIssue
  have cleanupChildren := afterWorker.toFrames.weaken (scope := immutableChild) (fun _ child => .inr child)
  have immutableAtReboot (path : FilePath) (selectedPath : state.selectedRetryPath path) (notRoot : path ≠ (dir).path) :
      retryNames rebooted path = retryNames finalized.reached path :=
    cleanupChildren.settledFrom (fun prior possible path child => immutableAtError prior possible path child.1 child.2)
      _ seen.chosen path ⟨selectedPath, notRoot⟩
  have actualDurability := ((selectedEffects.preserves initial).2.2.2 priorStorage).2.2.1
  obtain ⟨nextEntry, vacant, empty⟩ := seen.selectsRetryAfterRepair (sameTarget ▸ targetAtKeeper)
    sameManifest actualDurability immutableAtReboot survivesCleanup
  refine ⟨nextEntry, vacant, empty, ?_⟩
  intro stageWriteCatalog stageSyncCatalog loadCatalog cleanupCatalog reset
  have atEntry := ((before.preserves initial).2.2.2 priorStorage).1
  have atPrune := settlesPrunedWindow (retainCatalog atEntry later.1).2.2 prunedNames prunedSettled
  have throughStage := (stageWriteCatalog written).trans (stageSyncCatalog persisted)
  have throughRename := throughStage.trans (inodeMove.walNames oldNamed settled firstOffset through)
  have throughError := (throughRename.trans (loadCatalog loaded)).trans (WalNamePresenceFrame.ofRootSync errorEffect.2.1)
  have throughCleanup := throughError.trans (cleanupCatalog.afterWorker (fun earlier later => earlier.trans later))
  have window := (throughCleanup.preservesNamespaceWindow atPrune).2 _ seen.chosen
  exact seen.startsRecoveryObservations reset nextEntry window

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
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {authorized pruned recorded synced : heap} {cause : IO.Error} {effective : Bool} {old : Nat}
    (startFiles : (view.files afterKeeper).image = (view.files entry).image)
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
      (fun before after => view.pending after seed.pendingRef = view.pending before seed.pendingRef))
    (listingPendingFrames : source.directoryCalls.ScopeFrames dir
      (fun before after => view.pending after seed.pendingRef = view.pending before seed.pendingRef))
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
            ((stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded →
                WalNamePresenceFrame dir firstOffset through (storage pruned) (storage recorded)) →
              (groupSync #[((dir).file .stagedWal)] recorded = .ok () synced →
                WalNamePresenceFrame dir firstOffset through (storage recorded) (storage synced)) →
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
  obtain ⟨prunedTrace, prunedEmpty, syncedImage, keeperActive⟩ :=
    longKeeperSyncPrefix (fun atHeap => (view.files atHeap).image) dir target layout.boundedPlan
      source.remove stageWrite groupSync source.rename authorize prune actualWrite persisted covers later
      authorizationImage pruneImage unlinkImage (fun _ => writeStage) (fun _ _ => syncStage)
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
  obtain ⟨durableFrame, rootFrame, _, authorizedScope, stageScope, oldAtRename, childrenSettled,
    ⟨prunedNames, prunedSettled⟩, issued, file, slot, replacement, _, _, apart, stageAtIssue, bytesAtIssue, fileSync, liveAtSync, protects⟩ :=
    source.stage.prunedAndSyncedReplacement callbacks
      (state.repairDirectoryScope (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename seed.handle physical
      layout.boundedPlan (path.trans targetAtKeeper) root rootNamed
      (by simpa only [NativeReadyState.repairDirectoryScope, path] using oldNamed) away unlinkStorage records readsPending readsRoot
      authorize unlinks suffixSync writtenPrefix persisted
  have renamedOld : retryNames synced ((dir).file (.walSegment target.first)) = some old := by
    simpa only [NativeReadyState.repairDirectoryScope, path] using oldAtRename
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
  have emptyPending := listing.emptyPendingAfterLongKeeper selected seals readPendingFrames listingPendingFrames
    (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle)) observedLong keeperRead
  have live := protects liveEffects emptyPending
  have sameOld : visible synced old = visible afterKeeper old :=
    (List.cons.inj ((live _ keeperPath).2 old oldNamed)).1
  have atRename : RawOpenRetryTrace.KeeperAt view dir target retryNames visible synced := by
    unfold RawOpenRetryTrace.KeeperAt at keeper ⊢
    rw [keeperActive, keeper, renamedOld, oldNamed]
    exact congrArg some sameOld.symm
  have toRename : retryFrame afterKeeper synced := by
    have inScope (path : FilePath) (selected : state.selectedRetryPath path) : state.crashPath path :=
      NativeReadyState.crashPath_iff_write.mpr (selected.imp id Or.inr)
    exact ⟨fun path selected => live path (inScope path selected),
      fun path selected => durableFrame path (inScope path selected), rootFrame⟩
  have safe (path : FilePath) (selectedPath : state.selectedRetryPath path) :
      path ≠ (dir).file (.walSegment target.first) ∧ path ≠ (dir).file .stagedWal := by
    refine ⟨?_, state.stagedWalOutsideRetryFootprint path selectedPath⟩
    rw [targetAtKeeper]
    exact state.protectedPathNeWalFromActive currentReady selectedPath (Nat.le_refl _)
  obtain ⟨repair, trace, framed, liveKeeper, _, renameNames, _, _, laterGone⟩ :=
    failedLongKeeperRename view state target layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      storage visible source.remove stageWrite groupSync source.rename checked size longer path payload authorize
      prune actualWrite persisted prunedTrace prunedEmpty syncedImage toRename safe renamedOld oldChoices stagedNamed
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
  intro stageWriteCatalog stageSyncCatalog cleanupCatalog reset
  have atEntry := ((before.preserves initial).2.2.2 priorStorage).1
  have gone : (view.files finalized.reached).image.later.visible = [] := finalImage.symm ▸ laterGone.1
  have atPrune := settlesPrunedWindow (retainCatalog atEntry gone).2.2 prunedNames prunedSettled
  have throughStage := (stageWriteCatalog written).trans (stageSyncCatalog persisted)
  have throughError := throughStage.trans (renameNames firstOffset through)
  have throughCleanup := throughError.trans (cleanupCatalog.afterWorker (fun earlier later => earlier.trans later))
  have window := (throughCleanup.preservesNamespaceWindow atPrune).2 _ seen.chosen
  exact seen.startsRecoveryObservations reset nextEntry window

end SelectedRetry

end Alvoki.Storage.DiskSession
