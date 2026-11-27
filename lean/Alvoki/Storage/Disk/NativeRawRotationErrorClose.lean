import Alvoki.Storage.Disk.NativeRawRotationDirectoryError
import Alvoki.Storage.Disk.NativeRotationErrorReopen

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

section

variable {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory

/-- Effects at the reached callbacks of the exclusive-created branch.
The live file frame carries names and bytes while permitting different
crash alternatives at the failed directory barrier. -/
structure NativeRotationCloseEffects
    {calls : OpenRotationCallbacks heap} {stager : RawWalStageCalls heap} {raw : RawSyncCalls heap}
    {cause : IO.Error} (failure : NativeRotationDirectoryFailure state (some cause))
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    {poisoned synced : heap}
    {filePrefix : calls.SuccessorFilePrefix opened.directory (state).writer.rotationInstalled.activeFirst poisoned synced}
    (file : filePrefix.ExclusiveSync stager raw cache) (issued failed : heap) : Prop where
  authority :
      let lock := DiskDirectory.file dir .lock
      let project := fun h => ((view.files h).owners lock, (view.handle h opened.lock).2.1)
      let same := fun before after => project after = project before
      let keep := fun before after => same before after ∧
        opened.contents after opened.phase = opened.contents before opened.phase
      project current.reached = (some (state).session.descriptor, (state).owner) ∧
      same current.reached poisoned ∧ keep poisoned filePrefix.afterRead ∧
      keep filePrefix.afterRead filePrefix.beforeSync ∧ keep filePrefix.beforeSync synced ∧
      keep synced issued ∧ keep issued failed
  inventoryEffects :
      let census := view.descriptors
      ∃ remembered readPending consumed syncedFile readRoot : List LockReferenceDrop,
        remembered ++ readPending ++ consumed = failure.reported.drops ∧
        syncedFile ++ readRoot = failure.reported.beforeDirectory ∧
        census file.opened = failure.created.handle.1 ∧
        census filePrefix.beforeSync = (census file.opened).afterDrops remembered ∧
        census file.loaded = (census filePrefix.beforeSync).afterDrops readPending ∧
        census file.issued = (census file.loaded).afterDrops consumed ∧
        census synced = (census file.issued).afterDrops syncedFile ∧
        census issued = (census synced).afterDrops readRoot ∧ census failed = census issued
  fileEffects :
      let project := fun h => ((view.files h).image.view, (view.files h).image.inodes.visible)
      let same := fun before after => project after = project before
      project file.opened = (failure.created.files.view, failure.created.files.inodes.visible) ∧
      same file.opened filePrefix.beforeSync ∧ same filePrefix.beforeSync file.loaded ∧
      same file.loaded file.issued ∧ same file.issued synced ∧ same synced issued ∧ same issued failed

/-- Derive the failed rotation effects used by live close and reopen.
The close uses the actual cache and crash alternatives. The rotation
model supplies the comparison for its live bindings and bytes. -/
theorem NativeOpenedPosition.rotationErrorCloseProjection
    (calls : OpenRotationCallbacks heap) (stager : RawWalStageCalls heap) (raw : RawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    {cause : IO.Error} {poisoned synced issued failed : heap} {root : IO.FS.Handle}
    (failure : NativeRotationDirectoryFailure state (some cause))
    (poisonedAt : opened.set opened.phase .poisoned current.reached = .ok () poisoned)
    (filePrefix : calls.SuccessorFilePrefix opened.directory (state).writer.rotationInstalled.activeFirst poisoned synced)
    (file : filePrefix.ExclusiveSync stager raw cache)
    (rootRoute : calls.sync opened.directory.path synced =
      raw.group opened.directory.path cache.directory cache.active cache.pending #[opened.directory.path] synced)
    (loaded : raw.readDirectory cache.directory synced = .ok (some root) issued)
    (rootFailed : raw.fsync root issued = .error cause failed)
    (effects : NativeRotationCloseEffects current failure cache view file issued failed) :
    calls.run opened failure.lookup cache.active current.reached =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") failed ∧
    opened.contents failed opened.phase = some .poisoned ∧
    view.descriptors failed = failure.reported.effectInventory ∧
    (view.handle failed opened.lock).2.1 = (state).owner ∧
    (view.files failed).owners.Owns dir (state).session.descriptor ∧
    (view.files failed).image.view = failure.reported.after.view ∧
    (view.files failed).image.inodes.visible = failure.reported.after.inodes.visible := by
  have checked : checkActiveSegmentWith opened.directory (state).writer.installed failure.lookup = .ok () := by
    rw [← current.directory]
    exact failure.reported.checked
  obtain ⟨guard, lookup⟩ := BatchActiveGuard.ofChecked failure.lookup checked
  have started := current.rotationReturnsDirectoryError calls raw cache guard failure.parent.nonempty
    poisonedAt filePrefix rootRoute loaded rootFailed
  rw [lookup] at started
  obtain ⟨initial, poison, read, create, sync, readRoot, error⟩ := effects.authority
  let lock := DiskDirectory.file dir .lock
  let custody := fun h => ((view.files h).owners lock, (view.handle h opened.lock).2.1)
  obtain ⟨poisonedPhase, _, carries⟩ := started.2.2.2 (frame := fun before after => custody after = custody before)
    (fun first last => last.trans first) read (fun _ => create) sync readRoot error
  have held := (carries poison).trans initial
  have inventoryAt : view.descriptors failed = failure.reported.effectInventory := by
    obtain ⟨_, _, _, _, _, beforeFile, beforeRoot, openedCensus, remembered, loadedCensus,
      consumed, syncedCensus, rootCensus, failedCensus⟩ := effects.inventoryEffects
    have atFile : view.descriptors file.issued =
        failure.created.handle.1.afterDrops failure.reported.drops := by
      simp only [consumed, loadedCensus, remembered, openedCensus, DescriptorInventory.afterDrops_append, beforeFile]
    rw [failedCensus, rootCensus, syncedCensus, atFile, DescriptorInventory.afterDrops_append, beforeRoot]
    rfl
  obtain ⟨openedFile, remembered, loadedFiles, consumed, syncedFiles, rootFiles, failedFiles⟩ := effects.fileEffects
  have images := failedFiles.trans (rootFiles.trans (syncedFiles.trans (consumed.trans
    (loadedFiles.trans (remembered.trans openedFile)))))
  have namespaceAt := (congrArg Prod.fst images).trans failure.reported.view.symm
  have visibleAt := (congrArg Prod.snd images).trans
    (congrArg WAL.Boundary.WalInodeImage.visible failure.reported.bytes).symm
  exact ⟨started.2.2.1, poisonedPhase, inventoryAt, congrArg Prod.snd held, congrArg Prod.fst held,
    namespaceAt, visibleAt⟩

/-- A returned directory error passes its actual poisoned heap to the
same table's close. Unlock and the reached setters leave the exact drop
inventory and keep the already visible successor for a live reopen. -/
theorem NativeOpenedPosition.closesAfterRotationDirectoryError
    (calls : OpenRotationCallbacks heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    (unlock : IO.FS.Handle → EStateM IO.Error heap Unit)
    (setCell : {α : Type} → IO.Ref α → α → EStateM IO.Error heap Unit)
    {cause : IO.Error} {failed afterUnlock : heap}
    (failure : NativeRotationDirectoryFailure state (some cause))
    (returned : calls.run opened failure.lookup cache.active current.reached =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") failed)
    (poisoned : opened.contents failed opened.phase = some .poisoned)
    (census : view.descriptors failed = failure.reported.effectInventory)
    (liveFiles : (view.files failed).image.view = failure.reported.after.view ∧
      (view.files failed).image.inodes.visible = failure.reported.after.inodes.visible)
    (owner : (view.handle failed opened.lock).2.1 = (state).owner)
    (held : (view.files failed).owners.Owns dir (state).session.descriptor)
    (drops : CloseCacheField → List LockReferenceDrop)
    (unlocked : unlock opened.lock failed = .ok () afterUnlock)
    (unlockEffect : (view.files failed).owners.Owns dir (state).session.descriptor →
      (view.handle failed opened.lock).2.1 ∈ (view.descriptors failed).slots →
      (view.handle failed opened.lock).2.1.description = (state).session.descriptor →
      unlock opened.lock failed = .ok () afterUnlock →
      view.phase afterUnlock opened.phase = some .poisoned ∧
      view.files afterUnlock = ⟨(view.files failed).image, (view.files failed).owners.set (DiskDirectory.file dir .lock) none⟩ ∧
      view.descriptors afterUnlock = view.descriptors failed)
    (clears : OpenCloseClears drops view ⟨opened.get, unlock, setCell⟩
      opened.phase cache.active cache.pending cache.directory afterUnlock) :
    opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (cache.active.set none) (cache.pending.set []) (cache.directory.set none) (opened.phase.set .closed) ∧
    (match calls.run opened failure.lookup cache.active current.reached with
      | .ok () _ => none
      | .error diagnostic atError =>
        some (diagnostic, closeSchedule (opened.get opened.phase) (fun _ => unlock opened.lock)
          (setCell cache.active none) (setCell cache.pending []) (setCell cache.directory none)
          (setCell opened.phase .closed) atError)) =
      some (IO.userError s!"sync failed for '{opened.directory.path}': {cause}", .ok () clears.afterPhase) ∧
    view.ClosedFrom opened.phase cache.active cache.pending cache.directory dir drops failed clears.afterPhase ∧
    let file := view.files clears.afterPhase
    let successor := file.image.view.modelObject failure.created.child.child
    file.image.view.child failure.parent.root
      (renderWalSegmentName ((state).writer.installed.walBytes / WAL.frameSize)) = some failure.created.child.child ∧
    successor = (view.descriptors clears.afterPhase).inode failure.created.raw.description ∧
    file.image.inodes.visible successor = ByteArray.empty := by
  obtain ⟨active, pending, cached, refs, schedule⟩ := opened.uses.close
  have activeRef := refs.1.symm.trans cache.references.1
  have pendingRef := refs.2.1.symm.trans cache.references.2.1
  have directoryRef := refs.2.2.symm.trans cache.references.2.2
  have source : opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (cache.active.set none) (cache.pending.set []) (cache.directory.set none) (opened.phase.set .closed) := by
    simpa only [activeRef, pendingRef, directoryRef] using schedule
  have valid := current.current.ready.readPrefix.refines.1
  obtain ⟨_, _, _, _, ownerLive, _, _, _, named, object, _⟩ := failure.custody valid
  have live : (view.handle failed opened.lock).2.1 ∈ (view.descriptors failed).slots := by
    rw [owner, census]
    exact ownerLive
  have described := (congrArg DescriptorSlot.description owner).trans valid.owner
  obtain ⟨phaseAtUnlock, filesAtUnlock, censusAtUnlock⟩ := unlockEffect held live described unlocked
  have read := opened.phaseEffects.reads failed opened.phase _ poisoned
  obtain ⟨rawClose, reached⟩ := clears.closesObserved
    read (by intro impossible; cases impossible) unlocked phaseAtUnlock filesAtUnlock censusAtUnlock
  refine ⟨source, ?_, reached, ?_⟩
  · rw [returned]
    exact congrArg (fun outcome => some (IO.userError s!"sync failed for '{opened.directory.path}': {cause}", outcome))
      rawClose
  · obtain ⟨_, _, files, closedCensus⟩ := reached
    have closedView := (congrArg (fun file => (LockedFileState.image file).view) files).trans liveFiles.1
    have closedBytes := (congrArg (fun file => (LockedFileState.image file).inodes.visible) files).trans liveFiles.2
    have exactInode : (view.descriptors clears.afterPhase).inode = failure.reported.effectInventory.inode := by
      rw [closedCensus, census]
      rfl
    dsimp only
    rw [closedView, closedBytes, exactInode]
    refine ⟨named, object, ?_⟩
    rw [object, failure.reported.bytes]
    exact failure.created.empty

end

end Alvoki.Storage.DiskSession
