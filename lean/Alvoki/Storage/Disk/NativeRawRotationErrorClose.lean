import Alvoki.Storage.Disk.NativeRawRotationDirectoryError
import Alvoki.Storage.Disk.NativeRotationErrorReopen

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

section

variable {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory

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
    (atFailure : view.Matches opened.phase cache.active cache.pending cache.directory failed failure.closeState)
    (owner : (view.handle failed opened.lock).2.1 = (state).owner)
    (drops : CloseCacheField → List LockReferenceDrop)
    (unlocked : unlock opened.lock failed = .ok () afterUnlock)
    (unlockEffect : (view.handle failed opened.lock).2.1 ∈ (view.descriptors failed).slots →
      (view.handle failed opened.lock).2.1.description = (state).session.descriptor →
      unlock opened.lock failed = .ok () afterUnlock →
      view.Matches opened.phase cache.active cache.pending cache.directory afterUnlock
        (failure.closeState.release dir (state).session.descriptor))
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
    rw [owner, atFailure.2.2.2]
    exact ownerLive
  have described := (congrArg DescriptorSlot.description owner).trans valid.owner
  have afterRelease := unlockEffect live described unlocked
  have read := opened.phaseEffects.reads failed opened.phase _ poisoned
  obtain ⟨rawClose, projected⟩ :=
    clears.returnsAfterUnlock (start := failure.closeState.release dir (state).session.descriptor)
      read (by intro impossible; cases impossible) unlocked afterRelease
  have reached := atFailure.closedFrom projected valid.retained.held
  refine ⟨source, ?_, reached, ?_⟩
  · rw [returned]
    exact congrArg (fun outcome => some (IO.userError s!"sync failed for '{opened.directory.path}': {cause}", outcome))
      rawClose
  · obtain ⟨_, _, files, census⟩ := reached
    have image : (view.files clears.afterPhase).image = failure.reported.after := by
      rw [files, atFailure.2.2.1]
      rfl
    have exactInode : (view.descriptors clears.afterPhase).inode = failure.reported.effectInventory.inode := by
      rw [census, atFailure.2.2.2]
      rfl
    dsimp only
    rw [image, exactInode]
    refine ⟨named, object, ?_⟩
    rw [object, failure.reported.bytes]
    exact failure.created.empty

end

end Alvoki.Storage.DiskSession
