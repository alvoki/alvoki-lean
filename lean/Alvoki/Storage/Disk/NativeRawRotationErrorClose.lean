import Alvoki.Storage.Disk.FileObservationFrame
import Alvoki.Storage.Disk.NativeRawRotationDirectoryError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting
open WAL.Boundary (WalInodeImage)

namespace RotationCreateFiles

/-- The reached name and visible bytes agree for selected children of one
directory. Crash name and byte choices are outside this live frame. -/
def FramesLiveChildren (root : DeviceInode) (children : String → Prop)
    (before after : RotationCreateFiles) : Prop :=
  FileObservationFrame (fun files name => (files.view.child root name).map files.view.modelObject)
    (fun files => files.inodes.visible) children before after

theorem FramesLiveChildren.trans {root children} {before middle after : RotationCreateFiles}
    (first : before.FramesLiveChildren root children middle)
    (last : middle.FramesLiveChildren root children after) : before.FramesLiveChildren root children after :=
  FileObservationFrame.trans first last

end RotationCreateFiles

section

variable {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "successorName" => renderWalSegmentName current.current.ready.state.writer.rotationInstalled.activeFirst

/-- Local effects along the exclusive-create route. The lock slot stays
live among the actual descriptors. The exclusive open binds the child
to an empty inode, and later callbacks retain those visible bytes. -/
structure NativeRotationCloseEffects
    {calls : OpenRotationCallbacks heap} {stager : RawWalStageCalls heap} {raw : RawSyncCalls heap}
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    {poisoned synced : heap}
    {filePrefix : calls.SuccessorFilePrefix opened.directory (state).writer.rotationInstalled.activeFirst poisoned synced}
    (file : filePrefix.ExclusiveSync stager raw cache)
    (root : DeviceInode) (children : String → Prop) (issued failed : heap) : Prop where
  authority :
    let lock := DiskDirectory.file dir .lock
    let project := fun h => ((view.files h).owners lock, (view.handle h opened.lock).2.1)
    let live := fun h => (view.handle h opened.lock).2.1 ∈ (view.descriptors h).slots
    let same := fun before after => project after = project before ∧ (live before → live after)
    let keep := fun before after => same before after ∧
      opened.contents after opened.phase = opened.contents before opened.phase
    project current.reached = (some (state).session.descriptor, (state).owner) ∧ live current.reached ∧
    same current.reached poisoned ∧ keep poisoned filePrefix.afterRead ∧
    keep filePrefix.afterRead filePrefix.beforeSync ∧ keep filePrefix.beforeSync synced ∧
    keep synced issued ∧ keep issued failed
  exclusiveOpened :
    let files := (view.files file.opened).image
    ∃ child : DeviceInode, files.view.child root successorName = some child ∧
      files.view.modelObject child = view.capturedInode file.opened file.handle ∧
      files.inodes.visible (files.view.modelObject child) = ByteArray.empty
  beforeCreation :
    let keep := fun before after =>
      (view.files before).image.FramesLiveChildren root children (view.files after).image
    keep current.reached poisoned ∧ keep poisoned filePrefix.afterRead ∧ keep filePrefix.afterRead file.opened
  afterCreation :
    let keep := fun before after =>
      (view.files before).image.FramesLiveChildren root (fun name => children name ∨ name = successorName)
        (view.files after).image
    keep file.opened filePrefix.beforeSync ∧ keep filePrefix.beforeSync file.loaded ∧
    keep file.loaded file.issued ∧ keep file.issued synced ∧ keep synced issued ∧ keep issued failed

/-- Follow the returned rotation through the literal callbacks. The
actual failed heap retains the lock and the visible successor bound
to the exclusive-open handle. This is a live observation. -/
theorem NativeOpenedPosition.rotationErrorCloseProjection
    (calls : OpenRotationCallbacks heap) (stager : RawWalStageCalls heap) (raw : RawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    (guard : BatchActiveGuard opened.directory (state).writer.installed)
    {cause : IO.Error} {poisoned synced issued failed : heap} {root : IO.FS.Handle}
    (nonempty : (state).writer.installed.activeFirst < (state).writer.rotationInstalled.activeFirst)
    (poisonedAt : opened.set opened.phase .poisoned current.reached = .ok () poisoned)
    (filePrefix : calls.SuccessorFilePrefix opened.directory (state).writer.rotationInstalled.activeFirst poisoned synced)
    (file : filePrefix.ExclusiveSync stager raw cache)
    (rootRoute : calls.sync opened.directory.path synced =
      raw.group opened.directory.path cache.directory cache.active cache.pending #[opened.directory.path] synced)
    (loaded : raw.readDirectory cache.directory synced = .ok (some root) issued)
    (rootFailed : raw.fsync root issued = .error cause failed)
    {directoryObject : DeviceInode} {children : String → Prop}
    (effects : NativeRotationCloseEffects current cache view file directoryObject children issued failed) :
    calls.run opened guard.lookup cache.active current.reached =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") failed ∧
    opened.contents failed opened.phase = some .poisoned ∧
    (view.handle failed opened.lock).2.1 = (state).owner ∧
    (view.files failed).owners.Owns dir (state).session.descriptor ∧
    (view.handle failed opened.lock).2.1 ∈ (view.descriptors failed).slots ∧
    (view.files current.reached).image.FramesLiveChildren directoryObject children (view.files failed).image ∧
    ∃ child : DeviceInode,
      (view.files failed).image.view.child directoryObject successorName = some child ∧
      (view.files failed).image.view.modelObject child = view.capturedInode file.opened file.handle ∧
      (view.files failed).image.inodes.visible ((view.files failed).image.view.modelObject child) =
        ByteArray.empty := by
  have started := current.rotationReturnsDirectoryError calls raw cache guard nonempty
    poisonedAt filePrefix rootRoute loaded rootFailed
  obtain ⟨initial, initialLive, poison, read, create, sync, readRoot, failedSync⟩ := effects.authority
  let lock := DiskDirectory.file dir .lock
  let custody := fun h => ((view.files h).owners lock, (view.handle h opened.lock).2.1)
  let live := fun h => (view.handle h opened.lock).2.1 ∈ (view.descriptors h).slots
  let frame := fun before after => custody after = custody before ∧ (live before → live after)
  obtain ⟨poisonedPhase, _, carries⟩ := started.2.2.2 (frame := frame)
    (fun first last => ⟨last.1.trans first.1, fun found => last.2 (first.2 found)⟩)
    read (fun _ => create) sync readRoot failedSync
  have preserved := carries poison
  have held := preserved.1.trans initial
  obtain ⟨beforePoison, probe, createFrame⟩ := effects.beforeCreation
  obtain ⟨remember, load, consume, fileSync, rootLoad, rootError⟩ := effects.afterCreation
  have fromOpened := remember.trans (load.trans (consume.trans (fileSync.trans (rootLoad.trans rootError))))
  have toOpened := beforePoison.trans (probe.trans createFrame)
  have kept : (view.files current.reached).image.FramesLiveChildren directoryObject children (view.files failed).image :=
    toOpened.trans fun name member => fromOpened name (.inl member)
  refine ⟨started.2.2.1, poisonedPhase, congrArg Prod.snd held, congrArg Prod.fst held,
    preserved.2 initialLive, kept, ?_⟩
  obtain ⟨fresh, named, inode, empty⟩ := effects.exclusiveOpened
  let number := view.capturedInode file.opened file.handle
  have openedName : ((view.files file.opened).image.view.child directoryObject successorName).map
      (view.files file.opened).image.view.modelObject = some number := by
    rw [named, Option.map_some, inode]
  obtain ⟨stays, retainsBytes⟩ := fromOpened successorName (.inr rfl)
  have finalName := stays.trans openedName
  cases found : (view.files failed).image.view.child directoryObject successorName with
  | none => simp [found] at finalName
  | some child =>
    have same := Option.some.inj (by simpa only [found, Option.map_some] using finalName)
    refine ⟨child, rfl, same, ?_⟩
    rw [same]
    exact (retainsBytes number openedName).trans (by simpa only [inode] using empty)

/-- Close the literal poisoned table at the reached rotation error.
Unlock and the cache clears start from that heap and preserve its files. -/
theorem NativeOpenedPosition.closesAfterRotationDirectoryError
    (calls : OpenRotationCallbacks heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (view : OpenCloseHeapView heap RotationCreateFiles)
    (unlock : IO.FS.Handle → EStateM IO.Error heap Unit)
    (setCell : {α : Type} → IO.Ref α → α → EStateM IO.Error heap Unit)
    (guard : BatchActiveGuard opened.directory (state).writer.installed)
    {cause : IO.Error} {failed afterUnlock : heap}
    (returned : calls.run opened guard.lookup cache.active current.reached =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") failed)
    (poisoned : opened.contents failed opened.phase = some .poisoned)
    (owner : (view.handle failed opened.lock).2.1 = (state).owner)
    (held : (view.files failed).owners.Owns dir (state).session.descriptor)
    (live : (view.handle failed opened.lock).2.1 ∈ (view.descriptors failed).slots)
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
    (match calls.run opened guard.lookup cache.active current.reached with
      | .ok () _ => none
      | .error diagnostic atError =>
        some (diagnostic, closeSchedule (opened.get opened.phase) (fun _ => unlock opened.lock)
          (setCell cache.active none) (setCell cache.pending []) (setCell cache.directory none)
          (setCell opened.phase .closed) atError)) =
      some (IO.userError s!"sync failed for '{opened.directory.path}': {cause}", .ok () clears.afterPhase) ∧
    view.ClosedFrom opened.phase cache.active cache.pending cache.directory dir drops failed clears.afterPhase := by
  obtain ⟨active, pending, cached, refs, schedule⟩ := opened.uses.close
  have activeRef := refs.1.symm.trans cache.references.1
  have pendingRef := refs.2.1.symm.trans cache.references.2.1
  have directoryRef := refs.2.2.symm.trans cache.references.2.2
  have source : opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (cache.active.set none) (cache.pending.set []) (cache.directory.set none) (opened.phase.set .closed) := by
    simpa only [activeRef, pendingRef, directoryRef] using schedule
  have valid := current.current.ready.readPrefix.refines.1
  have described := (congrArg DescriptorSlot.description owner).trans valid.owner
  obtain ⟨phaseAtUnlock, filesAtUnlock, censusAtUnlock⟩ := unlockEffect held live described unlocked
  have read := opened.phaseEffects.reads failed opened.phase _ poisoned
  obtain ⟨rawClose, reached⟩ := clears.closesObserved
    read (by intro impossible; cases impossible) unlocked phaseAtUnlock filesAtUnlock censusAtUnlock
  refine ⟨source, ?_, reached⟩
  rw [returned]
  exact congrArg (fun outcome => some (IO.userError s!"sync failed for '{opened.directory.path}': {cause}", outcome))
    rawClose

end

end Alvoki.Storage.DiskSession
