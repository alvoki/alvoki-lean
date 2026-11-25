import Alvoki.Storage.Disk.WalCollectionOrderedPrefix
import Alvoki.Storage.Disk.SegmentedCollectionStep

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

abbrev WalCollectionDirectoryHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The raw call reports its return separately from the directory effect.
The visible names and bytes stay fixed. An effective barrier settles the
existing metadata and sealed namespace. An error before the effect
leaves the reached alternatives in place. -/
structure WalCollectionDirectoryEffect (before after : WalSealedUnlinkImage)
    (outcome : DelayedDirectorySyncOutcome) : Prop where
  sealed : after.visible.sealed = before.visible.sealed
  keeper : after.visible.active = before.visible.active
  metadata : after.visible.directory.active = before.visible.directory.active
  staged : after.visible.directory.staged = before.visible.directory.staged
  crashMetadata : after.visible.directory.crashImages =
    if outcome.effective then [before.visible.directory.active] else before.visible.directory.crashImages
  crashNames : after.crashSealed =
    if outcome.effective then [before.visible.sealed] else before.crashSealed

theorem WalCollectionDirectoryEffect.exactImage {before after : WalSealedUnlinkImage}
    {outcome : DelayedDirectorySyncOutcome} (effect : WalCollectionDirectoryEffect before after outcome) :
    after = if outcome.effective then before.syncDirectory else before := by
  obtain ⟨sealed, keeper, metadata, staged, crashMetadata, crashNames⟩ := effect
  cases before with
  | mk files _ =>
    cases files with
    | mk directory _ _ =>
      cases directory
      cases after with
      | mk files _ =>
        cases files with
        | mk directory _ _ =>
          cases directory
          cases outcome <;> simp_all [DelayedDirectorySyncOutcome.effective, WalSealedUnlinkImage.syncDirectory,
            WalSealedUnlinkImage.start, WalSegmentImage.applyCollectionStep, DirectoryPublication.Image.syncDirectory]

private def directoryFsyncResult (outcome : DelayedDirectorySyncOutcome) (after : WalSealedUnlinkImage) :
    EStateM.Result IO.Error WalSealedUnlinkImage Unit :=
  match outcome with
  | .completed => .ok () after
  | .errorBeforeEffect cause | .errorAfterEffect cause => .error cause after

/-- Physical reports for the final fsync. The writer retains the cache
captured at entry through the unlink prefix. The same observed directory
object names the root of the unlink lookup view and the live cached
description, including at the effect. -/
structure WalCollectionDirectoryFsync (directory : DiskDirectory) (root : DeviceInode)
    (entryView effectView : DirectoryReadNamespace) (writer : Nat) (before : WalSealedUnlinkImage) where
  cache : Cache WalCollectionDirectoryHandle
  handle : WalCollectionDirectoryHandle
  captured : cache.directory = some handle
  captureInode : entryView.modelObject root = handle.1.inode handle.2.1.description
  effectInode : effectView.modelObject root = handle.1.inode handle.2.1.description
  pathObject : FilePath → Option DeviceInode
  bound : pathObject directory.path = some root
  drops : List LockReferenceDrop
  directoryLive : handle.2.1 ∈ (handle.1.afterDrops drops).slots
  writerSlot : DescriptorSlot
  writerDescription : writerSlot.description = writer
  writerLive : writerSlot ∈ (handle.1.afterDrops drops).slots
  openRead : FilePath → EStateM IO.Error WalSealedUnlinkImage WalCollectionDirectoryHandle
  fsync : WalCollectionDirectoryHandle → EStateM IO.Error WalSealedUnlinkImage Unit
  outcome : DelayedDirectorySyncOutcome
  after : WalSealedUnlinkImage
  effect : WalCollectionDirectoryEffect before after outcome
  returned : fsync handle before = directoryFsyncResult outcome after

namespace WalCollectionDirectoryFsync

variable {directory : DiskDirectory} {root : DeviceInode} {entryView effectView : DirectoryReadNamespace}
  {writer : Nat} {before : WalSealedUnlinkImage}

def group (report : WalCollectionDirectoryFsync directory root entryView effectView writer before)
    (path : FilePath) :
    EStateM IO.Error (Cache WalCollectionDirectoryHandle × WalSealedUnlinkImage) Unit :=
  SyncPathGroup.run (SyncHandleRouting.sync directory.path report.openRead report.fsync) #[path]

/-- The singleton group projects its file state into the collector's
existing mutation callback. Its cache is unchanged on the directory route. -/
def syncDirectory (report : WalCollectionDirectoryFsync directory root entryView effectView writer before)
    (path : FilePath) : EStateM IO.Error WalSealedUnlinkImage Unit := fun image =>
  match report.group path (report.cache, image) with
  | .ok () (_, after) => .ok () after
  | .error cause (_, after) => .error cause after

theorem resolves (report : WalCollectionDirectoryFsync directory root entryView effectView writer before) :
    report.cache.resolve directory.path directory.path report.openRead before =
      .ok report.handle (report.cache, before) := by
  simp [Cache.resolve, report.captured]

/-- Both slot references in the effect-time census belong to the reached
writer stretch. The selected directory slot still names its captured
root inode. -/
theorem custody (report : WalCollectionDirectoryFsync directory root entryView effectView writer before) :
    report.pathObject directory.path = some root ∧
    entryView.modelObject root = (report.handle.1.afterDrops report.drops).inode report.handle.2.1.description ∧
    effectView.modelObject root = (report.handle.1.afterDrops report.drops).inode report.handle.2.1.description ∧
    report.handle.2.1.reference ∈
      (report.handle.1.afterDrops report.drops).references report.handle.2.1.description ∧
    report.writerSlot.reference ∈ (report.handle.1.afterDrops report.drops).references writer :=
  ⟨report.bound, report.captureInode, report.effectInode,
    (report.handle.1.afterDrops report.drops).mem_references.mpr ⟨_, report.directoryLive, rfl, rfl⟩,
    (report.handle.1.afterDrops report.drops).mem_references.mpr
      ⟨_, report.writerLive, rfl, report.writerDescription⟩⟩

/-- The actual directory slot reaches the singleton group. Reuse the
path wrapping of the native grouped barrier on either returned error. -/
theorem groupReturns (report : WalCollectionDirectoryFsync directory root entryView effectView writer before) :
    report.group directory.path (report.cache, before) =
      match report.outcome with
      | .completed => .ok () (report.cache, report.after)
      | .errorBeforeEffect cause | .errorAfterEffect cause =>
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") (report.cache, report.after) := by
  rw [group, SyncPathGroup.run_single]
  simp only [SyncHandleRouting.sync, report.resolves, report.returned]
  cases report.outcome <;> rfl

theorem syncReturns (report : WalCollectionDirectoryFsync directory root entryView effectView writer before) :
    report.syncDirectory directory.path before =
      match report.outcome with
      | .completed => .ok () report.after
      | .errorBeforeEffect cause | .errorAfterEffect cause =>
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") report.after := by
  rw [syncDirectory, report.groupReturns]
  cases report.outcome <;> rfl

end WalCollectionDirectoryFsync

/-- The final barrier composes with the existing sealed-unlink trace.
Both outcomes keep the ordered bindings. An effective fsync narrows
the crash namespace to the exact visible names. -/
theorem WalUnlinkInvariant.afterDirectoryFsync {initial : WalSegmentImage} {root : DeviceInode}
    {view : DirectoryReadNamespace} {before projected after : WalSealedUnlinkImage}
    {outcome : DelayedDirectorySyncOutcome}
    (prior : WalUnlinkInvariant initial root view before projected)
    (effect : WalCollectionDirectoryEffect before after outcome) :
    WalUnlinkInvariant initial root view after (if outcome.effective then projected.syncDirectory else projected) := by
  rw [effect.exactImage]
  by_cases effective : outcome.effective = true
  · simp only [effective, ite_true]
    refine ⟨.sync prior.trace, ?_, ?_, ?_⟩
    · exact congrArg (fun image => image.applyCollectionStep .syncDirectory) prior.visible
    · intro sealed member
      change sealed ∈ [before.visible.sealed] at member
      change sealed ∈ [projected.visible.sealed]
      rw [← prior.visible]
      exact member
    · exact prior.sealedNames
  · simp only [effective]
    exact prior

/-- Before the barrier, every reported unlink frames the full metadata
image, including pending staged entries. -/
theorem WalUnlinkPrefix.keepsDirectory {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {failure : Option IO.Error}
    {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed) :
    after.visible.directory = before.visible.directory := by
  induction reported with
  | pause | failedWithoutEffect => rfl
  | next _ effect _ _ ih => exact ih.trans effect.metadata
  | failed _ effect _ => exact effect.metadata

/-- Every successful call detached its target or observed it already
absent. The remainder cannot reintroduce that canonical name. -/
theorem WalUnlinkPrefix.completedNamesAbsent {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {failure : Option IO.Error}
    {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (finished : pending = []) (successful : failure = none) :
    ∀ offset ∈ offsets, afterView.child root (renderWalSegmentName offset) = none := by
  induction reported with
  | pause => simp [finished]
  | next _ effect accepted tail ih =>
    intro offset member
    rcases List.mem_cons.mp member with rfl | later
    · have absent := effect.lookupAfter offset
      rcases effect.accepted accepted with detached | missing
      · simp only [detached, beq_self_eq_true, Bool.and_self, ite_true] at absent
        simpa [absent] using tail.lookupAfter offset
      · simp only [beq_self_eq_true, Bool.and_true, missing, ite_self] at absent
        simpa [absent] using tail.lookupAfter offset
    · exact ih finished successful offset later
  | failed | failedWithoutEffect => contradiction

/-- The first complete reported pass through the original planner and
unlink prefix executes the cached descriptor's final directory barrier.
The returned phase follows the actual syscall result, including an
error reported after settlement. The current writer's table and owner
continue directly, without a reopen premise. -/
theorem SegmentedWriterState.RetainedReady.reportedWalCollectionBarrier
    {directory : DiskDirectory} {descriptor : Nat} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) (calls : WalCollectionReads)
    {root : DeviceInode} {entryView effectView : DirectoryReadNamespace}
    {offsets removed : List Nat} {atBarrier : WalSealedUnlinkImage}
    (planned : calls.plan directory state.installed = .ok offsets)
    (approved : ∀ offset ∈ offsets, offset ∈ state.wal.collectionOffsets)
    (bound : ∀ segment ∈ state.wal.sealed,
      (entryView.child root (renderWalSegmentName segment.first)).isSome = true)
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (unlinked : WalUnlinkPrefix directory root removeFile offsets entryView (.start state.wal)
      [] none effectView atBarrier removed)
    (report : WalCollectionDirectoryFsync directory root entryView effectView descriptor atBarrier) :
    report.after = (if report.outcome.effective then atBarrier.syncDirectory else atBarrier) ∧
      (∃ final, WalUnlinkInvariant state.wal root effectView report.after final) ∧
      (∀ sealed ∈ report.after.crashSealed, WalSegmentCollectionRetry state.wal {report.after.visible with sealed}) ∧
      (report.outcome.effective = true → report.after.crashSealed = [atBarrier.visible.sealed] ∧
        ∀ offset ∈ offsets, ∀ sealed ∈ report.after.crashSealed, ∀ segment ∈ sealed, segment.first ≠ offset) ∧
      (report.outcome = .completed → (state.afterWalCollection report.after).RetainedReady directory descriptor) ∧
      calls.collectWithEffects directory removeFile report.syncDirectory
        (.ready state.installed, ⟨.start state.wal, state.owners⟩) =
        match report.outcome with
        | .completed => .ok () (.ready state.installed, ⟨report.after, state.owners⟩)
        | .errorBeforeEffect cause | .errorAfterEffect cause =>
          .error (IO.userError s!"sync failed for '{directory.path}': {cause}")
            (.poisoned, ⟨report.after, state.owners⟩) := by
  obtain ⟨⟨projected, prior⟩, _, _, _, schedule⟩ :=
    ready.reportedWalUnlinkPrefix calls planned approved bound removeFile report.syncDirectory unlinked
  have after := prior.afterDirectoryFsync report.effect
  refine ⟨report.effect.exactImage, ⟨_, after⟩, ?_, ?_, ?_, ?_⟩
  · intro sealed member
    rw [after.visible]
    exact (after.trace.projects ready.layout).2 sealed (after.survivors sealed member)
  · intro effective
    have settled : report.after.crashSealed = [atBarrier.visible.sealed] := by
      simpa only [effective, ite_true] using report.effect.crashNames
    refine ⟨settled, ?_⟩
    intro offset plannedMember sealed member segment present same
    rw [settled] at member
    have stored : segment ∈ atBarrier.visible.sealed := List.mem_singleton.mp member ▸ present
    have found := prior.bound ready.layout segment stored
    rw [same, unlinked.completedNamesAbsent rfl rfl offset plannedMember] at found
    contradiction
  · intro completed
    have physical : report.after = atBarrier.syncDirectory := by
      simpa [completed, DelayedDirectorySyncOutcome.effective] using report.effect.exactImage
    have projectedAfter : report.after = projected.syncDirectory := by
      rw [physical]
      exact congrArg (fun image => WalSealedUnlinkImage.start (image.applyCollectionStep .syncDirectory)) prior.visible
    have trace : WalSealedUnlinkTrace state.wal report.after := projectedAfter ▸ prior.trace.sync
    have directoryUnchanged : report.after.visible.directory = state.wal.directory := by
      rw [physical]
      change atBarrier.visible.directory.syncDirectory = state.wal.directory
      rw [unlinked.keepsDirectory]
      change state.wal.directory.syncDirectory = state.wal.directory
      have settled := ready.walDirectorySettled
      cases directoryImage : state.wal.directory
      rw [directoryImage] at settled
      simp only [DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.mk.injEq, true_and, and_true]
      exact settled.symm
    apply ready.afterWalCollection trace directoryUnchanged
    rw [physical]
    rfl
  · rw [schedule, WalCollectionReads.continueWithEffects_barrier, report.syncReturns]
    cases report.outcome <;> rfl

end Alvoki.Storage.DiskSession
