import Alvoki.Storage.Disk.Proofs.Rotation.NativePendingRotation
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation
open WAL (frameSize)

variable {state : NativeReadyState} {cause : IO.Error}

namespace NativeRotationDirectoryFailure

/-- The actual poisoned close uses the original cache and reported
reached census, with the raw files returned by the final barrier. -/
def closeState (failure : NativeRotationDirectoryFailure state (some cause)) :
    CachedCloseState CheckpointOpenHandle RotationCreateFiles :=
  ⟨failure.session.phase, ⟨(state.cache, failure.reported.after), state.writer.owners⟩,
    failure.reported.effectInventory⟩

/-- This is a projection of the visible file layout for the next open.
The original phase stays poisoned. The new name is visible under
both final-directory error timings. -/
def liveState (failure : NativeRotationDirectoryFailure state (some cause)) (valid : state.Valid) : NativeReadyState :=
  { state with
    session := failure.session
    writer := state.writer.rotated valid.retained.rotationTarget
    census := failure.reported.effectInventory }

theorem liveWal (failure : NativeRotationDirectoryFailure state (some cause)) (valid : state.Valid) :
    failure.reported.cut.image.visible state.writer.wal = (failure.liveState valid).writer.wal := by
  have settled : state.writer.wal.directory.syncDirectory = state.writer.wal.directory := by
    rw [DirectoryPublication.Image.syncDirectory, ← valid.retained.walDirectorySettled]
  cases effect : failure.reported.effective <;>
    simp [RotationDirectoryFsyncFailure.cut, RotationCreateParent.cutAtBarrier, effect, State.visible,
      settled, liveState, SegmentedWriterState.rotated]

theorem liveRetained (failure : NativeRotationDirectoryFailure state (some cause)) (valid : state.Valid) :
    (failure.liveState valid).writer.RetainedReady state.session.directory state.session.descriptor :=
  valid.retained.rotates failure.parent.nonempty ⟨rfl, rfl, rfl⟩

end NativeRotationDirectoryFailure

/-- The protected lookups at the direct retry are in the same reached
namespace. Every selected payload refers to the actual failed barrier's
visible inode image. Its physical successor may still have had a crash
alternative before this next opener synchronizes the directory. -/
structure NativeRotationErrorFiles (failure : NativeRotationDirectoryFailure state (some cause)) (valid : state.Valid) where
  selected : NativeCloseFiles (failure.liveState valid)
  child : ∀ name, selected.names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
    (failure.reported.after.view.child failure.parent.root name).map failure.reported.after.view.modelObject
  bytes : ∀ inode payload, selected.bytes inode = some payload →
    failure.reported.after.inodes.visible inode = payload

theorem NativeRotationErrorFiles.successor
    {failure : NativeRotationDirectoryFailure state (some cause)} {valid : state.Valid}
    (files : NativeRotationErrorFiles failure valid) :
    files.selected.names (state.session.directory.file (.walSegment (state.writer.installed.walBytes / frameSize))) =
      some (failure.reported.effectInventory.inode failure.created.raw.description) := by
  obtain ⟨_, _, _, _, _, _, _, _, successor, object, _⟩ := failure.custody valid
  rw [DiskDirectory.walSegment_path, files.child, successor, Option.map_some, object]

/-- Successful explicit close feeds its reported slot drops into a direct
healthy aligned open on the same live files, with no intervening crash. -/
structure NativeRotationErrorReopenObservation (failure : NativeRotationDirectoryFailure state (some cause))
    (valid : state.Valid) (input : FilePath) where
  close : CachedCloseReports state.session.directory state.session.descriptor failure.closeState
  owner : close.slot = state.owner
  closed : close.result = .ok ()
  retiresAppend : ∀ entry ∈ state.cache.active, entry.2.2.1.closeEvent ∈ close.drops .active
  files : NativeRotationErrorFiles failure valid
  observe : ∀ plan : ClosedReadyReopenLayout (failure.liveState valid).writer (failure.liveState valid).releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint (failure.liveState valid).writer.published.durable
        (failure.liveState valid).releasedFiles.image.directory.active.manifest (failure.liveState valid).writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files.selected input close.finished.descriptors plan.layout selected)

/-- The exact returned error and close precede the next actual aligned
open. Its keeper read refers to the same live successor that the failed
rotation created and synced, even when its directory sync had no effect. -/
structure NativeRotationErrorReopenContinuation (current next : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state (some cause)} {input : FilePath}
    (observed : NativeRotationErrorReopenObservation failure current.readPrefix.refines.1 input) : Prop where
  stage : NativeReturnedRotationError current cause failure
  close : observed.close.run = .ok () observed.close.finished
  closed : observed.close.finished.phase = .closed
  files : observed.close.finished.files = ⟨(⟨none, none, []⟩, failure.reported.after),
    (failure.liveState current.readPrefix.refines.1).releasedFiles.owners⟩
  census : observed.close.finished.descriptors = failure.reported.effectInventory.afterDrops
    (observed.close.drops .active ++ observed.close.drops .pending ++ observed.close.drops .directory)
  activeClosed : ∀ entry ∈ current.state.cache.active, entry.2.2.1 ∉ observed.close.finished.descriptors.slots
  vacant : TryLockObserves observed.close.finished.files.owners current.state.session.directory (.ok true)
  lock : observed.close.bindings (current.state.session.directory.file .lock) =
    observed.files.selected.names (current.state.session.directory.file .lock)
  reads : next.reads = current.reads
  sessionRef : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseRef : next.state.session.phaseRef ≠ current.state.session.phaseRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  directoryInode : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  lockInode : next.state.census.inode next.state.owner.description =
    current.state.census.inode current.state.owner.description
  exactOpen :
    let live := failure.liveState current.readPrefix.refines.1
    ∃ (plan : ClosedReadyReopenLayout live.writer live.releasedFiles)
      (selected : SelectedIntegrityCheckpoint live.writer.published.durable
        live.releasedFiles.image.directory.active.manifest live.writer.checkpoint)
      (seen : NativeCloseAlignedReads observed.files.selected input observed.close.finished.descriptors plan.layout selected),
      next.opened = seen.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      next.state.files.image.directory.active = current.state.writer.target.pair ∧
      NativeCloseSelectedReads seen ∧
      plan.layout.keeper.first = current.state.writer.installed.walBytes / frameSize ∧
      plan.layout.keeper.bytes = ByteArray.empty ∧
      ∃ read : seen.opening.reads.reads.ObservesFile
        (current.state.session.directory.file (.walSegment plan.layout.keeper.first)) ByteArray.empty,
        read.object = failure.reported.effectInventory.inode failure.created.raw.description ∧
        failure.reported.after.inodes.visible read.object = ByteArray.empty

theorem NativeReadPosition.recoversRotationError (current : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state (some cause)} {input : FilePath}
    (observed : NativeRotationErrorReopenObservation failure current.readPrefix.refines.1 input) :
    ∃ next, NativeRotationErrorReopenContinuation current next observed := by
  let valid := current.readPrefix.refines.1
  let pending := current.rotationReturnsError cause failure
  have closed := observed.close.reaches (by rintro ⟨⟩) pending.ownerHeld
  rw [CachedCloseReports.Reached, observed.closed] at closed
  obtain ⟨closed, phase, cleared, census, vacant⟩ := closed
  have released := observed.files.selected.reopensReleasedAligned (failure.liveRetained valid)
    current.readPrefix.refines.2.1 pending.reads pending.bounded observed.observe
  obtain ⟨plan, selected, seen, next, seeded, path, owner, directorySlot, cache, afterCensus, sessionFresh,
    phaseFresh, lockObject, directoryObject, pair, kept, target, checkpoint, durable, manifestAbsent,
    manifest, runs, marker, wal, replay⟩ := released
  let reached : NativeReadPosition history log := ⟨seen.run, next, next, current.reads, seeded⟩
  have closeLock : observed.close.bindings (current.state.session.directory.file .lock) =
      observed.files.selected.names (current.state.session.directory.file .lock) := by
    rw [observed.close.lockObject, observed.owner]
    exact observed.files.selected.lock.symm
  have first : plan.layout.keeper.first = current.state.writer.installed.walBytes / frameSize :=
    (congrArg WalSegment.first plan.keeper).trans (valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm)
  have empty : plan.layout.keeper.bytes = ByteArray.empty := congrArg WalSegment.bytes plan.keeper
  obtain ⟨read, name, bytes⟩ := wal plan.layout.keeper (List.mem_append_right _ (List.mem_singleton_self _))
  have alias : observed.files.selected.names
      (current.state.session.directory.file (.walSegment plan.layout.keeper.first)) =
      some (failure.reported.effectInventory.inode failure.created.raw.description) :=
    first.symm ▸ observed.files.successor
  have inode := Option.some.inj (name.symm.trans alias)
  have exactBytes := observed.files.bytes _ _ bytes
  have activeClosed : ∀ entry ∈ current.state.cache.active, entry.2.2.1 ∉ observed.close.finished.descriptors.slots := by
    intro entry active stillLive
    rw [census] at stillLive
    have observedClose := List.mem_append_left (observed.close.drops .directory)
      (List.mem_append_left (observed.close.drops .pending) (observed.retiresAppend entry active))
    have remains := List.all_eq_true.mp (List.mem_filter.mp stillLive).2 _ observedClose
    simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes] at remains
  refine ⟨reached, pending, closed, phase, cleared, census, activeClosed, vacant, closeLock, rfl, sessionFresh, phaseFresh,
    checkpoint, durable,
    directoryObject.trans (congrFun pending.sameInodes _), lockObject.trans (congrFun pending.sameInodes _),
    plan, selected, seen, rfl, seeded.frames.1, cache, afterCensus, owner, directorySlot, ?_,
    ⟨manifestAbsent, manifest, runs, marker, wal⟩, first, empty, ?_⟩
  · exact pair.trans (failure.liveRetained valid).resumed.ready.selected
  · have sameObject {left right : ByteArray} (equal : left = right)
        (seenFile : seen.opening.reads.reads.ObservesFile
          (current.state.session.directory.file (.walSegment plan.layout.keeper.first)) left) :
        (equal ▸ seenFile : seen.opening.reads.reads.ObservesFile
          (current.state.session.directory.file (.walSegment plan.layout.keeper.first)) right).object = seenFile.object := by
      cases equal
      rfl
    refine ⟨empty ▸ read, ?_, ?_⟩
    · exact (sameObject empty read).trans inode
    · rw [sameObject empty read]
      exact exactBytes.trans empty

end Alvoki.Storage.DiskSession
