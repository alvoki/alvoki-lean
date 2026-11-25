import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

/-- Report the machine restart between two reached heaps. The old heap
provides the selected live name bindings. The reboot heap provides the
chosen survivor's bindings and durable payloads at those paths. -/
structure RawQuietRebootEntry {heap : Type} {state : NativeReadyState}
    (crash : NativeReadyQuietCrash state) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (before after : heap) : Prop where
  previous : (view.descriptors before, view.files before) = (state.census, state.files)
  liveNames : ∀ path, state.crashPath path → names before path = crash.live.names path
  survivorNames : ∀ path, state.crashPath path → names after path = crash.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
    ∀ inode, crash.names path = some inode → bytes after inode = crash.contents inode

/-- Every selected file in this reader comes from the reported reboot
heap, with the same inode and durable bytes. -/
theorem RawQuietRebootEntry.readsSurvivingFile {heap : Type} {state : NativeReadyState}
    {crash : NativeReadyQuietCrash state} {view : OpenCloseHeapView heap FileImage}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray} {before after : heap}
    (entry : RawQuietRebootEntry crash view names bytes before after) {input : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash input layout selected} {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (observed : reader.ReadsSurvivor path payload) :
    ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names after path = some read.object ∧ bytes after read.object = payload := by
  obtain ⟨read, bound, durable⟩ := observed
  exact ⟨read, (entry.survivorNames path (.inr (.inr selectedPath))).trans bound,
    (entry.survivorBytes path selectedPath read.object bound).trans durable⟩

/-- The admitted lock and cache for one aligned reader start at the same
observed reboot heap and use its selected filesystem survivor. -/
structure RawQuietRestartAdmission {heap : Type} {state : NativeReadyState}
    {crash : NativeReadyQuietCrash state} {input : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    (reader : NativeReadyRestartReads crash input layout selected) (view : OpenCloseHeapView heap FileImage)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (before after : heap) where
  reboot : RawQuietRebootEntry crash view names bytes before after
  raw : RawOpenAdmissionReport reader.opening.admission view calls after
  seed : OpenSyncCacheAllocations reader.opening.admission.opened view init raw.afterFlock

/-- The reported quiet reboot discards the old census. The exact raw
next admission captures the surviving lock and directory before it
passes the same initialized cache to the marked worker. The single
selected chronological reader accounts for the surviving bytes and the
modeled next replay, including the earlier client's reads. -/
theorem RawQuietRestartAdmission.admits
    {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (crash : NativeReadyQuietCrash current.current.ready.state)
    {input : FilePath} {layout : CanonicalKeeperLayout crash.retry.image current.current.ready.state.writer.history}
    (target : layout.target = current.current.ready.state.writer.target)
    (keeper : layout.keeper = current.current.ready.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] =
      current.current.ready.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first)
      layout.range.watermark = some (layout.first,
        (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    {selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.current.ready.state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash input layout selected}
    {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
    {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    {after : heap} (admitted : RawQuietRestartAdmission reader view calls init names bytes current.reached after) :
    let directory := current.current.ready.state.session.directory
    (view.descriptors after, view.files after) = (crash.reboot, crash.retry) ∧ (view.descriptors after).slots = [] ∧
    BoundedReopenTrace directory (· = current.current.ready.state.writer.target)
      current.current.ready.state.files crash.retry ∧
    ∃ (next : NativeReadyState) (cache : DiskTable.OpenSyncFiles) (action : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      reader.ReachedSession next current.current.history current.current.submissions current.current.ready.reads ∧
      cache.UsesCacheReferences admitted.seed.activeRef admitted.seed.pendingRef admitted.seed.directoryRef ∧
      cache.AtDirectory directory.path ∧ DiskTable.OpenSyncFiles.IsOpenAction directory.path action ∧
      action = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      names after (directory.file .lock) = some ((view.handle admitted.raw.afterFlock admitted.raw.lock).1.inode
        (view.handle admitted.raw.afterFlock admitted.raw.lock).2.1.description) ∧
      names after directory.path = some ((view.descriptors admitted.seed.afterPending).inode
        reader.opening.admission.cached.description) ∧
      view.cacheAt admitted.seed.afterPending admitted.seed.directoryRef admitted.seed.activeRef admitted.seed.pendingRef =
        reader.opening.admission.cache ∧
      (view.descriptors admitted.seed.afterPending, view.files admitted.seed.afterPending) =
        (reader.opening.admission.reached, reader.opening.admission.held) ∧
      ∀ {α : Type} (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α),
        calls.runOpen input init makeCache recover after =
          (tryCatchThe IO.Error (recover directory admitted.raw.lock cache) fun cause => do
            calls.unlock admitted.raw.lock
            throw cause) admitted.seed.afterPending := by
  intro directory
  obtain ⟨valid, history, pending⟩ := current.current.ready.readPrefix.refines
  obtain ⟨lost, next, reached⟩ := crash.restartsAt valid history pending current.current.ready.readPrefix.readsBounded
    layout target keeper descriptors offsets prepared selected reader
  obtain ⟨cache, makeCache, action, isOpen, source, references, atPath, lock, _, _, cacheAt, atHold, run⟩ :=
    admitted.raw.admitsWithCache init admitted.seed
  have sameLock := reader.opening.reads.sameObjects.2.1.symm.trans reader.lockObject
  have sameDirectory := reader.opening.reads.sameObjects.1.symm.trans reader.directoryObject
  refine ⟨Prod.ext admitted.raw.entryCensus admitted.raw.entryFiles, ?_, lost,
    next, cache, action, makeCache, reached, references, atPath, isOpen, source, ?_, ?_, cacheAt, atHold, run⟩
  · rw [admitted.raw.entryCensus]
    rfl
  · rw [lock]
    exact (admitted.reboot.survivorNames _ (.inr (.inl rfl))).trans sameLock.symm
  · have census : view.descriptors admitted.seed.afterPending = reader.opening.admission.reached :=
      congrArg Prod.fst atHold
    rw [census]
    exact (admitted.reboot.survivorNames _ (.inl rfl)).trans sameDirectory.symm

end Alvoki.Storage.DiskSession
