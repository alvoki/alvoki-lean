import Alvoki.Storage.Disk.NativeOpenCloseReopenTrace
import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}
  {initial current : NativeOpenedPosition opened} {input : FilePath}
  {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
  {directory : IO.Ref (Option IO.FS.Handle)}

/-- Interpret public close using the cells of the reached open handle. -/
def NativeOpenedPosition.closeOnOpenedCells (current : NativeOpenedPosition opened) (calls : OpenCloseCallbacks heap)
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle)) :
    EStateM.Result IO.Error heap Unit :=
  closeSchedule (opened.get opened.phase) (fun _ => calls.unlock opened.lock)
    (calls.set active none) (calls.set pending []) (calls.set directory none) (opened.set opened.phase .closed) current.reached

/-- The projected aligned reader fixes the next admission. The raw
append and flock begin on the heap returned by the preceding close,
and their reached heap supplies the directory-cache allocator. -/
structure RawAlignedReopenAdmission {state : NativeReadyState} {files : NativeCloseFiles state}
    {inventory : DescriptorInventory} {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable state.releasedFiles.image.directory.active.manifest
      state.writer.checkpoint}
    (reader : NativeCloseAlignedReads files input inventory layout selected) (view : OpenCloseHeapView heap FileImage)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap) (before : heap) where
  raw : RawOpenAdmissionReport reader.opening.admission view calls before
  seed : OpenSyncCacheAllocations reader.opening.admission.opened view init raw.afterFlock

namespace RawAlignedReopenAdmission

variable {state : NativeReadyState} {files : NativeCloseFiles state} {inventory : DescriptorInventory}
  {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable state.releasedFiles.image.directory.active.manifest
    state.writer.checkpoint}
  {reader : NativeCloseAlignedReads files input inventory layout selected} {view : OpenCloseHeapView heap FileImage}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap} {before : heap}

/-- The production admission and cache prefix of the aligned reopen.
The caller supplies the subsequent held worker. -/
def run (_admitted : RawAlignedReopenAdmission reader view calls init before)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    EStateM.Result IO.Error heap α :=
  DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend (fun resolved lock =>
    openWithLock (calls.flock lock) (fun _ => IO.userError s!"database already open: {resolved.path}")
      (fun _ => calls.unlock lock) fun _ => do
        let cache ← openSyncFilesWith (init.openDirectory resolved.path) init.newRef init.newRef init.newRef makeCache
        recovery resolved lock cache) before

end RawAlignedReopenAdmission

/-- A successful public close hands its actual returned heap to the
next aligned opener. The raw admission takes the same lock inode,
initializes the cache on the flock's returned heap and starts the held
continuation there. The projected reader retains the checkpoint, WAL
and client replay of the same next open. -/
theorem NativeOpenedTrace.closesThenAdmitsAligned
    (prior : NativeOpenedTrace initial instructions events current)
    (references : opened.files.UsesCacheReferences active pending directory)
    (view : OpenCloseHeapView heap FileImage) (closeCalls : OpenCloseCallbacks heap)
    (samePhase : view.phase = opened.contents) (sameGet : closeCalls.getPhase = opened.get)
    (sameSet : @closeCalls.set (Phase Installed) = opened.set)
    (observed : NativeCloseReopenObservation current.current.ready.state input)
    (close : OpenCloseObservation observed.close.report view closeCalls opened.lock opened.phase
      active pending directory current.reached) (success : observed.close.report.result = .ok ())
    (openCalls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (observe : ∀ after, current.closeOnOpenedCells closeCalls active pending directory = .ok () after →
      ∀ (plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles)
        (selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
          current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint)
        (reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected),
        Nonempty (RawAlignedReopenAdmission reader view openCalls init after)) :
    let state := current.current.ready.state
    opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (active.set none) (pending.set []) (directory.set none) (opened.phase.set .closed) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (after : heap) (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint)
      (reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected)
      (admitted : RawAlignedReopenAdmission reader view openCalls init after)
      (cache : DiskTable.OpenSyncFiles) (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      current.closeOnOpenedCells closeCalls active pending directory = .ok () after ∧
      opened.contents after opened.phase = some .closed ∧
      view.cacheAt after directory active pending = ⟨none, none, []⟩ ∧
      view.files after = state.releasedFiles ∧ view.descriptors after = observed.inventory ∧
      reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      NativeCloseSelectedReads reader ∧ NativeCloseReopenStep current.current.ready observed next ∧
      NativeExecutionTrace initial.current (events ++ [.closedAndReopened input (.ok ())])
        ⟨current.current.history, current.current.submissions, next⟩ ∧
      cache.UsesCacheReferences admitted.seed.activeRef admitted.seed.pendingRef admitted.seed.directoryRef ∧
      cache.AtDirectory state.session.directory.path ∧
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      (view.handle admitted.raw.afterFlock admitted.raw.lock).1.inode
          (view.handle admitted.raw.afterFlock admitted.raw.lock).2.1.description = state.census.inode state.owner.description ∧
      (view.descriptors admitted.seed.afterPending).inode reader.opening.admission.cached.description =
        state.census.inode state.directorySlot.description ∧
      view.cacheAt admitted.seed.afterPending admitted.seed.directoryRef admitted.seed.activeRef admitted.seed.pendingRef =
        reader.opening.admission.cache ∧
      (view.descriptors admitted.seed.afterPending, view.files admitted.seed.afterPending) =
        (reader.opening.admission.reached, reader.opening.admission.held) ∧
      ∀ {α : Type} (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α),
        admitted.run makeCache recovery =
          (tryCatchThe IO.Error (recovery state.session.directory admitted.raw.lock cache) fun cause => do
            openCalls.unlock admitted.raw.lock
            throw cause) admitted.seed.afterPending := by
  intro state
  obtain ⟨source, next, reopened, trace, physical⟩ :=
    prior.closesAndReopens references view closeCalls samePhase sameGet sameSet observed close
  rw [success] at trace physical
  obtain ⟨after, returned, closed, cleared, files, census⟩ := physical
  obtain ⟨plan, selected, reader, nextReturned, nextOpened, _, _, _, _, _, reads⟩ := reopened.exactOpen
  obtain ⟨admitted⟩ := observe after returned plan selected reader
  obtain ⟨cache, makeCache, cacheOpen, cacheAction, cacheSource, cacheRefs, cachePath, lockHandle,
    _, _, cacheProjection, atHold, admittedRun⟩ := admitted.raw.admitsWithCache init admitted.seed
  refine ⟨source, next, after, plan, selected, reader, admitted, cache, cacheOpen, makeCache, returned, closed, cleared,
    files, census, nextOpened.symm, nextOpened.trans nextReturned, reads, reopened, trace, cacheRefs, cachePath,
    cacheAction, cacheSource, ?_, ?_,
    cacheProjection, atHold, admittedRun⟩
  · rw [lockHandle]
    exact reader.admission.lockObject
  · have censusAtHold : view.descriptors admitted.seed.afterPending = reader.opening.admission.reached :=
      congrArg Prod.fst atHold
    rw [censusAtHold]
    exact reader.opening.admission.opened.captures.2.2.2.2.1.symm.trans reader.admission.directoryObject

end Alvoki.Storage.DiskSession
