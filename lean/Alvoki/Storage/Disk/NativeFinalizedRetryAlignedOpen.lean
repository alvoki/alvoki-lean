import Alvoki.Storage.Disk.NativeAlignedCloseTableOpen
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {state : NativeReadyState}
  {files : NativeCloseFiles state} {inventory : DescriptorInventory}
  {plan : ClosedReadyReopenLayout state.writer state.releasedFiles}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
  {reader : NativeCloseAlignedReads files input inventory plan.layout selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {release : IO.FS.Handle → heap → heap} {first before : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- Follow finalized read-only open errors by a healthy aligned open
from the last caller-visible heap. The same file image and description
map supply the chosen raw reader, and the actual returned table starts
with the earlier client ledger and fresh snapshot pins. -/
theorem RawFinalizedOpenAttempts.reopensAligned
    {errors : List (FilePath × IO.Error)}
    (attempts : RawFinalizedOpenAttempts view state.session.directory calls init release first errors before)
    (retained : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (pending : PendingClientReplay log recorded state.writer.history)
    (bounded : ∀ read ∈ recorded, read.BoundedBy state.writer.history.length)
    (seen : RawAlignedReopenEffects reader view calls init before phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (compare : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    (view.files first).image = state.releasedFiles.image ∧
    (view.descriptors first).inode = inventory.inode ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      handle.lock = seen.admission.raw.lock ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = compare ∧
      start.current.history = state.writer.history ∧ start.current.submissions = log ∧
      start.current.ready.reads = recorded ∧ start.pins = [] ∧
      InstalledClientReplay log recorded state.writer.history start.current.ready.state.writer.installed
        start.current.ready.state.session := by
  obtain ⟨inodes, files⟩ := attempts.preserves
  obtain ⟨installed, cacheOpen, makeCache, canonical, source, returned⟩ :=
    seen.opens retained pending bounded remove write rename bootstrap assemble constructs
  obtain ⟨handle, start, table, _, lock, _, _, _, phase, getter, setter, compared, reached, _, history, submissions, reads, pins⟩ :=
    installed.fromOpen get set effects compare
  refine ⟨files.symm.trans (congrArg LockedFileState.image seen.admission.raw.entryFiles),
    inodes.symm.trans (congrArg DescriptorInventory.inode seen.admission.raw.entryCensus),
    cacheOpen, makeCache, handle, start, canonical, source, ?_, lock, phase, getter, setter, compared,
    history, submissions, reads, pins, ?_⟩
  · simpa only [table, reached] using returned
  · rw [← submissions, ← reads, ← history]
    exact start.current.ready.readPrefix.guardedReplay

end Alvoki.Storage.DiskSession
