import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenCacheReferences
import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeRawSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

inductive BootstrapPendingFile where
  | keeper
  | marker

def BootstrapPendingFile.path (directory : DiskDirectory) : BootstrapPendingFile → FilePath
  | .keeper => directory.file (.walSegment 0)
  | .marker => directory.file .stagedWalBoundary

structure BootstrapPendingCalls (heap : Type) extends RawSyncCalls heap where
  create : FilePath → EStateM IO.Error heap IO.FS.Handle
  stage : FilePath → ByteArray → EStateM IO.Error heap IO.FS.Handle
  remember : IO.Ref (List (FilePath × IO.FS.Handle)) →
    (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit

def BootstrapPendingCalls.produces (calls : BootstrapPendingCalls heap) (directory : DiskDirectory) :
    BootstrapPendingFile → EStateM IO.Error heap IO.FS.Handle
  | .keeper => calls.create (directory.file (.walSegment 0))
  | .marker => calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0)

/-- Each file barrier reads and removes the only pending entry before
issuing fsync on its exact handle. Return observations supply the
reached heap even when that fsync returns an error. -/
structure BootstrapPendingObservation (view : OpenCloseHeapView heap image) (calls : BootstrapPendingCalls heap)
    (directory : DiskDirectory) (file : BootstrapPendingFile) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (expected : CheckpointOpenHandle) (before : heap) where
  handle : IO.FS.Handle
  produced : heap
  recorded : heap
  consumed : heap
  reached : heap
  result : Except IO.Error Unit
  returnedHandle : calls.produces directory file before = .ok handle produced
  sameProduced : view.handle produced handle = expected
  previouslyEmpty : view.pending produced pending = []
  remembered : calls.remember pending (pushPending (file.path directory) handle) produced = .ok () recorded
  recordedValue : view.pending recorded pending = pushPending (file.path directory) handle (view.pending produced pending)
  pendingRead : calls.readPending pending recorded = .ok (view.pending recorded pending) recorded
  removed : calls.setPending pending ((view.pending recorded pending).filter (fun entry => entry.1 != file.path directory))
    recorded = .ok () consumed
  consumedValue : view.pending consumed pending = (view.pending recorded pending).filter (fun entry => entry.1 != file.path directory)
  sameIssuing : view.handle consumed handle = expected
  syncReturned : calls.fsync handle consumed = match result with
    | .ok () => .ok () reached
    | .error cause => .error cause reached
  pendingKept : view.pending reached pending = view.pending consumed pending

namespace BootstrapPendingObservation

variable {view : OpenCloseHeapView heap image} {calls : BootstrapPendingCalls heap} {directory : DiskDirectory}
  {file : BootstrapPendingFile} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
  {expected : CheckpointOpenHandle} {before : heap}

/-- The production cache callbacks for this file issue on the captured
pending cell. No directory-cell read, active lookup or fallback
open is reached at this file barrier. -/
theorem returns (seen : BootstrapPendingObservation view calls directory file pending expected before)
    (cache : DiskTable.OpenSyncFiles) {active cachedDirectory}
    (uses : cache.UsesCacheReferences active pending cachedDirectory) (path : cache.AtDirectory directory.path) :
    cache.UsesBootstrapCacheSchedules directory active pending cachedDirectory ∧
    (do
      let handle ← calls.produces directory file
      calls.remember pending (pushPending (file.path directory) handle) : EStateM IO.Error heap Unit)
      before = .ok () seen.recorded ∧
    calls.toRawSyncCalls.group directory.path cachedDirectory active pending
      #[file.path directory] seen.recorded =
        (match seen.result with
          | .ok () => .ok () seen.reached
          | .error cause => .error (IO.userError s!"sync failed for '{file.path directory}': {cause}") seen.reached) ∧
    view.pending seen.recorded pending = [(file.path directory, seen.handle)] ∧
    view.pending seen.consumed pending = [] ∧ view.pending seen.reached pending = [] ∧
    view.handle seen.consumed seen.handle = view.handle seen.produced seen.handle := by
  have one : view.pending seen.recorded pending = [(file.path directory, seen.handle)] := by
    rw [seen.recordedValue, seen.previouslyEmpty]
    rfl
  have empty : view.pending seen.consumed pending = [] := by
    simp only [seen.consumedValue, one, List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨cache.bootstrapCacheSchedules uses path, ?_, ?_, one, empty, seen.pendingKept.trans empty,
    seen.sameIssuing.trans seen.sameProduced.symm⟩
  · simp only [Bind.bind, EStateM.bind, seen.returnedHandle, seen.remembered]
  · have separate : file.path directory ≠ directory.path := by
      cases file
      · exact file_ne_directory directory (.walSegment 0)
      · exact file_ne_directory directory .stagedWalBoundary
    let refs : OpenSyncCacheRefs cache directory.path := ⟨cachedDirectory, active, pending, uses, path⟩
    have selected : (view.pending seen.recorded pending).find? (fun entry => entry.1 == file.path directory) =
        some (file.path directory, seen.handle) := by simp [one]
    have synced := calls.toRawSyncCalls.syncPending refs separate seen.pendingRead selected seen.removed
    rw [RawSyncCalls.group, SyncPathGroup.run_single]
    dsimp only [refs] at synced
    rw [synced, seen.syncReturned]
    cases seen.result with
    | ok value => cases value; rfl
    | error => rfl

end BootstrapPendingObservation

end Alvoki.Storage.DiskSession
