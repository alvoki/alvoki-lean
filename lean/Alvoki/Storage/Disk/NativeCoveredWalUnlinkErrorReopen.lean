import Alvoki.Storage.Disk.NativeCoveredWalUnlinkError
import Alvoki.Storage.Disk.Proofs.Collection.NativeCollectionErrorReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {state : NativeReadyState}

namespace NativeCoveredWalUnlinkError

/-- The failed unlink leaves these exact files under the held old lock. -/
def collected (error : NativeCoveredWalUnlinkError state) : NativeCollectedWal state :=
  ⟨error.after, error.census, error.inventory.lifetime.root, error.afterView,
    error.inventory.lifetime.lock, error.retainsLock.1, error.retainsLock.2, error.retainsDirectory⟩

end NativeCoveredWalUnlinkError

/-- The close starts with the exact poisoned return of the ordered
unlink schedule. The next marked opener uses its released census and
reads the remaining seals in the same directory. -/
structure NativeCoveredWalUnlinkErrorReopen (state : NativeReadyState) (input : FilePath) where
  error : NativeCoveredWalUnlinkError state
  close : CachedCloseReports state.session.directory state.session.descriptor error.closeState
  owner : close.slot = state.owner
  closed : close.result = .ok ()
  files : NativeCollectionCloseFiles error.collected
  reopen : ∀ selected : CoveredWalRetrySelection state.writer error.after.visible,
    Nonempty (NativeCollectionAlignedReads files input close.finished.descriptors selected)

/-- An ordinary unlink error, the exact close of its poisoned session,
and the next marked return preserve the original read history. -/
structure NativeCoveredWalUnlinkErrorContinuation (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCoveredWalUnlinkErrorReopen current.state input) (next : NativeReadPosition history log) : Prop where
  failed : NativeReturnedCoveredWalUnlinkError current observed.error
  closed : observed.close.run = .ok () observed.close.finished ∧ observed.close.finished.phase = .closed ∧
    observed.close.finished.files =
      ⟨(⟨none, none, []⟩, observed.error.after), observed.error.collected.released.owners⟩ ∧
    observed.close.finished.descriptors = observed.error.census.afterDrops
      (observed.close.drops .active ++ observed.close.drops .pending ++ observed.close.drops .directory) ∧
    observed.close.bindings (current.state.session.directory.file .lock) = observed.files.names (current.state.session.directory.file .lock)
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  pair : next.state.files.image.directory.active = current.state.writer.target.pair
  seals : next.state.files.image.kept = observed.error.collected.released.image.kept
  exactOpen : ∃ (selection : CoveredWalRetrySelection current.state.writer observed.error.after.visible)
    (seen : NativeCollectionAlignedReads observed.files input observed.close.finished.descriptors selection),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    seen.opening.reads.bindings current.state.session.directory.path =
      some (observed.error.afterView.modelObject observed.error.inventory.lifetime.root) ∧
    NativeCollectionSelectedReads seen

theorem NativeReadPosition.recoversCoveredWalUnlinkError (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCoveredWalUnlinkErrorReopen current.state input) :
    ∃ next, NativeCoveredWalUnlinkErrorContinuation current observed next := by
  have failed := current.returnsCoveredWalUnlinkError observed.error
  obtain ⟨selection⟩ := failed.visible
  obtain ⟨closed, phase, cleared, afterClose, closeLock, seen, state, readPrefix, cache, census, owner,
    directorySlot, directory, phaseFresh, sessionFresh, lockInode, directoryInode, pair, seals, target, checkpoint, durable,
    physical, _⟩ := current.readPrefix.reopensCollectedWal observed.error.collected observed.close observed.owner
      observed.closed observed.files selection observed.reopen
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, readPrefix⟩
  have entryInodes := congrArg DescriptorInventory.inode observed.error.sameCensus
  have frame : NativeReadRecoveryFrame current.state next.state :=
    ⟨directory, directoryInode.trans (congrFun entryInodes _), lockInode.trans (congrFun entryInodes _),
      target.trans (selection.sameTarget current.readPrefix.refines.1.retained), checkpoint, durable⟩
  exact ⟨next, failed, ⟨closed, phase, cleared, afterClose, closeLock⟩, rfl, frame, phaseFresh, sessionFresh,
    pair, seals, selection, seen, readPrefix.frames.1, rfl, rfl, owner, directorySlot, cache, census,
    seen.directoryObject.trans observed.files.directoryAtRoot, physical⟩

end Alvoki.Storage.DiskSession
