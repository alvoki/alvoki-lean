import Alvoki.Storage.Disk.Proofs.Read.NativeReadyReadPrefix
import Alvoki.Storage.Disk.Proofs.Session.ClientCachedClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeReadyState

/-- Read the reached session phase and pass its exact cache and census
to the shared native close schedule. -/
def closeState (state : NativeReadyState) : CachedCloseState CheckpointOpenHandle FileImage :=
  ⟨state.session.phase, ⟨(state.cache, state.files.image), state.files.owners⟩, state.census⟩

def releasedFiles (state : NativeReadyState) : LockedFileState FileImage :=
  ⟨state.files.image, state.files.owners.set (state.session.directory.file .lock) none⟩

end NativeReadyState

/-- The unlock callback receives the exact slot retained by the ready
session. The report enumerates the observed effects of the cache clears. -/
structure NativeReadyClose (state : NativeReadyState) where
  report : CachedCloseReports state.session.directory state.session.descriptor state.closeState
  owner : report.slot = state.owner

namespace NativeReadyClose

variable {state : NativeReadyState}

theorem reaches (close : NativeReadyClose state) (valid : state.Valid) : close.report.Reached :=
  close.report.reaches (by simp [NativeReadyState.closeState, valid.phase]) valid.retained.held

theorem failed (close : NativeReadyClose state) (valid : state.Valid)
    {cause : IO.Error} (failure : close.report.result = .error cause) :
    close.report.run = .error cause state.closeState := by
  have reached := close.reaches valid
  simp only [CachedCloseReports.Reached, failure] at reached
  exact reached.1

theorem closes (close : NativeReadyClose state) (valid : state.Valid)
    (success : close.report.result = .ok ()) :
    close.report.run = .ok () close.report.finished ∧ close.report.finished.phase = .closed ∧
    close.report.finished.files = ⟨(⟨none, none, []⟩, state.files.image), state.releasedFiles.owners⟩ ∧
    close.report.finished.descriptors = state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    TryLockObserves state.releasedFiles.owners state.session.directory (.ok true) := by
  have reached := close.reaches valid
  simp only [CachedCloseReports.Reached, success, NativeReadyState.closeState] at reached
  obtain ⟨returned, phase, files, census, vacant⟩ := reached
  rw [files] at vacant
  exact ⟨returned, phase, files, census, vacant⟩

/-- A failed explicit unlock keeps the starting cache and owner in the
returned error. Later ordered slot events release authority only when
the whole observed description is unreferenced. -/
theorem followsFailedUnlock (close : NativeReadyClose state) (valid : state.Valid)
    {cause : IO.Error} (failure : close.report.result = .error cause)
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    (drops : LockCensusTrace state.session.directory state.session.descriptor state.census state.files inventory retry) :
    close.report.run = .error cause state.closeState ∧
    inventory.inode = state.census.inode ∧
    retry = (if inventory.references state.session.descriptor = [] then state.releasedFiles else state.files) ∧
    (TryLockObserves retry.owners state.session.directory (.ok true) ↔
      inventory.references state.session.descriptor = []) :=
  ⟨close.failed valid failure, drops.reached.2.1, drops.reached.2.2, drops.freshFlockAllowed⟩

end NativeReadyClose

/-- The next native admission starts from the reported census and file
state. Stable object identities relate its separately issued opens back
to the previous ready owner and captured directory. -/
structure NativeCloseAdmission (state : NativeReadyState) (input : FilePath)
    (inventory : DescriptorInventory) (retry : LockedFileState FileImage) where
  admission : CensusOpenAdmissionReports input state.session.directory inventory retry
  distinct : admission.owner.description ≠ state.session.descriptor
  distinctCached : admission.cached.description ≠ state.session.descriptor
  lockObject : inventory.inode admission.owner.description = state.census.inode state.owner.description
  directoryObject : admission.view.modelObject admission.root = state.census.inode state.directorySlot.description

namespace NativeReadyReadPrefix

variable {state : NativeReadyState}

/-- Both native close outcomes extend the exact ready-read prefix on
the returned session, and preserve the same client key-value replay. -/
theorem reachesClose (observed : NativeReadyReadPrefix opened initial history log reads state)
    (close : NativeReadyClose state) :
    opened = .ok initial.session (initial.census, initial.files) ∧
    state.closeState.files = ⟨(initial.cache, initial.files.image), initial.files.owners⟩ ∧
    state.closeState.descriptors = initial.census ∧ close.report.slot = initial.owner ∧
    close.report.Reached ∧ PendingClientReplay log reads history := by
  obtain ⟨returned, files, census, cache, _, _, owner, _⟩ := observed.frames
  refine ⟨returned, ?_, census, close.owner.trans owner, close.reaches observed.refines.1, observed.refines.2.2⟩
  simp only [NativeReadyState.closeState, files, cache]

/-- Reported success clears the exact reached cache, preserves the
selected files and makes the lock vacant even if old references remain.
The next reported native admission allocates its own lock and cache. -/
theorem closeAdmits (observed : NativeReadyReadPrefix opened initial history log reads state)
    (close : NativeReadyClose state) (success : close.report.result = .ok ())
    {input : FilePath} (next : NativeCloseAdmission state input close.report.finished.descriptors state.releasedFiles)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error CensusOpenState result) :
    close.report.run = .ok () close.report.finished ∧ close.report.finished.phase = .closed ∧
    close.report.finished.files = ⟨(⟨none, none, []⟩, state.files.image), state.releasedFiles.owners⟩ ∧
    close.report.finished.descriptors = state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    TryLockObserves state.releasedFiles.owners state.session.directory (.ok true) ∧
    next.admission.reached.inode next.admission.owner.description = state.census.inode state.owner.description ∧
    next.admission.reached.inode next.admission.cached.description = state.census.inode state.directorySlot.description ∧
    next.admission.run recover =
      (tryCatchThe IO.Error (recover state.session.directory next.admission.owner next.admission.cache) fun cause => do
        next.admission.unlock next.admission.owner ()
        throw cause) (next.admission.reached, next.admission.held) ∧ PendingClientReplay log reads history := by
  obtain ⟨returned, phase, files, census, vacant⟩ := close.closes observed.refines.1 success
  have captured := next.admission.opened.captures.2.2.2.2.1
  exact ⟨returned, phase, files, census, vacant, next.lockObject, captured.symm.trans next.directoryObject,
    next.admission.run_reachesRecovery recover, observed.refines.2.2⟩

/-- Failed unlock takes the later reference-drop edge from the exact
error return. The last reference opens admission on the same selected
files and original objects. Recovery still has its native unlock handler. -/
theorem dropAdmitsAfterFailedClose (observed : NativeReadyReadPrefix opened initial history log reads state)
    (close : NativeReadyClose state) {cause : IO.Error} (failure : close.report.result = .error cause)
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    (drops : LockCensusTrace state.session.directory state.session.descriptor state.census state.files inventory retry)
    (last : inventory.references state.session.descriptor = [])
    {input : FilePath} (next : NativeCloseAdmission state input inventory retry)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error CensusOpenState result) :
    close.report.run = .error cause state.closeState ∧ retry = state.releasedFiles ∧
    TryLockObserves retry.owners state.session.directory (.ok true) ∧
    ReportedReopenPrefix state.session.directory state.writer.wal.active.first state.files retry ∧
    next.admission.reached.references state.session.descriptor = [] ∧
    next.admission.reached.references next.admission.owner.description = [next.admission.owner.reference] ∧
    next.admission.reached.inode next.admission.owner.description = state.census.inode state.owner.description ∧
    next.admission.reached.inode next.admission.cached.description = state.census.inode state.directorySlot.description ∧
    next.admission.run recover =
      (tryCatchThe IO.Error (recover state.session.directory next.admission.owner next.admission.cache) fun cause => do
        next.admission.unlock next.admission.owner ()
        throw cause) (next.admission.reached, next.admission.held) ∧ PendingClientReplay log reads history := by
  obtain ⟨returned, _, files, _⟩ := close.followsFailedUnlock observed.refines.1 failure drops
  have lockObject : inventory.inode next.admission.owner.description = state.census.inode state.session.descriptor := by
    rw [← observed.refines.1.owner]
    exact next.lockObject
  obtain ⟨retried, vacant, owned, _, empty, _, root, ran⟩ :=
    drops.capturesAfterAdmission (.start : ReportedReopenPrefix state.session.directory state.writer.wal.active.first
      state.files state.files) last next.admission next.distinct next.distinctCached lockObject recover
  exact ⟨returned, by simpa only [last, ite_true] using files, vacant, retried, empty, owned, next.lockObject,
    root.symm.trans next.directoryObject, ran, observed.refines.2.2⟩

end NativeReadyReadPrefix

end Alvoki.Storage.DiskSession
