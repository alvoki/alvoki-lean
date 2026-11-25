import Alvoki.Storage.Disk.BatchCutReopenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WAL.Boundary

/-- A cache reference cleared by close. Kernel slot drops are separately
observed at each clear. -/
inductive CloseCacheField where
  | active
  | pending
  | directory

structure CachedCloseState (handle image : Type) where
  phase : Phase Installed
  files : LockedFileState (Cache handle × image)
  descriptors : DescriptorInventory

def CachedCloseState.drop (before : CachedCloseState handle image) (field : CloseCacheField)
    (drops : List LockReferenceDrop) : CachedCloseState handle image :=
  let cache := before.files.image.1
  let cache := match field with
    | .active => { cache with active := none }
    | .pending => { cache with pending := [] }
    | .directory => { cache with directory := none }
  { before with
    files := { before.files with image := (cache, before.files.image.2) }
    descriptors := before.descriptors.afterDrops drops }

def CachedCloseState.release (before : CachedCloseState handle image) (directory : DiskDirectory)
    (writer : Nat) : CachedCloseState handle image :=
  { before with files := { before.files with owners := before.files.owners.release (directory.file .lock) writer } }

/-- Observe the live lock slot and each reached cache reference clear.
The drop lists record the native slot effects. Each clear's report also
frames the reached file contents. -/
structure CachedCloseReports {handle image : Type} (directory : DiskDirectory) (writer : Nat)
    (before : CachedCloseState handle image) where
  slot : DescriptorSlot
  live : slot ∈ before.descriptors.slots
  description : slot.description = writer
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (before.descriptors.inode slot.description)
  unlock : DescriptorSlot → EStateM IO.Error (CachedCloseState handle image) Unit
  clear : CloseCacheField → EStateM IO.Error (CachedCloseState handle image) Unit
  result : Except IO.Error Unit
  unlockEffect : unlock slot before = match result with
    | .ok () => .ok () (before.release directory writer)
    | .error cause => .error cause before
  drops : CloseCacheField → List LockReferenceDrop
  active : result = .ok () →
    clear .active (before.release directory writer) =
      .ok () ((before.release directory writer).drop .active (drops .active))
  pending : result = .ok () →
    let active := (before.release directory writer).drop .active (drops .active)
    clear .pending active = .ok () (active.drop .pending (drops .pending))
  directoryCache : result = .ok () →
    let active := (before.release directory writer).drop .active (drops .active)
    let pending := active.drop .pending (drops .pending)
    clear .directory pending = .ok () (pending.drop .directory (drops .directory))

namespace CachedCloseReports

variable {handle image : Type} {directory : DiskDirectory} {writer : Nat}
  {before : CachedCloseState handle image}

def run (report : CachedCloseReports directory writer before) :
    EStateM.Result IO.Error (CachedCloseState handle image) Unit :=
  closeSchedule (fun reached => .ok reached.phase reached)
    (fun _ => report.unlock report.slot) (report.clear .active) (report.clear .pending) (report.clear .directory)
    (fun reached => .ok () { reached with phase := .closed }) before

def finished (report : CachedCloseReports directory writer before) : CachedCloseState handle image :=
  let active := (before.release directory writer).drop .active (report.drops .active)
  let pending := active.drop .pending (report.drops .pending)
  { pending.drop .directory (report.drops .directory) with phase := .closed }

/-- The shared close schedule clears active, pending and directory
references in order after successful unlock. An unlock error leaves the
poisoned phase, cache, files, slots and ownership at the reached state. -/
theorem outcome (report : CachedCloseReports directory writer before) (poisoned : before.phase = .poisoned) :
    report.run = match report.result with
    | .ok () => .ok () report.finished
    | .error cause => .error cause before := by
  unfold run closeSchedule
  simp only [Bind.bind, EStateM.bind, poisoned, Phase.close]
  cases returned : report.result with
  | error cause =>
    have unlock := report.unlockEffect
    rw [returned] at unlock
    rw [unlock]
  | ok value =>
    cases value
    have unlock := report.unlockEffect
    rw [returned] at unlock
    simp only [unlock, report.active returned, report.pending returned, report.directoryCache returned, finished]

theorem finishedFiles (report : CachedCloseReports directory writer before)
    (held : before.files.owners.Owns directory writer) :
    report.finished.files =
      ⟨(⟨none, none, []⟩, before.files.image.2), before.files.owners.set (directory.file .lock) none⟩ := by
  simp only [finished, CachedCloseState.drop, CachedCloseState.release, LockOwners.release_owned held]

/-- An explicit unlock can release authority while its descriptor slot
remains live. Slot survival follows from the measured drops at the three
cache clears. -/
theorem lockSlotAfterClears (report : CachedCloseReports directory writer before)
    (poisoned : before.phase = .poisoned) (successful : report.result = .ok ())
    (retained : ∀ field, ∀ drop ∈ report.drops field, drop.removes report.slot.reference = false) :
    report.run = .ok () report.finished ∧ report.slot ∈ report.finished.descriptors.slots ∧
      report.bindings (directory.file .lock) = some (report.finished.descriptors.inode writer) := by
  refine ⟨by rw [report.outcome poisoned, successful], ?_, ?_⟩
  · simp [finished, CachedCloseState.drop, CachedCloseState.release, DescriptorInventory.afterDrops,
      report.live, List.all_eq_true]
    exact ⟨retained .directory, retained .pending, retained .active⟩
  · exact report.lockObject.trans (congrArg (fun description => some (before.descriptors.inode description))
      report.description)

end CachedCloseReports

namespace ObservedBatchFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {failure : SegmentedBatchFailure directory before}
  {handle : Type} {writer : Nat}

abbrev FailedAt (observed : ObservedBatchFailure failure handle) (cacheAfter : Cache handle) : Prop :=
  runBatchWrite directory failure.rows observed.guard.lookup observed.append observed.stage observed.sync observed.rename
    (.ready before.installed, ⟨(observed.cache, WriteFiles.initial before.history
      (before.wal.directory.staged .walBoundary)), before.owners⟩) =
    .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩)

def closeState (failure : SegmentedBatchFailure directory before) (cache : Cache handle)
    (descriptors : DescriptorInventory) : CachedCloseState handle WriteFiles :=
  ⟨.poisoned, ⟨(cache, failure.failed), before.owners⟩, descriptors⟩

/-- Close starts with the cache returned by the reported batch failure.
After unlock and the three clears, its file and owner projection is
the admitted opener's exact retry origin. -/
theorem reopensAfterCachedClose {files : Type} {input : FilePath} {retry : LockedFileState FileImage}
    (observed : ObservedBatchFailure failure handle) (ready : before.RetainedReady directory writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      failure.released retry)
    (reads : BatchCutReopenObservations directory before failure.batch files input retry)
    (closes : ∀ cacheAfter, observed.FailedAt cacheAfter →
      ∃ (descriptors : DescriptorInventory)
        (reported : CachedCloseReports directory writer (closeState failure cacheAfter descriptors)),
        reported.result = .ok ()) :
    ∃ descriptor after, observed.AdmittedReopen (files := files) (.closed : SegmentedFailureRelease writer)
      input retry descriptor after ∧
      ∃ (cacheAfter : Cache handle) (descriptors : DescriptorInventory)
        (reported : CachedCloseReports directory writer (closeState failure cacheAfter descriptors)),
        observed.FailedAt cacheAfter ∧ reported.run = .ok () reported.finished ∧
        reported.finished.files.image.1 = ⟨none, none, []⟩ ∧
        (⟨before.wal.appendReopenFiles (reported.finished.files.image.2.reopenSegment before.wal.active.first
          before.history before.wal.directory.active.manifest) before.files.keeper.staged,
            reported.finished.files.owners⟩ : LockedFileState FileImage) = failure.released := by
  obtain ⟨descriptor, after, installed⟩ := observed.reopensAdmitted ready .closed attempts reads
  obtain ⟨cacheAfter, returned, _⟩ := installed.returned
  obtain ⟨descriptors, reported, successful⟩ := closes cacheAfter returned
  have closeRan := reported.outcome (poisoned := rfl)
  rw [successful] at closeRan
  have projected := reported.finishedFiles ready.held
  refine ⟨descriptor, after, installed, cacheAfter, descriptors, reported, returned, closeRan, ?_, ?_⟩
  · rw [projected]
  · rw [projected]
    rfl

end ObservedBatchFailure
end Alvoki.Storage.DiskSession
