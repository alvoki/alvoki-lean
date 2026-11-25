import Alvoki.Storage.Disk.SegmentedRotationStep
import Alvoki.Storage.Disk.DiskCleanReopenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation SyncHandleRouting

private def onRotationFiles {image α : Type} (action : EStateM IO.Error image α) :
    EStateM IO.Error (Phase Installed × LockedFileState image) α := fun (phase, before) =>
  match action before.image with
  | .ok value reached => .ok value (phase, { before with image := reached })
  | .error cause reached => .error cause (phase, { before with image := reached })

/-- Interpret the native rotation schedule over the ready phase, held lock,
file effects and actual reached handle cache. -/
def runObservedRotation {handle : Type} (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × State) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × State) Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState (Cache handle × State)) Unit :=
  rotateWalSchedule
    (fun state => match (state.1.installed : Except IO.Error Installed) with
      | .ok installed => .ok installed state
      | .error cause => .error cause state)
    (fun installed => onRotationFiles (checkActiveSegmentWith directory installed (fun path => liftExcept (lookup path))))
    (fun phase (_, before) => .ok () (phase, before))
    (fun first => onRotationFiles (WalSegmentRotation.runAt directory first read create sync))
    (fun (phase, before) =>
      .ok () (phase, { before with image := ({ before.image.1 with active := none }, before.image.2) }))

/-- An empty keeper makes rotation a no-op, including on the append cache. -/
theorem runObservedRotation_empty {handle : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × State))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × State) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × State) Unit)
    (empty : installed.walBytes / WAL.frameSize ≤ installed.activeFirst) :
    runObservedRotation directory lookup read create sync (.ready installed, before) = .ok () (.ready installed, before) := by
  simp [runObservedRotation, rotateWalSchedule, Phase.installed, Nat.not_lt.mpr empty,
    Bind.bind, EStateM.bind, Pure.pure, Except.pure, EStateM.pure]

/-- A publication error leaves the writer poisoned with the exact reached
files and cache. The active-handle reset belongs to successful publication. -/
theorem runObservedRotation_publishError {handle : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × State))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × State) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × State) Unit)
    (nonempty : installed.activeFirst < installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache handle × State))
      directory installed (fun path => liftExcept (lookup path)) before.image = .ok () before.image)
    {cause : IO.Error} {reached : Cache handle × State}
    (failed : WalSegmentRotation.runAt directory (installed.walBytes / WAL.frameSize) read create sync before.image =
      .error cause reached) :
    runObservedRotation directory lookup read create sync (.ready installed, before) =
      .error cause (.poisoned, { before with image := reached }) := by
  simp [runObservedRotation, rotateWalSchedule, Phase.installed, nonempty, onRotationFiles,
    checked, publishPrepared, failed, Bind.bind, EStateM.bind, Pure.pure, Except.pure]

/-- The successful local observations for an initially absent successor.
Each cached callback starts in the exact state left by its predecessor.
Its file component records the reached creation and durability effects. -/
structure ObservedRotation (directory : DiskDirectory) (before : SegmentedWriterState) (handle : Type) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  read : FilePath → EStateM IO.Error (Cache handle × State) (Option ByteArray)
  create : FilePath → EStateM IO.Error (Cache handle × State) Unit
  sync : FilePath → EStateM IO.Error (Cache handle × State) Unit
  cache : Cache handle
  created : Cache handle
  fileSynced : Cache handle
  directorySynced : Cache handle
  checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache handle × State))
    directory before.installed (fun path => liftExcept (lookup path))
    (cache, .initial before.wal) = .ok () (cache, .initial before.wal)
  absent : read (directory.file (.walSegment (before.installed.walBytes / WAL.frameSize)))
    (cache, .initial before.wal) = .ok none (cache, .initial before.wal)
  createReturned : create (directory.file (.walSegment (before.installed.walBytes / WAL.frameSize)))
    (cache, .initial before.wal) = .ok () (created, ⟨before.wal.directory, .created⟩)
  fileReturned : sync (directory.file (.walSegment (before.installed.walBytes / WAL.frameSize)))
    (created, ⟨before.wal.directory, .created⟩) = .ok () (fileSynced, ⟨before.wal.directory, .fileSynced⟩)
  directoryReturned : sync directory.path (fileSynced, ⟨before.wal.directory, .fileSynced⟩) =
    .ok () (directorySynced, ⟨before.wal.directory.syncDirectory, .durable⟩)

/-- Derive the complete ready return from the reached lookup, creation,
file sync and directory sync. Successful publication clears only the
active cache field left by those callbacks. -/
theorem ObservedRotation.rotates {directory : DiskDirectory} {before : SegmentedWriterState} {handle : Type}
    (observed : ObservedRotation directory before handle) (report : SegmentedRotationReport directory before) :
    runObservedRotation directory observed.lookup observed.read observed.create observed.sync
      (.ready before.installed, ⟨(observed.cache, .initial before.wal), before.owners⟩) =
      .ok () (.ready report.nextInstalled, ⟨({ observed.directorySynced with active := none }, report.cut), before.owners⟩) := by
  have ran : WalSegmentRotation.runAt directory (before.installed.walBytes / WAL.frameSize)
      observed.read observed.create observed.sync (observed.cache, .initial before.wal) =
      .ok () (observed.directorySynced, report.cut) := by
    rw [report.settled, WalSegmentRotation.runAt_fileEffects]
    simp [observeSuccessorWith, observed.absent, observed.createReturned, observed.fileReturned,
      observed.directoryReturned, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  simp [runObservedRotation, rotateWalSchedule, Phase.installed, report.nonempty, onRotationFiles,
    observed.checked, publishPrepared, ran, SegmentedRotationReport.nextInstalled,
    Bind.bind, EStateM.bind, Pure.pure, Except.pure]

/-- The exact rotated writer can close and reopen under the same canonical
lock object on a new description. The admitted opener uses the new keeper
and the exact selected chunk reports for that rotated writer. -/
theorem ObservedRotation.reopensAfterClose {directory : DiskDirectory} {before : SegmentedWriterState}
    {handle files : Type} {writer : Nat} {input : FilePath}
    (observed : ObservedRotation directory before handle) (ready : before.RetainedReady directory writer)
    (report : SegmentedRotationReport directory before) {target : Target} (selected : report.Selects target)
    (closed : CleanUnlockReports directory writer) (reads : closed.ReopenObservations files input (report.next target)) :
    runObservedRotation directory observed.lookup observed.read observed.create observed.sync
      (.ready before.installed, ⟨(observed.cache, .initial before.wal), before.owners⟩) =
      .ok () (.ready (report.next target).installed,
        ⟨({ observed.directorySynced with active := none }, report.cut), (report.next target).owners⟩) ∧
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory (report.next target)).image
        (report.next target).history)
      (reopened : MarkedRetryChunkReports files directory layout (report.next target).published)
      (admission : OpenAdmissionReports input directory reopened.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen closed reopened admission after :=
  ⟨observed.rotates report, (report.preservesRetainedReady ready selected).closeWithAdmission closed reads⟩

end Alvoki.Storage.DiskSession
