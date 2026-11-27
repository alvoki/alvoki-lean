import Alvoki.Storage.Disk.Proofs.Rotation.SegmentedRotationStep
import Alvoki.Storage.Disk.Proofs.Session.DiskCleanReopenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation SyncHandleRouting

private def onRotationFiles {image α : Type} (action : EStateM IO.Error image α) :
    EStateM IO.Error (Phase Installed × LockedFileState image) α := fun (phase, before) =>
  match action before.image with
  | .ok value reached => .ok value (phase, { before with image := reached })
  | .error cause reached => .error cause (phase, { before with image := reached })

/-- Interpret the native rotation schedule, including the file-descriptor
effect of clearing the active handle before publishing readiness. -/
def runObservedRotationWithReset {handle image : Type} (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (releaseActive : Cache handle → image → image) :
    EStateM IO.Error (Phase Installed × LockedFileState (Cache handle × image)) Unit :=
  rotateWalSchedule
    (fun state => match (state.1.installed : Except IO.Error Installed) with
      | .ok installed => .ok installed state
      | .error cause => .error cause state)
    (fun installed => onRotationFiles (checkActiveSegmentWith directory installed (fun path => liftExcept (lookup path))))
    (fun phase (_, before) => .ok () (phase, before))
    (fun first => onRotationFiles (WalSegmentRotation.runAt directory first read create sync))
    (fun (phase, before) =>
      .ok () (phase, { before with image :=
        ({ before.image.1 with active := none }, releaseActive before.image.1 before.image.2) }))

/-- Project the native rotation onto an image without descriptor effects
from releasing the previous active handle. -/
def runObservedRotation {handle image : Type} (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit) :=
  runObservedRotationWithReset directory lookup read create sync (fun _ files => files)

theorem runObservedRotationWithReset_empty {handle image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × image))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (releaseActive : Cache handle → image → image)
    (empty : installed.walBytes / WAL.frameSize ≤ installed.activeFirst) :
    runObservedRotationWithReset directory lookup read create sync releaseActive (.ready installed, before) =
      .ok () (.ready installed, before) := by
  simp [runObservedRotationWithReset, rotateWalSchedule, Phase.installed, Nat.not_lt.mpr empty,
    Bind.bind, EStateM.bind, Pure.pure, Except.pure, EStateM.pure]

/-- A completing publication reaches the same cache and files set by the
issued callbacks. The active retirement is sequenced before the ready phase. -/
theorem runObservedRotationWithReset_ready {handle image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × image))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (releaseActive : Cache handle → image → image)
    (nonempty : installed.activeFirst < installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache handle × image))
      directory installed (fun path => liftExcept (lookup path)) before.image = .ok () before.image)
    {settled : Cache handle × image}
    (published : WalSegmentRotation.runAt directory (installed.walBytes / WAL.frameSize) read create sync before.image =
      .ok () settled) :
    runObservedRotationWithReset directory lookup read create sync releaseActive (.ready installed, before) =
      .ok () (.ready { installed with activeFirst := installed.walBytes / WAL.frameSize },
        { before with image := ({ settled.1 with active := none }, releaseActive settled.1 settled.2) }) := by
  simp [runObservedRotationWithReset, rotateWalSchedule, Phase.installed, nonempty, onRotationFiles,
    checked, publishPrepared, published, Bind.bind, EStateM.bind, Pure.pure, Except.pure]

/-- An empty keeper makes rotation a no-op, including on the append cache. -/
theorem runObservedRotation_empty {handle image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × image))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (empty : installed.walBytes / WAL.frameSize ≤ installed.activeFirst) :
    runObservedRotation directory lookup read create sync (.ready installed, before) = .ok () (.ready installed, before) := by
  exact runObservedRotationWithReset_empty directory installed before lookup read create sync _ empty

/-- A publication error leaves the writer poisoned with the exact reached
files and cache. The active-handle reset belongs to successful publication. -/
theorem runObservedRotation_publishError {handle image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × image))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (nonempty : installed.activeFirst < installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache handle × image))
      directory installed (fun path => liftExcept (lookup path)) before.image = .ok () before.image)
    {cause : IO.Error} {reached : Cache handle × image}
    (failed : WalSegmentRotation.runAt directory (installed.walBytes / WAL.frameSize) read create sync before.image =
      .error cause reached) :
    runObservedRotation directory lookup read create sync (.ready installed, before) =
      .error cause (.poisoned, { before with image := reached }) := by
  simp [runObservedRotation, runObservedRotationWithReset, rotateWalSchedule, Phase.installed, nonempty, onRotationFiles,
    checked, publishPrepared, failed, Bind.bind, EStateM.bind, Pure.pure, Except.pure]

/-- An already present empty successor skips creation. Successful file and
directory syncs still precede the active cache reset and ready phase. -/
theorem runObservedRotation_present {handle image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState (Cache handle × image))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (Cache handle × image) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (Cache handle × image) Unit)
    (nonempty : installed.activeFirst < installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error (Cache handle × image))
      directory installed (fun path => liftExcept (lookup path)) before.image = .ok () before.image)
    {fileSynced settled : Cache handle × image} :
    let successor := installed.walBytes / WAL.frameSize
    let path := directory.file (.walSegment successor)
    read path before.image = .ok (some ByteArray.empty) before.image →
    sync path before.image = .ok () fileSynced → sync directory.path fileSynced = .ok () settled →
    runObservedRotation directory lookup read create sync (.ready installed, before) =
      .ok () (.ready { installed with activeFirst := successor },
        { before with image := ({ settled.1 with active := none }, settled.2) }) := by
  intro successor path present file directorySync
  have ran : WalSegmentRotation.runAt directory successor read create sync before.image = .ok () settled := by
    rw [WalSegmentRotation.runAt_fileEffects]
    simp [observeSuccessorWith, present, file, directorySync, path, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  exact runObservedRotationWithReset_ready directory installed before lookup read create sync _ nonempty checked ran

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
  simp [runObservedRotation, runObservedRotationWithReset, rotateWalSchedule, Phase.installed, report.nonempty, onRotationFiles,
    observed.checked, publishPrepared, ran, SegmentedRotationReport.nextInstalled, SegmentedWriterState.rotationInstalled,
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
