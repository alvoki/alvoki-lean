import Alvoki.Storage.Disk.SegmentedDatabaseTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The locked prefix of `DiskTable.open` selects the markerless installer
after directory setup and ENOENT at the exact flat WAL and marker paths.
The three reports are read-only on the reached file image. This equality
transports `SegmentedDatabaseTrace.fromHealthyBootstrap` to the shared
native branch without assuming a result from either recovery worker. -/
theorem runOpenWithInstallation_markerlessBranch {image files : Type}
    (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState image) (unlock : UnlockReport)
    (openFiles : EStateM IO.Error image files) (lookup : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : files → EStateM IO.Error image Reopened)
    (opened : files) (initialized : openFiles before.image = .ok opened before.image)
    (flatName flatMessage markerName markerMessage : String)
    (flatAbsent : lookup (directory.file .wal) before.image =
      .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) before.image)
    (markerAbsent : lookup (directory.file .walBoundary) before.image =
      .ok (.error (.noFileOrDirectory markerName 2 markerMessage)) before.image) :
    let recover := do
      let files ← openFiles
      recoverSegmentedWalWith (rejectFlatWalWith directory (optionalMetadataWith (lookup (directory.file .wal))))
        (optionalMetadataWith (lookup (directory.file .walBoundary))) (marked files) (bootstrap files)
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before =
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock (bootstrap opened) before := by
  intro recover
  have selected : recover before.image = bootstrap opened before.image := by
    simp only [recover, recoverSegmentedWalWith, rejectFlatWalWith, optionalMetadataWith, Bind.bind, EStateM.bind,
      initialized, flatAbsent, markerAbsent, Pure.pure, EStateM.pure, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte]
  rw [runOpenWithInstallation_outcome, runOpenWithInstallation_outcome,
    runOpenWithImage_acquired, runOpenWithImage_acquired, selected]

/-- Successful admission reads and reached durability callbacks start the
mixed trace with the exact empty session installed by markerless open. -/
theorem SegmentedDatabaseTrace.fromHealthyBootstrap (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (acquisition : TryLockObserves before.owners directory (.ok true)) (unlock : UnlockReport)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    (clear : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false)
    (zeroRead : readEmpty (directory.file (.walSegment 0)) = .ok before.image.observeSuccessor)
    {stage : Option IO.FS.Metadata} (staged : metadata (directory.file .stagedWalBoundary) = .ok stage)
    (allowed : ∀ info, stage = some info → info.type = .file ∧ before.image.observeSuccessor.isSome = true)
    (createEmpty : FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (allowCollection : Bool) :
    let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
    let publish := Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]
    let settled : WalSegmentRotation.State := ⟨before.image.metadata.syncDirectory, .durable⟩
    let recover := bootstrapSegmentedWith directory
      (fun path => liftExcept (list path)) (fun path => liftExcept (readEmpty path))
      (fun path => liftExcept (metadata path)) createEmpty write sync renameFile
    (∀ done step todo prior next, WalSegmentRotation.steps before.image.observeSuccessor.isSome = done ++ step :: todo →
      before.image.execute done = some prior → prior.step step = some next → rotate step prior = .ok () next) →
    (∀ done step todo prior next, Publication.steps = done ++ step :: todo →
      done.foldlM bootstrapMarkerStep settled = some prior → bootstrapMarkerStep prior step = some next →
      publish step prior = .ok () next) →
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before =
        .ok ⟨directory, descriptor, .ready writer.installed, nextRef, nextRef + 1⟩ after ∧
      before.owners (directory.file .lock) = none ∧
      after.owners = before.owners.set (directory.file .lock) (some descriptor) ∧
      writer.RetainedReady directory descriptor ∧
      SegmentedDatabaseTrace directory descriptor writer allowCollection [] descriptor writer := by
  intro rotate publish settled recover rotation marker
  have admitted : prepareBootstrapWith directory list readEmpty metadata = .ok before.image.observeSuccessor := by
    cases stage with
    | none =>
      simp [prepareBootstrapWith, listed, clear, zeroRead, staged, Bind.bind, Except.bind, Pure.pure, Except.pure]
    | some info =>
      obtain ⟨regular, present⟩ := allowed info rfl
      have regularFile : (info.type == .file) = true := by rw [regular]; rfl
      simp [prepareBootstrapWith, listed, clear, zeroRead, staged, regularFile, present, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  obtain ⟨image, completed, bootstrap⟩ := bootstrapEmptyWith_completes directory before.image valid
    before.image.observeSuccessor rfl createEmpty write sync renameFile rotation marker
  have recovered : recover before.image = .ok ⟨.empty, 0, 0, 0⟩ image := by
    unfold recover bootstrapSegmentedWith
    rw [prepareBootstrapWith_liftReports, admitted]
    exact completed
  let after : LockedFileState WalSegmentRotation.State := ⟨image, before.owners.set (directory.file .lock) (some descriptor)⟩
  have held : after.owners.Owns directory descriptor := by simp [after, LockOwners.Owns, LockOwners.set]
  refine ⟨after, bootstrap, ?_, acquisition rfl, rfl, (bootstrap.writerReady held).toRetained, .start⟩
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired, recovered]
  rfl

end Alvoki.Storage.DiskSession
