import Alvoki.Storage.Disk.SegmentedDatabaseTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

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
