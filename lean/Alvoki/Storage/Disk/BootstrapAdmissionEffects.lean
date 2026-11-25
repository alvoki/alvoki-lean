import Alvoki.Storage.Disk.SegmentedSessionInstall

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- Reports for a checked listing, the empty segment probe and an allowed
staging name reach publication with the exact observed empty segment. -/
theorem prepareBootstrapWith_admitted (directory : DiskDirectory)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    (clear : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false)
    {empty : Option ByteArray} (observed : readEmpty (directory.file (.walSegment 0)) = .ok empty)
    {stage : Option IO.FS.Metadata} (staged : metadata (directory.file .stagedWalBoundary) = .ok stage)
    (allowed : ∀ info, stage = some info → info.type = .file ∧ empty.isSome = true) :
    prepareBootstrapWith directory list readEmpty metadata = .ok empty := by
  cases stage with
  | none =>
    simp [prepareBootstrapWith, listed, clear, observed, staged, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some info =>
    obtain ⟨regular, present⟩ := allowed info rfl
    have regularFile : (info.type == .file) = true := by rw [regular]; rfl
    simp [prepareBootstrapWith, listed, clear, observed, staged, regularFile, present, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

theorem prepareBootstrapWith_readEmpty (directory : DiskDirectory)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata)) {empty : Option ByteArray}
    (prepared : prepareBootstrapWith directory list readEmpty metadata = .ok empty) :
    readEmpty (directory.file (.walSegment 0)) = .ok empty := by
  unfold prepareBootstrapWith at prepared
  cases listed : list directory.path with
  | error cause => simp [listed, Bind.bind, Except.bind] at prepared
  | ok entries =>
    by_cases conflict : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = true
    · simp [listed, conflict, Bind.bind, Except.bind, throw] at prepared
    · cases zero : readEmpty (directory.file (.walSegment 0)) with
      | error cause => simp [listed, conflict, zero, Bind.bind, Except.bind] at prepared
      | ok actual =>
        cases stage : metadata (directory.file .stagedWalBoundary) with
        | error cause => simp [listed, conflict, zero, stage, Bind.bind, Except.bind] at prepared
        | ok stageInfo =>
          cases stageInfo with
          | none =>
            simpa [listed, conflict, zero, stage, Bind.bind, Except.bind, Pure.pure, Except.pure] using prepared
          | some staged =>
            by_cases allowed : (staged.type == .file && actual.isSome) = true
            · simpa [listed, conflict, zero, stage, allowed, Bind.bind, Except.bind, Pure.pure, Except.pure] using prepared
            · simp [listed, conflict, zero, stage, allowed, Bind.bind, Except.bind, throw] at prepared

/-- Admission consists of read-only reports. Every read error leaves the
filesystem image unchanged, with the same error as the concrete guard. -/
theorem prepareBootstrapWith_liftReports {state : Type} (directory : DiskDirectory)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata)) :
    (prepareBootstrapWith directory (fun path => liftExcept (list path))
      (fun path => liftExcept (readEmpty path)) (fun path => liftExcept (metadata path)) :
      EStateM IO.Error state (Option ByteArray)) = liftExcept (prepareBootstrapWith directory list readEmpty metadata) := by
  funext before
  unfold prepareBootstrapWith
  dsimp only
  cases listed : list directory.path with
  | error cause => simp only [liftExcept, Bind.bind, EStateM.bind, Except.bind]; rfl
  | ok entries =>
    simp only [liftExcept, Bind.bind, EStateM.bind, Except.bind, Pure.pure, EStateM.pure]
    by_cases conflict : entries.any (fun entry => conflictsWithBootstrap entry.fileName) = true
    · simp only [ite_eq_left conflict]; rfl
    · simp only [ite_eq_right conflict]
      cases zero : readEmpty (directory.file (.walSegment 0)) with
      | error cause => rfl
      | ok actual =>
        cases stage : metadata (directory.file .stagedWalBoundary) with
        | error cause => rfl
        | ok stageInfo =>
          cases stageInfo with
          | none => rfl
          | some staged =>
            by_cases allowed : (staged.type == .file && actual.isSome) = true
            · simp only [EStateM.bind, EStateM.pure, Except.pure, ite_eq_left allowed]
            · simp only [EStateM.bind, EStateM.pure, Except.pure, ite_eq_right allowed]; rfl

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A markerless native attempt runs the exact locked directory guards
before creating or publishing any files. Failed admission leaves the
filesystem image unchanged. A completed bootstrap installs the exact
empty table and keeps the acquired lock. -/
theorem runOpenWithInstallation_bootstrapFromReports (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    (seen : ∀ empty, readEmpty (directory.file (.walSegment 0)) = .ok empty → before.image.observeSuccessor = empty)
    (createEmpty : FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (rotation : WalSegmentRotation.EffectReports
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])) :
    let report := prepareBootstrapWith directory list readEmpty metadata
    let recover := bootstrapSegmentedWith directory
      (fun path => liftExcept (list path)) (fun path => liftExcept (readEmpty path))
      (fun path => liftExcept (metadata path)) createEmpty write sync renameFile
    match runOpenWithInstallation directory descriptor nextRef acquired unlock recover before with
    | .ok session after => session.phase = .ready ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after.image ∧
        before.owners (directory.file .lock) = none ∧ after.owners.Owns directory descriptor ∧
        report = .ok before.image.observeSuccessor
    | .error _ after => BootstrapValid after.image ∧
        (∀ error, report = .error error → after.image = before.image) := by
  intro report recover
  have route : recover = (do
      let empty ← (liftExcept report : EStateM IO.Error WalSegmentRotation.State (Option ByteArray))
      bootstrapEmptyWith directory empty createEmpty write sync renameFile) := by
    change bootstrapSegmentedWith directory _ _ _ createEmpty write sync renameFile = _
    unfold bootstrapSegmentedWith
    rw [prepareBootstrapWith_liftReports]
  rw [route]
  cases prepared : report with
  | error cause =>
    let rejected : EStateM IO.Error WalSegmentRotation.State Reopened := fun state => .error cause state
    have blocked : ((do
        let empty ← (liftExcept (.error cause) : EStateM IO.Error WalSegmentRotation.State (Option ByteArray))
        bootstrapEmptyWith directory empty createEmpty write sync renameFile) :
          EStateM IO.Error WalSegmentRotation.State Reopened) = rejected := rfl
    rw [blocked, runOpenWithInstallation_outcome]
    by_cases held : acquired = .ok true
    · subst acquired
      rw [runOpenWithImage_acquired]
      cases unlock <;> exact ⟨valid, fun _ _ => rfl⟩
    · obtain ⟨_, refused⟩ := runOpenWithImage_notAcquired directory descriptor acquired unlock rejected before held
      rw [refused]
      exact ⟨valid, fun _ _ => rfl⟩
  | ok empty =>
    have read := prepareBootstrapWith_readEmpty directory list readEmpty metadata prepared
    have observes := seen empty read
    have next : ((do
        let observed ← (liftExcept (.ok empty : Except IO.Error (Option ByteArray)) :
          EStateM IO.Error WalSegmentRotation.State (Option ByteArray))
        bootstrapEmptyWith directory observed createEmpty write sync renameFile) :
          EStateM IO.Error WalSegmentRotation.State Reopened) =
        bootstrapEmptyWith directory empty createEmpty write sync renameFile := rfl
    rw [next]
    have safety := runOpenWithInstallation_bootstrap directory descriptor nextRef before valid empty observes
      acquired acquisition unlock createEmpty write sync renameFile rotation marker
    dsimp only at safety
    cases outcome : runOpenWithInstallation directory descriptor nextRef acquired unlock
        (bootstrapEmptyWith directory empty createEmpty write sync renameFile) before with
    | error cause after =>
      rw [outcome] at safety
      exact ⟨safety, fun _ impossible => by cases impossible⟩
    | ok session after =>
      rw [outcome] at safety
      obtain ⟨phase, ready, prior, owned⟩ := safety
      exact ⟨phase, ready, prior, owned, congrArg Except.ok observes.symm⟩

end Alvoki.Storage.DiskSession
