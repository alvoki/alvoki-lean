import Alvoki.Storage.Disk.Proofs.Filesystem.DiskLockLifecycle
import Alvoki.Storage.Disk.Proofs.Bootstrap.WalSegmentBootstrapEffects

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- The installed ready cell and the separately allocated snapshot identity
belong to the same directory and open lock description. Natural numbers
represent fresh reference identities in the allocation report. -/
structure SegmentedSession where
  directory : DiskDirectory
  descriptor : Nat
  phase : Phase Installed
  phaseRef : Nat
  sessionRef : Nat

private def installSegmented {image : Type} (directory : DiskDirectory) (descriptor nextRef : Nat)
    (opened : Reopened) : EStateM IO.Error image SegmentedSession :=
  installReady opened.installed (fun phase => pure (phase, nextRef)) (fun _ => pure (nextRef + 1))
    fun (phase, phaseRef) sessionRef => pure ⟨directory, descriptor, phase, phaseRef, sessionRef⟩

/-- The shared lock scheduler runs recovery before allocation. Reference
allocation changes neither the files nor the lock owner. -/
def runOpenWithInstallation {image : Type} (directory : DiskDirectory) (descriptor nextRef : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (recover : EStateM IO.Error image Reopened) : EStateM IO.Error (LockedFileState image) SegmentedSession :=
  runOpenWithImage directory descriptor acquired unlock do
    installSegmented directory descriptor nextRef (← recover)

theorem runOpenWithInstallation_outcome {image : Type} (directory : DiskDirectory) (descriptor nextRef : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (recover : EStateM IO.Error image Reopened) (before : LockedFileState image) :
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before =
      match runOpenWithImage directory descriptor acquired unlock recover before with
      | .ok opened after =>
        .ok ⟨directory, descriptor, .ready opened.installed, nextRef, nextRef + 1⟩ after
      | .error cause after => .error cause after := by
  rcases acquired with error | (_ | _)
  · rfl
  · rfl
  · rw [runOpenWithInstallation, runOpenWithImage_acquired, runOpenWithImage_acquired]
    cases outcome : recover before.image with
    | ok opened after => simp [Bind.bind, EStateM.bind, outcome]; rfl
    | error cause after =>
      simp only [Bind.bind, EStateM.bind, outcome]
      cases unlock <;> rfl

/-- A successful observed recovery installs its exact payload and keeper in
the ready phase, and gives the caller the description that owns the lock.
The allocation report's next identity is above all references still live. -/
theorem runOpenWithInstallation_ready {image : Type} {directory : DiskDirectory} {descriptor nextRef : Nat}
    {unlock : UnlockReport} {recover : EStateM IO.Error image Reopened} {before : LockedFileState image}
    {opened : Reopened} {after : image} (liveRefs : List Nat)
    (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves before.owners directory (.ok true))
    (recovered : recover before.image = .ok opened after) :
    ∃ session final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before = .ok session final ∧
      session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready ⟨opened.table, opened.generation, opened.walBytes.toNat, opened.keeper⟩ ∧
      final.image = after ∧ before.owners (directory.file .lock) = none ∧ final.owners.Owns directory descriptor ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs := by
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired, recovered]
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, acquisition rfl, ?_, ?_, ?_, ?_⟩
  · simp [LockOwners.Owns, LockOwners.set]
  · change nextRef ≠ nextRef + 1
    omega
  · intro present
    exact Nat.lt_irrefl _ (fresh _ present)
  · intro present
    change nextRef + 1 ∈ liveRefs at present
    have earlier := fresh _ present
    omega

/-- After native admission, the shared markerless schedule installs an
empty ready session only once the segment and its zero marker are durable.
A reported failure preserves the projected bootstrap invariant. -/
theorem runOpenWithInstallation_bootstrap (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (empty : Option ByteArray) (seen : before.image.observeSuccessor = empty)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport)
    (createEmpty : System.FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : System.FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array System.FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : System.FilePath → System.FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (rotation : WalSegmentRotation.EffectReports
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])) :
    let recover := bootstrapEmptyWith directory empty createEmpty write sync renameFile
    match runOpenWithInstallation directory descriptor nextRef acquired unlock recover before with
    | .ok session after => session.phase = .ready ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after.image ∧
        before.owners (directory.file .lock) = none ∧ after.owners.Owns directory descriptor
    | .error _ after => BootstrapValid after.image := by
  intro recover
  rw [runOpenWithInstallation_outcome]
  by_cases took : acquired = .ok true
  · subst acquired
    rw [runOpenWithImage_acquired]
    have safe := bootstrapEmptyWith_safe directory before.image valid empty seen createEmpty write sync renameFile
      rotation marker
    change (match recover before.image with
      | .ok opened after => opened = ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after
      | .error _ after => BootstrapValid after) at safe
    cases recovered : recover before.image with
    | ok opened after =>
      rw [recovered] at safe
      obtain ⟨rfl, ready⟩ := safe
      exact ⟨rfl, ready, acquisition rfl, by simp [LockOwners.Owns, LockOwners.set]⟩
    | error _ after =>
      rw [recovered] at safe
      cases unlock <;> exact safe
  · obtain ⟨error, refused⟩ := runOpenWithImage_notAcquired directory descriptor acquired unlock recover before took
    rw [refused]
    exact valid

end Alvoki.Storage.DiskSession
