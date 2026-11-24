import Alvoki.Storage.Disk.DiskTable

namespace Alvoki.Storage.DiskSession

/-- Ownership of each stable lock object by a modeled open-file-description identity.
Distinct keys in the owned namespace name distinct stable lock objects. -/
abbrev LockOwners := System.FilePath → Option Nat

def LockOwners.Owns (owners : LockOwners) (directory : DiskDirectory) (descriptor : Nat) : Prop :=
  owners (directory.file .lock) = some descriptor

/-- A fresh descriptor can successfully take the exclusive Linux lock only
when the stable lock object has no owner. Each cooperating opener uses that
same object. A failed acquisition preserves the ownership map. -/
def TryLockObserves (owners : LockOwners) (directory : DiskDirectory)
    (result : Except IO.Error Bool) : Prop :=
  result = .ok true → owners (directory.file .lock) = none

def LockOwners.set (owners : LockOwners) (lock : System.FilePath) (owner : Option Nat) : LockOwners :=
  fun other => if other = lock then owner else owners other

def LockOwners.release (owners : LockOwners) (lock : System.FilePath) (descriptor : Nat) : LockOwners :=
  if owners lock = some descriptor then owners.set lock none else owners

private theorem releaseAcquired (owners : LockOwners) (lock : System.FilePath) (descriptor : Nat) :
    (owners.set lock (some descriptor)).release lock descriptor = owners.set lock none := by
  funext path
  by_cases selected : path = lock <;> simp [LockOwners.release, LockOwners.set, selected]

theorem LockOwners.release_owned {owners : LockOwners} {directory : DiskDirectory} {descriptor : Nat}
    (owned : owners.Owns directory descriptor) :
    owners.release (directory.file .lock) descriptor = owners.set (directory.file .lock) none := by
  change owners (directory.file .lock) = some descriptor at owned
  simp [LockOwners.release, owned]

theorem LockOwners.release_unowned {owners : LockOwners} {lock : System.FilePath} {descriptor : Nat}
    (unowned : owners lock ≠ some descriptor) : owners.release lock descriptor = owners := by
  simp [LockOwners.release, unowned]

/-- A reported unlock error records whether the release took effect. Release
affects only the lock of the descriptor on which it was requested. -/
inductive UnlockReport where
  | success
  | failure (cause : IO.Error) (released : Bool)

/-- On the supported local Linux `flock` path, an unlock reported as an error
preserves ownership while the open file description stays live. -/
def UnlockReport.LocalFlock : UnlockReport → Prop
  | .success => True
  | .failure _ released => released = false

private def UnlockReport.perform (report : UnlockReport) (release : σ → σ) : EStateM IO.Error σ Unit :=
  fun state => match report with
  | .success => .ok () (release state)
  | .failure cause released => .error cause (if released then release state else state)

private def acquire (lock : System.FilePath) (descriptor : Nat) (result : Except IO.Error Bool) :
    EStateM IO.Error LockOwners Bool := fun owners => match result with
  | .ok true => .ok true (owners.set lock (some descriptor))
  | .ok false => .ok false owners
  | .error cause => .error cause owners

/-- Interpret the shared open schedule after path resolution and opening the
lock file. Recovery receives the acquired lock and leaves its ownership unchanged. -/
def runOpen (directory : DiskDirectory) (descriptor : Nat) (acquired : Except IO.Error Bool)
    (recovered : Except IO.Error α) (unlock : UnlockReport) : EStateM IO.Error LockOwners α :=
  let lock := directory.file .lock
  openWithLock (acquire lock descriptor acquired) (fun _ => IO.userError s!"database already open: {directory.path}")
    (fun _ => unlock.perform (fun owners => owners.release lock descriptor))
    (fun _ owners => match recovered with
      | .ok value => .ok value owners
      | .error cause => .error cause owners)

theorem runOpen_busy (directory : DiskDirectory) (descriptor : Nat) (owners : LockOwners)
    (recovered : Except IO.Error α) (unlock : UnlockReport) :
    runOpen directory descriptor (.ok false) recovered unlock owners =
      .error (IO.userError s!"database already open: {directory.path}") owners := rfl

theorem runOpen_lockError (directory : DiskDirectory) (descriptor : Nat) (owners : LockOwners)
    (cause : IO.Error) (recovered : Except IO.Error α) (unlock : UnlockReport) :
    runOpen directory descriptor (.error cause) recovered unlock owners = .error cause owners := rfl

theorem runOpen_success {directory : DiskDirectory} {descriptor : Nat} {acquired : Except IO.Error Bool}
    {recovered : Except IO.Error α} {unlock : UnlockReport} {before after : LockOwners} {value : α}
    (contract : TryLockObserves before directory acquired)
    (opened : runOpen directory descriptor acquired recovered unlock before = .ok value after) :
    before (directory.file .lock) = none ∧ after.Owns directory descriptor ∧
      recovered = .ok value ∧ ∀ other, other ≠ directory.file .lock → after other = before other := by
  cases acquired with
  | error => contradiction
  | ok took =>
    cases took with
    | false => contradiction
    | true =>
      cases recovered with
      | error => cases unlock <;> contradiction
      | ok result =>
        cases opened
        exact ⟨contract rfl, by simp [LockOwners.Owns, LockOwners.set], rfl,
          fun other elsewhere => by simp [LockOwners.set, elsewhere]⟩

/-- A second cooperating open cannot start recovery while the first owns the
lock. The failed acquisition leaves the owner and all other bindings intact. -/
theorem runOpen_held {directory : DiskDirectory} {owner : Nat} {owners : LockOwners}
    {acquired : Except IO.Error Bool} (held : owners.Owns directory owner)
    (contract : TryLockObserves owners directory acquired) (descriptor : Nat)
    (recovered : Except IO.Error α) (unlock : UnlockReport) :
    ∃ cause, runOpen directory descriptor acquired recovered unlock owners = .error cause owners := by
  cases acquired with
  | error cause => exact ⟨cause, rfl⟩
  | ok took =>
    cases took with
    | false => exact ⟨_, rfl⟩
    | true =>
      change owners (directory.file .lock) = some owner at held
      rw [contract rfl] at held
      contradiction

/-- Once recovery fails, successful cleanup returns the recovery error and
clears the lock. If cleanup fails, its error is the reported one. -/
theorem runOpen_recoveryError (directory : DiskDirectory) (descriptor : Nat) (owners : LockOwners)
    (recoveryError : IO.Error) (unlock : UnlockReport) :
    runOpen directory descriptor (.ok true) (.error recoveryError : Except IO.Error α) unlock owners =
      match unlock with
      | .success => .error recoveryError (owners.set (directory.file .lock) none)
      | .failure error released => .error error (owners.set (directory.file .lock)
        (if released then none else some descriptor)) := by
  cases unlock with
  | success =>
    change EStateM.Result.error recoveryError
      ((owners.set (directory.file .lock) (some descriptor)).release (directory.file .lock) descriptor) = _
    rw [releaseAcquired]
  | failure error released =>
    cases released with
    | false => rfl
    | true =>
      change EStateM.Result.error error
        ((owners.set (directory.file .lock) (some descriptor)).release (directory.file .lock) descriptor) = _
      rw [releaseAcquired]
      rfl

structure LockedFileState (image : Type) where
  image : image
  owners : LockOwners

private def liftLockAction (action : EStateM IO.Error LockOwners α) :
    EStateM IO.Error (LockedFileState image) α := fun before =>
  match action before.owners with
  | .ok value after => .ok value { before with owners := after }
  | .error error after => .error error { before with owners := after }

private def liftRecoveryAction (recover : EStateM IO.Error image α) :
    EStateM IO.Error (LockedFileState image) α := fun before =>
  match recover before.image with
  | .ok value after => .ok value { before with image := after }
  | .error error after => .error error { before with image := after }

/-- Interpret the shared lock schedule with recovery effects on a separate
file image. Cleanup runs with the image left by the failed recovery. -/
def runOpenWithImage (directory : DiskDirectory) (descriptor : Nat) (acquired : Except IO.Error Bool)
    (unlock : UnlockReport) (recover : EStateM IO.Error image α) :
    EStateM IO.Error (LockedFileState image) α :=
  let lock := directory.file .lock
  openWithLock (liftLockAction (acquire lock descriptor acquired))
    (fun _ => IO.userError s!"database already open: {directory.path}")
    (fun _ => liftLockAction (unlock.perform (fun owners => owners.release lock descriptor)))
    (fun _ => liftRecoveryAction recover)

theorem runOpenWithImage_notAcquired (directory : DiskDirectory) (descriptor : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport) (recover : EStateM IO.Error image α)
    (before : LockedFileState image) (denied : acquired ≠ .ok true) :
    ∃ error, runOpenWithImage directory descriptor acquired unlock recover before = .error error before := by
  rcases acquired with error | (_ | _)
  · exact ⟨error, rfl⟩
  · exact ⟨_, rfl⟩
  · exact False.elim (denied rfl)

theorem runOpenWithImage_acquired (directory : DiskDirectory) (descriptor : Nat)
    (unlock : UnlockReport) (recover : EStateM IO.Error image α) (before : LockedFileState image) :
    runOpenWithImage directory descriptor (.ok true) unlock recover before =
      match recover before.image with
      | .ok value after => .ok value ⟨after, before.owners.set (directory.file .lock) (some descriptor)⟩
      | .error error after => match unlock with
        | .success => .error error ⟨after, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup applied => .error cleanup
          ⟨after, before.owners.set (directory.file .lock) (if applied then none else some descriptor)⟩ := by
  simp only [runOpenWithImage, openWithLock, liftLockAction, acquire, Bind.bind, EStateM.bind, ite_true,
    MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, liftRecoveryAction]
  cases recover before.image with
  | ok => rfl
  | error error after =>
    cases unlock with
    | success =>
      change EStateM.Result.error error
        (⟨after, (before.owners.set (directory.file .lock) (some descriptor)).release
          (directory.file .lock) descriptor⟩ : LockedFileState image) = _
      rw [releaseAcquired]
    | failure cleanup applied =>
      cases applied
      · rfl
      · change EStateM.Result.error cleanup
          (⟨after, (before.owners.set (directory.file .lock) (some descriptor)).release
            (directory.file .lock) descriptor⟩ : LockedFileState image) = _
        rw [releaseAcquired]
        rfl

structure LockSession (α : Type) where
  phase : Phase α
  owners : LockOwners

def runClose (directory : DiskDirectory) (descriptor : Nat) (unlock : UnlockReport)
    (state : LockSession α) : EStateM.Result IO.Error (LockSession α) Unit :=
  state.phase.close (fun _ => unlock.perform fun current =>
      { current with owners := current.owners.release (directory.file .lock) descriptor })
    (fun _ current => .ok () { current with phase := .closed }) state

theorem runClose_closed (directory : DiskDirectory) (descriptor : Nat) (owners : LockOwners)
    (unlock : UnlockReport) : runClose directory descriptor unlock (⟨.closed, owners⟩ : LockSession α) =
      .ok () ⟨.closed, owners⟩ := rfl

/-- Both ready and poisoned handles can release ownership. A reporting error
preserves the old phase, even when the unlock released the lock. -/
theorem runClose_open {directory : DiskDirectory} {descriptor : Nat} {state : LockSession α}
    (live : state.phase ≠ .closed) (unlock : UnlockReport) : runClose directory descriptor unlock state =
      let released := state.owners.release (directory.file .lock) descriptor
      match unlock with
      | .success => .ok () ⟨.closed, released⟩
      | .failure error applied => .error error (if applied then { state with owners := released } else state) := by
  cases state with
  | mk phase owners =>
    cases phase <;> cases unlock <;>
      simp_all [runClose, Phase.close, UnlockReport.perform, Bind.bind, EStateM.bind]

/-- Under the local unlock contract, a failed close preserves both the
session's phase and its entire lock ownership map. -/
theorem runClose_localFlock_error {directory : DiskDirectory} {descriptor : Nat} {state after : LockSession α}
    {unlock : UnlockReport} {cause : IO.Error} (contract : unlock.LocalFlock)
    (closed : runClose directory descriptor unlock state = .error cause after) : after = state := by
  by_cases alreadyClosed : state.phase = .closed
  · unfold runClose at closed
    rw [alreadyClosed] at closed
    contradiction
  · rw [runClose_open alreadyClosed unlock] at closed
    cases unlock with
    | success => contradiction
    | failure _ released =>
      change released = false at contract
      subst released
      exact (EStateM.Result.error.inj closed).2.symm

end Alvoki.Storage.DiskSession
