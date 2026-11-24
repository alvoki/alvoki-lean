import Alvoki.Storage.Disk.LockedMarkedReopenFailureTrace
import Alvoki.Storage.Disk.SegmentedSessionInstall

namespace Alvoki.Storage.DiskSession

/-- A live descriptor-table slot referring to one open file description.
The process identity stays stable for the observation, independent of a
numeric PID or descriptor being reused by a later open. -/
structure LockReference where
  process : Nat
  fd : Nat
  closeOnExec : Bool

/-- Events on private process descriptor tables. A close records removal of
the slot, including when the syscall reports an error after dropping it.
An exec records successful exec, and an exit records release of the table
by its last task. -/
inductive LockReferenceDrop where
  | closed (process fd : Nat)
  | executed (process : Nat)
  | exited (process : Nat)

def LockReferenceDrop.removes : LockReferenceDrop → LockReference → Bool
  | .closed process fd, reference => reference.process == process && reference.fd == fd
  | .executed process, reference => reference.process == process && reference.closeOnExec
  | .exited process, reference => reference.process == process

/-- The initial observation enumerates every live slot for the held open
file description, including inherited or duplicated slots. The observer
supplies stable process and description identities. During a drop sequence
no new slots refer to this description and their close-on-exec flags stay
fixed. The contract excludes non-slot references that retain the lock and
an independent explicit unlock during the sequence. -/
structure HeldLockReferences (description : Nat) where
  live : List LockReference
  nonempty : live ≠ []
  distinct : (live.map fun reference => (reference.process, reference.fd)).Nodup

def HeldLockReferences.remaining {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop) : List LockReference :=
  references.live.filter fun reference => drops.all fun event => !event.removes reference

theorem HeldLockReferences.mem_remaining {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (reference : LockReference) :
    reference ∈ references.remaining drops ↔
      reference ∈ references.live ∧ ∀ event ∈ drops, event.removes reference = false := by
  simp only [remaining, List.mem_filter, List.all_eq_true, Bool.not_eq_true']

private def HeldLockReferences.ownersAfterDrops {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (directory : DiskDirectory) (owners : LockOwners) : LockOwners :=
  if (references.remaining drops).isEmpty then
    owners.release (directory.file .lock) description
  else owners

/-- Apply observed reference drops to the whole-file reopen state. -/
def HeldLockReferences.afterDrops {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (directory : DiskDirectory) (before : LockedReopenState) : LockedReopenState :=
  { before with owners := references.ownersAfterDrops drops directory before.owners }

/-- Observed reference drops change only ownership of the matching lock.
The file image survives even when the description's last reference is gone. -/
def HeldLockReferences.afterFileDrops {image : Type} {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (directory : DiskDirectory) (before : LockedFileState image) : LockedFileState image :=
  { before with owners := references.ownersAfterDrops drops directory before.owners }

theorem HeldLockReferences.afterFileDrops_surviving {image : Type} {description : Nat}
    {directory : DiskDirectory} {before : LockedFileState image} {drops : List LockReferenceDrop}
    (references : HeldLockReferences description) (retained : references.remaining drops ≠ []) :
    references.afterFileDrops drops directory before = before := by
  simp [afterFileDrops, ownersAfterDrops, List.isEmpty_eq_false_iff.mpr retained]

theorem HeldLockReferences.afterFileDrops_released {image : Type} {description : Nat}
    {directory : DiskDirectory} {before : LockedFileState image} {drops : List LockReferenceDrop}
    (references : HeldLockReferences description) (ownership : before.owners.Owns directory description)
    (last : references.remaining drops = []) :
    references.afterFileDrops drops directory before =
      ⟨before.image, before.owners.set (directory.file .lock) none⟩ := by
  simp [afterFileDrops, ownersAfterDrops, last, LockOwners.release_owned ownership]

/-- A successful acquisition is consistent with the observed file state
exactly when the last reference to its previous owner has dropped. -/
theorem HeldLockReferences.afterFileDrops_admits {image : Type} {description : Nat}
    {directory : DiskDirectory} {before : LockedFileState image} {drops : List LockReferenceDrop}
    (references : HeldLockReferences description) (ownership : before.owners.Owns directory description) :
    TryLockObserves (references.afterFileDrops drops directory before).owners directory (.ok true) ↔
      references.remaining drops = [] := by
  by_cases last : references.remaining drops = []
  · rw [references.afterFileDrops_released ownership last]
    simp [TryLockObserves, LockOwners.set, last]
  · rw [references.afterFileDrops_surviving last]
    constructor
    · intro acquired
      change before.owners (directory.file .lock) = some description at ownership
      rw [acquired rfl] at ownership
      contradiction
    · exact fun gone => False.elim (last gone)

/-- The shared open schedule reaches neither recovery nor ready installation
while any observed reference keeps the exclusive lock description live. -/
theorem runOpenWithInstallation_whileReferenceSurvives {image : Type}
    {directory : DiskDirectory} {before : LockedFileState image} {description descriptor nextRef : Nat}
    {drops : List LockReferenceDrop} {acquired : Except IO.Error Bool}
    (references : HeldLockReferences description) (ownership : before.owners.Owns directory description)
    (retained : references.remaining drops ≠ [])
    (acquisition : TryLockObserves (references.afterFileDrops drops directory before).owners directory acquired)
    (unlock : UnlockReport) (recover : EStateM IO.Error image WalSegmentRepair.Reopened) :
    ∃ cause, runOpenWithInstallation directory descriptor nextRef acquired unlock recover
      (references.afterFileDrops drops directory before) = .error cause before := by
  rw [references.afterFileDrops_surviving retained] at acquisition ⊢
  have denied : acquired ≠ .ok true := by
    intro took
    have lockHeld := ownership
    change before.owners (directory.file .lock) = some description at lockHeld
    rw [acquisition took] at lockHeld
    contradiction
  obtain ⟨cause, refused⟩ := runOpenWithImage_notAcquired directory descriptor acquired unlock recover before denied
  exact ⟨cause, by rw [runOpenWithInstallation_outcome, refused]⟩

/-- Once the last reference drops, the same lock admits a reported healthy
open on the exact preceding image. Only its owner entry is replaced. -/
theorem runOpenWithInstallation_afterLastReferenceDrop {image : Type}
    {directory : DiskDirectory} {before : LockedFileState image} {description descriptor nextRef : Nat}
    {drops : List LockReferenceDrop} {recover : EStateM IO.Error image WalSegmentRepair.Reopened}
    {opened : WalSegmentRepair.Reopened} {after : image}
    (references : HeldLockReferences description) (ownership : before.owners.Owns directory description)
    (last : references.remaining drops = []) (unlock : UnlockReport)
    (recovered : recover before.image = .ok opened after) :
    let released := references.afterFileDrops drops directory before
    TryLockObserves released.owners directory (.ok true) ∧
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover released =
        .ok ⟨directory, descriptor, .ready opened.installed, nextRef, nextRef + 1⟩
          ⟨after, before.owners.set (directory.file .lock) (some descriptor)⟩ := by
  dsimp only
  rw [references.afterFileDrops_released ownership last]
  constructor
  · simp [TryLockObserves, LockOwners.set]
  · rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired]
    dsimp only
    rw [recovered]
    have owners :
        (before.owners.set (directory.file .lock) none).set (directory.file .lock) (some descriptor) =
          before.owners.set (directory.file .lock) (some descriptor) := by
      funext path
      by_cases same : path = directory.file .lock <;> simp [LockOwners.set, same]
    rw [owners]

/-- The complete reference observation determines when the existing locked
retry trace may take its last-reference transition. If any reference
survives, the original owner still blocks cooperating recovery attempts. -/
theorem LockedMarkedReopenFailureTrace.referenceDrops
    {directory : DiskDirectory} {durable : CheckpointPublication.RunFiles}
    {initial before : LockedReopenState} {description : Nat}
    (trace : LockedMarkedReopenFailureTrace directory durable initial before)
    (ownership : before.owners.Owns directory description)
    (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
    let after := references.afterDrops drops directory before
    LockedMarkedReopenFailureTrace directory durable initial after ∧
      (after.owners (directory.file .lock) = none ↔ references.remaining drops = []) ∧
      (references.remaining drops ≠ [] → after = before) := by
  dsimp only
  by_cases last : references.remaining drops = []
  · have lengthZero : (references.remaining drops).length = 0 := by simp [last]
    have released := trace.lastReferenceClosed ⟨description, (references.remaining drops).length⟩ ownership lengthZero
    refine ⟨by simpa [HeldLockReferences.afterDrops, HeldLockReferences.ownersAfterDrops, last]
      using released, ?_, by simp [last]⟩
    simp [HeldLockReferences.afterDrops, HeldLockReferences.ownersAfterDrops, last,
      LockOwners.release_owned ownership, LockOwners.set]
  · have live : (references.remaining drops).isEmpty = false := List.isEmpty_eq_false_iff.mpr last
    have stillOwned := ownership
    change before.owners (directory.file .lock) = some description at stillOwned
    simpa [HeldLockReferences.afterDrops, HeldLockReferences.ownersAfterDrops, live, last, stillOwned] using trace

/-- A surviving reference prevents the reported open from reaching recovery. -/
theorem LockedMarkedReopenReports.whileReferenceSurvives
    {directory : DiskDirectory} {durable : CheckpointPublication.RunFiles}
    {before : LockedReopenState} {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (ownership : before.owners.Owns directory description)
    (retained : references.remaining drops ≠ [])
    (reports : LockedMarkedReopenReports directory (references.afterDrops drops directory before) durable) :
    ∃ cause, reports.run = .error cause (references.afterDrops drops directory before) := by
  apply reports.whileHeld (owner := description)
  have live := List.isEmpty_eq_false_iff.mpr retained
  simpa [HeldLockReferences.afterDrops, HeldLockReferences.ownersAfterDrops, live] using ownership

/-- An inherited reference can keep the lock after owner exit, even when it
is marked close-on-exec. A successful child exec then releases the lock if
every initial reference belonged to the exiting process or was such a
child reference. The child may keep running after the lock is released. -/
theorem LockedMarkedReopenFailureTrace.ownerExit_thenChildExec
    {directory : DiskDirectory} {durable : CheckpointPublication.RunFiles}
    {initial before : LockedReopenState} {description owner child : Nat} {inherited : LockReference}
    (trace : LockedMarkedReopenFailureTrace directory durable initial before)
    (ownership : before.owners.Owns directory description)
    (references : HeldLockReferences description) (present : inherited ∈ references.live)
    (childProcess : inherited.process = child) (distinct : child ≠ owner)
    (covered : ∀ reference ∈ references.live,
      reference.process = owner ∨ reference.process = child ∧ reference.closeOnExec = true) :
    let afterExit := references.afterDrops [.exited owner] directory before
    let afterExec := references.afterDrops [.exited owner, .executed child] directory before
    afterExit = before ∧ LockedMarkedReopenFailureTrace directory durable initial afterExec ∧
      afterExec.owners (directory.file .lock) = none := by
  have survives : inherited ∈ references.remaining [.exited owner] :=
    (references.mem_remaining _ _).mpr ⟨present, by simp [LockReferenceDrop.removes, childProcess, distinct]⟩
  have allClosed : references.remaining [.exited owner, .executed child] = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro reference remaining
    obtain ⟨known, notRemoved⟩ := (references.mem_remaining _ _).mp remaining
    rcases covered reference known with ownerReference | ⟨childReference, closeOnExec⟩
    · have afterExit := notRemoved (.exited owner) (by simp)
      simp [LockReferenceDrop.removes, ownerReference] at afterExit
    · have afterExec := notRemoved (.executed child) (by simp)
      simp [LockReferenceDrop.removes, childReference, closeOnExec] at afterExec
  obtain ⟨_, _, staysOwned⟩ := trace.referenceDrops ownership references [.exited owner]
  obtain ⟨retry, available, _⟩ := trace.referenceDrops ownership references [.exited owner, .executed child]
  exact ⟨staysOwned (List.ne_nil_of_mem survives), retry, available.mpr allClosed⟩

/-- The shared close procedure changes the phase and lock ownership.
It carries the file image unchanged in either result. -/
def runCloseWithFiles {α image : Type} (directory : DiskDirectory) (descriptor : Nat)
    (unlock : UnlockReport) : EStateM IO.Error (Phase α × LockedFileState image) Unit :=
  fun (phase, files) => match runClose directory descriptor unlock ⟨phase, files.owners⟩ with
    | .ok _ after => .ok () (after.phase, { files with owners := after.owners })
    | .error cause after => .error cause (after.phase, { files with owners := after.owners })

/-- A successful close of an owned live session preserves the reached file image. -/
theorem runCloseWithFiles_success {α image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {phase : Phase α} {before : LockedFileState image}
    (live : phase ≠ .closed) (ownership : before.owners.Owns directory descriptor) :
    runCloseWithFiles directory descriptor .success (phase, before) =
      .ok () (.closed, ⟨before.image, before.owners.set (directory.file .lock) none⟩) := by
  dsimp only [runCloseWithFiles]
  rw [runClose_open live, LockOwners.release_owned ownership]

theorem runCloseWithFiles_poisoned {α image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {before : LockedFileState image}
    (ownership : before.owners.Owns directory descriptor) {unlock : UnlockReport}
    (localUnlock : unlock.LocalFlock) :
    runCloseWithFiles directory descriptor unlock ((.poisoned : Phase α), before) =
      match unlock with
      | .success => .ok () (.closed, ⟨before.image, before.owners.set (directory.file .lock) none⟩)
      | .failure cause _ => .error cause (.poisoned, before) := by
  dsimp only [runCloseWithFiles]
  rw [runClose_open (by simp) unlock, LockOwners.release_owned ownership]
  cases unlock with
  | success => rfl
  | failure cause released =>
    change released = false at localUnlock
    subst released
    rfl

/-- An explicit close and an observed final reference drop expose the
same reached file image to the next cooperating lock acquisition. -/
theorem runCloseWithFiles_handoff {α image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {phase : Phase α} {before : LockedFileState image}
    (live : phase ≠ .closed) (ownership : before.owners.Owns directory descriptor) :
    let released : LockedFileState image :=
      ⟨before.image, before.owners.set (directory.file .lock) none⟩
    runCloseWithFiles directory descriptor .success (phase, before) = .ok () (.closed, released) ∧
      (∀ (references : HeldLockReferences descriptor) (drops : List LockReferenceDrop),
        references.remaining drops = [] → references.afterFileDrops drops directory before = released) ∧
      TryLockObserves released.owners directory (.ok true) := by
  dsimp only
  refine ⟨runCloseWithFiles_success live ownership, ?_, ?_⟩
  · intro references drops last
    exact references.afterFileDrops_released ownership last
  · simp [TryLockObserves, LockOwners.set]

end Alvoki.Storage.DiskSession
