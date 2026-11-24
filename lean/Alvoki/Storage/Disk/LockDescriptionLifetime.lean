import Alvoki.Storage.Disk.LockedMarkedReopenFailureTrace

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

/-- Release only the matching lock when the completed events consumed every
reference. The owner map and file image need no other change. -/
def HeldLockReferences.afterDrops {description : Nat}
    (references : HeldLockReferences description) (drops : List LockReferenceDrop)
    (directory : DiskDirectory) (before : LockedReopenState) : LockedReopenState :=
  if (references.remaining drops).isEmpty then
    ⟨before.image, before.owners.release (directory.file .lock) description⟩
  else before

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
    refine ⟨by simpa [HeldLockReferences.afterDrops, last] using released, ?_, by simp [last]⟩
    simp [HeldLockReferences.afterDrops, last, LockOwners.release_owned ownership, LockOwners.set]
  · have live : (references.remaining drops).isEmpty = false := List.isEmpty_eq_false_iff.mpr last
    have stillOwned := ownership
    change before.owners (directory.file .lock) = some description at stillOwned
    simpa [HeldLockReferences.afterDrops, live, last, stillOwned] using trace

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
  simpa [HeldLockReferences.afterDrops, live] using ownership

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

end Alvoki.Storage.DiskSession
