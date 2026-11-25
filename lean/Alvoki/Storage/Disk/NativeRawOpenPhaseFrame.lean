import Alvoki.Storage.Disk.NativeFinalizedOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap α β : Type} {observe : heap → Option (Phase Installed)}

/-- Preserve an already allocated phase cell across either result of an
interpreted callback. The observation is bound to the original cell. -/
def KeepsPhase (observe : heap → Option (Phase Installed)) (run : EStateM IO.Error heap α) : Prop :=
  ∀ before, match run before with
    | .ok _ after | .error _ after => observe after = observe before

namespace KeepsPhase

theorem pure (value : α) : KeepsPhase observe (Pure.pure value) := fun _ => rfl

theorem throw (cause : IO.Error) : KeepsPhase observe (MonadExceptOf.throw cause : EStateM IO.Error heap α) :=
  fun _ => rfl

theorem bind {run : EStateM IO.Error heap α} {next : α → EStateM IO.Error heap β}
    (first : KeepsPhase observe run) (rest : ∀ value, KeepsPhase observe (next value)) :
    KeepsPhase observe (run >>= next) := by
  intro before
  have kept := first before
  cases returned : run before with
  | error cause after =>
    simpa only [Bind.bind, EStateM.bind, returned] using kept
  | ok value after =>
    rw [returned] at kept
    have followed := rest value after
    simp only [Bind.bind, EStateM.bind, returned]
    cases outcome : next value after <;> rw [outcome] at followed <;> exact followed.trans kept

theorem handle {run : EStateM IO.Error heap α} {recover : IO.Error → EStateM IO.Error heap α}
    (main : KeepsPhase observe run) (handler : ∀ cause, KeepsPhase observe (recover cause)) :
    KeepsPhase observe (tryCatchThe IO.Error run recover) := by
  intro before
  have kept := main before
  cases returned : run before with
  | ok value after =>
    simpa only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, returned] using kept
  | error cause after =>
    rw [returned] at kept
    have followed := handler cause after
    simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, returned,
      EStateM.Backtrackable.restore, EStateM.dummyRestore]
    cases outcome : recover cause after <;> rw [outcome] at followed <;> exact followed.trans kept

end KeepsPhase

/-- Primitive effects on the native open prefix and its cache initialize
other objects and leave the original phase cell untouched. -/
structure RawOpenPhaseFrame (observe : heap → Option (Phase Installed))
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap) : Prop where
  realPath : ∀ path, KeepsPhase observe (calls.realPath path)
  stat : ∀ path, KeepsPhase observe (calls.lookup path)
  openAppend : ∀ path, KeepsPhase observe (calls.openAppend path)
  flock : ∀ lock, KeepsPhase observe (calls.flock lock)
  unlock : ∀ lock, KeepsPhase observe (calls.unlock lock)
  openDirectory : ∀ path, KeepsPhase observe (init.openDirectory path)
  newRef : ∀ {γ : Type} (value : γ), KeepsPhase observe (init.newRef value)

private theorem RawOpenPhaseFrame.withAdmission {calls : RawOpenAdmissionCallbacks heap}
    {init : OpenSyncCacheCallbacks heap} (frame : RawOpenPhaseFrame observe calls init) (input : FilePath)
    {continueOpen : DiskDirectory → IO.FS.Handle → EStateM IO.Error heap α}
    (continueFrame : ∀ directory lock, KeepsPhase observe (continueOpen directory lock)) :
    KeepsPhase observe (DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend continueOpen) := by
  have metadata (path : FilePath) : KeepsPhase observe (optionalMetadataWith (calls.lookup path)) := by
    unfold optionalMetadataWith
    apply (frame.stat path).bind
    intro value
    split <;> first | exact .pure _ | exact .throw _
  have resolved : KeepsPhase observe (DiskDirectory.openWith calls.realPath input) := by
    unfold DiskDirectory.openWith
    apply (frame.realPath input).bind
    intro path
    split
    · exact .pure _
    · exact .throw _
  unfold DiskTable.withOpenAdmission
  apply resolved.bind
  intro directory
  have noFlat : KeepsPhase observe
      (rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))) := by
    unfold rejectFlatWalWith
    apply (metadata (directory.file .wal)).bind
    intro result
    split
    · exact .throw _
    · exact .pure _
  apply noFlat.bind
  intro _
  apply (metadata (directory.file .lock)).bind
  intro binding
  have append := (frame.openAppend (directory.file .lock)).bind (continueFrame directory)
  cases binding with
  | none => exact append
  | some lockMetadata =>
    have checked : KeepsPhase observe (checkPrivateRegularWith (directory.file .lock) lockMetadata) := by
      unfold checkPrivateRegularWith
      split
      · exact .pure _
      · exact .throw _
    exact checked.bind fun _ => append

/-- The fixed ordinary admission prefix preserves the old reference
through the reached resolution, metadata guards and append. -/
theorem RawOpenPhaseFrame.beforeFlock {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
    (frame : RawOpenPhaseFrame observe calls init) (input : FilePath) :
    KeepsPhase observe (calls.beforeFlock input) :=
  frame.withAdmission input fun directory lock => .pure (directory, lock)

theorem RawOpenPhaseFrame.runOpen {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
    (frame : RawOpenPhaseFrame observe calls init) (input : FilePath)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    {recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α}
    (worker : ∀ directory lock cache, KeepsPhase observe (recover directory lock cache)) :
    KeepsPhase observe (calls.runOpen input init makeCache recover) := by
  unfold RawOpenAdmissionCallbacks.runOpen
  apply frame.withAdmission input
  intro directory lock
  unfold openWithLock
  have initialized : KeepsPhase observe (openSyncFilesWith (init.openDirectory directory.path)
      init.newRef init.newRef init.newRef makeCache) := by
    unfold openSyncFilesWith
    exact (frame.openDirectory directory.path).bind fun handle =>
      (frame.newRef (some handle)).bind fun directoryRef =>
        (frame.newRef none).bind fun active =>
          (frame.newRef []).bind fun pending => .pure (makeCache directoryRef active pending)
  have finished := (initialized.bind (worker directory lock)).handle
    (fun cause => (frame.unlock lock).bind (fun _ => .throw cause))
  apply (frame.flock lock).bind
  intro acquired
  cases acquired with
  | false =>
    simpa [tryCatchThe, MonadExcept.tryCatch, throw, throwThe] using
      (KeepsPhase.throw (observe := observe) (α := Unit)
        (IO.userError s!"database already open: {directory.path}")).bind (fun _ => finished)
  | true => simpa [tryCatchThe, MonadExcept.tryCatch, throw, throwThe] using finished

/-- On the successful route, new phase and token allocations leave the
original cell unchanged when their primitive effects preserve that cell. -/
theorem RawOpenPhaseFrame.installs {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
    (frame : RawOpenPhaseFrame observe calls init) (input : FilePath)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    {recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened}
    (worker : ∀ directory lock cache, KeepsPhase observe (recover directory lock cache))
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    (phaseAllocation : ∀ phase, KeepsPhase observe (allocatePhase phase))
    (tokenAllocation : KeepsPhase observe (allocateToken ()))
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable) :
    KeepsPhase observe (calls.runOpen input init makeCache (fun directory lock cache => do
      let opened ← recover directory lock cache
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble directory lock cache phase token)))) := by
  apply frame.runOpen input makeCache
  intro directory lock cache
  apply (worker directory lock cache).bind
  intro opened
  unfold installReady
  exact (phaseAllocation (.ready opened.installed)).bind fun phase =>
    tokenAllocation.bind fun token => .pure (assemble directory lock cache phase token)

variable {view : OpenCloseHeapView heap WalSegmentRepair.FileImage}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {directory : DiskDirectory}

/-- The original phase survives an actual failed open if its worker,
cache disposal and lock finalizer preserve that reference. Neither the
chosen diagnostic nor the success of unlock affects the phase. -/
theorem RawFinalizedOpenAttempt.keepsPhase {input : FilePath} {entry : heap}
    (attempt : RawFinalizedOpenAttempt view directory calls init release input entry)
    (admissionFrame : RawOpenPhaseFrame observe calls init)
    (worker : ∀ root lock cache, KeepsPhase observe (attempt.recover root lock cache))
    (dispose : ∀ cache, KeepsPhase observe (attempt.disposed.dispose cache))
    (releaseLock : ∀ lock before, observe (release lock before) = observe before) :
    observe attempt.reached = observe entry := by
  obtain ⟨_, makeCache, _, _, returned, _, _, _⟩ := attempt.returns
  have scope (root : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) :
      KeepsPhase observe (attempt.disposed.errorScope attempt.recover root lock cache) :=
    (worker root lock cache).handle (fun cause => (dispose cache).bind (fun _ => .throw cause))
  have kept := (admissionFrame.runOpen input makeCache scope) entry
  cases outcome : calls.runOpen input init makeCache (attempt.disposed.errorScope attempt.recover) entry with
  | ok value after =>
    simp only [finishFailedOpen, outcome] at returned
    cases returned
  | error cause after =>
    simp only [finishFailedOpen, outcome, EStateM.Result.error.injEq] at returned
    rw [← returned.2, releaseLock]
    simpa only [outcome] using kept

/-- The exact next caller heap is used for each failed open. Apply the
primitive phase frame and the reported worker and finalizer scopes in
that order to transport the original phase through the whole prefix. -/
theorem RawFinalizedOpenAttempts.keepsPhase {start reached : heap} {errors : List (FilePath × IO.Error)}
    (attempts : RawFinalizedOpenAttempts view directory calls init release start errors reached)
    (admissionFrame : RawOpenPhaseFrame observe calls init)
    (worker : ∀ input entry (seen : RawFinalizedOpenAttempt view directory calls init release input entry),
      ∀ root lock cache, KeepsPhase observe (seen.recover root lock cache))
    (dispose : ∀ input entry (seen : RawFinalizedOpenAttempt view directory calls init release input entry),
      ∀ cache, KeepsPhase observe (seen.disposed.dispose cache))
    (releaseLock : ∀ lock entry, observe (release lock entry) = observe entry) :
    observe reached = observe start := by
  induction attempts with
  | empty => rfl
  | @beforeFlock _ entry _ input refused prior =>
    have kept := (admissionFrame.beforeFlock input) entry
    rw [refused.failed] at kept
    exact kept.trans prior
  | @flockError _ entry _ input refused prior =>
    have appended := (admissionFrame.beforeFlock input) entry
    rw [refused.report.opened] at appended
    have failed := admissionFrame.flock refused.report.handle refused.report.atFlock
    rw [refused.report.flock] at failed
    have closed := releaseLock refused.report.handle refused.report.reached
    rw [refused.finalized.finalized] at closed
    exact closed.trans (failed.trans (appended.trans prior))
  | attempt _ _ input seen prior =>
    exact (seen.keepsPhase admissionFrame (worker input _ seen) (dispose input _ seen) releaseLock).trans prior

end Alvoki.Storage.DiskSession
