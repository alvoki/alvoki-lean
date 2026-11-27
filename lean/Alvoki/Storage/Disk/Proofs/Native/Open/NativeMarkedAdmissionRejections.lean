import Alvoki.Storage.Disk.Proofs.Native.Open.NativeMarkedOpenInterpreter
import Alvoki.Storage.Disk.Proofs.Recovery.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeContendedAliasAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage}
  {input : FilePath} {entry : heap} {directory : DiskDirectory}

/-- Factor the guarded append-open from the continuation that receives
the newly opened lock. Every prefix error returns at its own reached heap. -/
private theorem RawOpenAdmissionCallbacks.withOpenAdmission_afterPrefix (calls : RawOpenAdmissionCallbacks heap)
    (input : FilePath) (continueOpen : DiskDirectory → IO.FS.Handle → EStateM IO.Error heap α) :
    DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend continueOpen =
      (do
        let (directory, lock) ← calls.beforeFlock input
        continueOpen directory lock) := by
  unfold RawOpenAdmissionCallbacks.beforeFlock
  simp only [DiskTable.withOpenAdmission, bind_assoc]
  congr 1
  funext directory
  congr 1
  funext _
  congr 1
  funext metadata
  cases metadata <;> simp only [bind_assoc, pure_bind]

/-- The fixed interpreter returns the exact first prefix error. No lock
handle was returned to its continuation, so no cleanup runs there. -/
theorem RawMarkedOpenInterpreter.returnsBeforeFlock (source : RawMarkedOpenInterpreter heap stream)
    {cause : IO.Error} {reached : heap} (failed : source.calls.beforeFlock input entry = .error cause reached) :
    source.openTable input entry = .error cause reached ∧
    RawOpenPrefixReturn source.calls input entry (.error cause reached) := by
  refine ⟨?_, failed ▸ source.calls.classifiesBeforeFlock input entry⟩
  unfold RawMarkedOpenInterpreter.openTable
  rw [source.calls.withOpenAdmission_afterPrefix]
  simp only [Bind.bind, EStateM.bind, failed]

theorem RawBeforeFlockRejection.returnsMarkedInterpreter (source : RawMarkedOpenInterpreter heap stream)
    (seen : RawBeforeFlockRejection view source.calls input entry) :
    source.openTable input entry = .error seen.cause seen.reached ∧
    RawOpenPrefixReturn source.calls input entry (.error seen.cause seen.reached) :=
  source.returnsBeforeFlock seen.failed

private theorem reachedState_bindWithoutEffects {α β : Type}
    (first : EStateM IO.Error heap α) (next : α → EStateM IO.Error heap β)
    (keeps : ∀ value reached, reachedState (next value reached) = reached) :
    reachedState ((first >>= next) entry) = reachedState (first entry) := by
  cases ran : first entry with
  | error => simp only [Bind.bind, EStateM.bind, ran, reachedState]
  | ok value reached =>
    simpa only [Bind.bind, EStateM.bind, ran, reachedState] using keeps value reached

private theorem openWith_reachedState (realPath : FilePath → EStateM IO.Error heap FilePath) :
    reachedState (DiskDirectory.openWith realPath input entry) = reachedState (realPath input entry) := by
  unfold DiskDirectory.openWith
  apply reachedState_bindWithoutEffects
  intro path reached
  split <;> rfl

private theorem checkLock_reachedState (calls : RawOpenAdmissionCallbacks heap) :
    reachedState (calls.checkLock directory entry) = reachedState (calls.lookup (directory.file .lock) entry) := by
  rw [← optionalMetadata_reachedState (calls.lookup (directory.file .lock))]
  unfold RawOpenAdmissionCallbacks.checkLock
  apply reachedState_bindWithoutEffects
  intro metadata reached
  cases metadata with
  | none => rfl
  | some stat =>
    dsimp only
    unfold checkPrivateRegularWith
    split <;> rfl

/-- Local frames for the actual calls of a pre-flock failure. Only
the reached append error can need a separate non-read-only law. -/
structure RawOpenAdmissionCallbacks.BeforeFlockErrorFrames
    (calls : RawOpenAdmissionCallbacks heap) (input : FilePath) (entry : heap) (cause : IO.Error) (reached : heap)
    (frame : heap → heap → Prop) : Prop where
  realPath : frame entry (reachedState (calls.realPath input entry))
  lookup : ∀ path atHeap, frame atHeap (reachedState (calls.lookup path atHeap))
  appendError : ∀ {resolvedDirectory afterResolve afterFlat afterGuard},
    DiskDirectory.openWith calls.realPath input entry = .ok resolvedDirectory afterResolve →
    rejectFlatWalWith resolvedDirectory (optionalMetadataWith (calls.lookup (resolvedDirectory.file .wal)))
      afterResolve = .ok () afterFlat →
    calls.checkLock resolvedDirectory afterFlat = .ok () afterGuard →
    calls.openAppend (resolvedDirectory.file .lock) afterGuard = .error cause reached →
    frame afterGuard reached

/-- The returned pre-flock failure frames the projection through only
the reached path and metadata calls. A failed append by itself carries
no guarantee about the returned descriptor or name projections. -/
theorem RawOpenPrefixReturn.framesRejected {calls : RawOpenAdmissionCallbacks heap}
    {cause : IO.Error} {reached : heap} (rejected : RawOpenPrefixReturn calls input entry (.error cause reached))
    {frame : heap → heap → Prop}
    (trans : ∀ {before intermediate after}, frame before intermediate → frame intermediate after → frame before after)
    (effects : calls.BeforeFlockErrorFrames input entry cause reached frame) :
    frame entry reached := by
  have resolvedFrame : frame entry (reachedState (DiskDirectory.openWith calls.realPath input entry)) := by
    rw [openWith_reachedState]; exact effects.realPath
  have flatFrame (resolvedDirectory : DiskDirectory) (afterResolve : heap) :
      frame afterResolve (reachedState (rejectFlatWalWith resolvedDirectory
        (optionalMetadataWith (calls.lookup (resolvedDirectory.file .wal))) afterResolve)) := by
    rw [rejectFlatWal_reachedState]; exact effects.lookup (resolvedDirectory.file .wal) afterResolve
  have lockFrame (resolvedDirectory : DiskDirectory) (afterFlat : heap) :
      frame afterFlat (reachedState (calls.checkLock resolvedDirectory afterFlat)) := by
    rw [checkLock_reachedState]; exact effects.lookup (resolvedDirectory.file .lock) afterFlat
  cases rejected with
  | resolveError resolved => simpa only [resolved, reachedState] using resolvedFrame
  | @flatError resolvedDirectory afterResolve _ _ resolved flat =>
    exact trans (by simpa only [resolved, reachedState] using resolvedFrame)
      (by simpa only [flat, reachedState] using flatFrame resolvedDirectory afterResolve)
  | @lockGuardError resolvedDirectory afterResolve afterFlat _ _ resolved flat checked =>
    exact trans (by simpa only [resolved, reachedState] using resolvedFrame)
      (trans (by simpa only [flat, reachedState] using flatFrame resolvedDirectory afterResolve)
        (by simpa only [checked, reachedState] using lockFrame resolvedDirectory afterFlat))
  | @appendError resolvedDirectory afterResolve afterFlat afterGuard _ _ resolved flat checked appended =>
    exact trans (by simpa only [resolved, reachedState] using resolvedFrame)
      (trans (by simpa only [flat, reachedState] using flatFrame resolvedDirectory afterResolve)
        (trans (by simpa only [checked, reachedState] using lockFrame resolvedDirectory afterFlat)
          (effects.appendError resolved flat checked appended)))

/-- The same callback chain supplies the actual public error and
frames any observation carried by the later retry. -/
theorem RawMarkedOpenInterpreter.framesBeforeFlock (source : RawMarkedOpenInterpreter heap stream)
    {cause : IO.Error} {reached : heap} (failed : source.calls.beforeFlock input entry = .error cause reached)
    {frame : heap → heap → Prop}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (effects : source.calls.BeforeFlockErrorFrames input entry cause reached frame) :
    source.openTable input entry = .error cause reached ∧ frame entry reached := by
  obtain ⟨returned, rejected⟩ := source.returnsBeforeFlock failed
  exact ⟨returned, rejected.framesRejected trans effects⟩

private theorem RawOpenAdmissionCallbacks.framesBeforeFlockSuccess (calls : RawOpenAdmissionCallbacks heap)
    {lock : IO.FS.Handle} {issued : heap}
    (opened : calls.beforeFlock input entry = .ok (directory, lock) issued)
    {frame : heap → heap → Prop} (trans : ∀ {a b c}, frame a b → frame b c → frame a c)
    (resolve : frame entry (reachedState (calls.realPath input entry)))
    (lookup : ∀ path atHeap, frame atHeap (reachedState (calls.lookup path atHeap)))
    (append : ∀ {before}, calls.openAppend (directory.file .lock) before = .ok lock issued →
      frame before issued) : frame entry issued := by
  obtain ⟨r, f, g, resolved, flat, checked, appended⟩ := calls.beforeFlock_steps opened
  have hr : frame entry r := by
    rw [← openWith_reachedState, resolved] at resolve
    exact resolve
  have hf := lookup (directory.file .wal) r
  have hg := lookup (directory.file .lock) f
  rw [← rejectFlatWal_reachedState, flat] at hf
  rw [← checkLock_reachedState, checked] at hg
  exact trans hr (trans hf (trans hg (append appended)))

/-- A non-granting flock returns after the lock handle's own scope
finalizer. Both diagnostics bypass cache allocation and the held worker. -/
theorem RawMarkedOpenInterpreter.returnsRefusedFlock (source : RawMarkedOpenInterpreter heap stream)
    {lock : IO.FS.Handle} {issued refused : heap} {cause : IO.Error}
    (opened : source.calls.beforeFlock input entry = .ok (directory, lock) issued)
    (outcome : source.calls.flock lock issued = .error cause refused ∨
      source.calls.flock lock issued = .ok false refused ∧ cause = IO.userError s!"database already open: {directory.path}") :
    source.openTable input entry = .error cause (source.release lock refused) := by
  unfold RawMarkedOpenInterpreter.openTable
  rw [source.calls.withOpenAdmission_afterPrefix]
  rcases outcome with failed | ⟨busy, rfl⟩
  · simp only [Bind.bind, EStateM.bind, opened, finishFailedOpen, openWithLock, failed]
  · simp only [Bind.bind, EStateM.bind, opened, finishFailedOpen, openWithLock, busy, Bool.false_eq_true,
      ↓reduceIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Transport a scoped observation across the reached admission callbacks,
the non-granting flock, and finalization of the very handle just opened. -/
theorem RawMarkedOpenInterpreter.framesRefusedFlock (source : RawMarkedOpenInterpreter heap stream)
    {lock : IO.FS.Handle} {issued refused reached : heap} {cause publicCause : IO.Error}
    (opened : source.calls.beforeFlock input entry = .ok (directory, lock) issued)
    (outcome : source.calls.flock lock issued = .error cause refused ∨
      source.calls.flock lock issued = .ok false refused ∧ cause = IO.userError s!"database already open: {directory.path}")
    (returned : source.openTable input entry = .error publicCause reached)
    {frame : heap → heap → Prop} (trans : ∀ {a b c}, frame a b → frame b c → frame a c)
    (resolve : frame entry (reachedState (source.calls.realPath input entry)))
    (lookup : ∀ path atHeap, frame atHeap (reachedState (source.calls.lookup path atHeap)))
    (append : ∀ {before}, source.calls.openAppend (directory.file .lock) before = .ok lock issued →
      frame before issued)
    (flock : frame issued refused) (release : frame refused (source.release lock refused)) :
    frame entry reached := by
  obtain ⟨_, endpoint⟩ := EStateM.Result.error.inj ((source.returnsRefusedFlock opened outcome).symm.trans returned)
  exact endpoint ▸ trans (source.calls.framesBeforeFlockSuccess opened trans resolve lookup append) (trans flock release)

/-- A directory-open failure ends initialization before any reference is allocated. -/
theorem RawMarkedOpenInterpreter.cacheInitialization_error_of_directoryOpenError
    (source : RawMarkedOpenInterpreter heap stream) {held failedHeap : heap} {cause : IO.Error}
    (failed : source.init.openDirectory directory.path held = .error cause failedHeap) :
    source.cacheInitialization directory held = .error cause failedHeap := by
  simp only [RawMarkedOpenInterpreter.cacheInitialization, openSyncFilesWith, Bind.bind, EStateM.bind, failed]

/-- Failure of the fixed initializer reaches unlock and lock release,
including when unlock returns an error. The worker's cache finalizer
requires an assembled cache. Any drop of a temporary directory handle
during partial initialization belongs to the initializer observation. -/
theorem RawMarkedOpenInterpreter.returnsCacheInitializationError (source : RawMarkedOpenInterpreter heap stream)
    {lock : IO.FS.Handle} {issued held failedHeap : heap} {cause : IO.Error}
    (opened : source.calls.beforeFlock input entry = .ok (directory, lock) issued)
    (acquired : source.calls.flock lock issued = .ok true held)
    (failed : source.cacheInitialization directory held = .error cause failedHeap) :
    source.openTable input entry = match source.calls.unlock lock failedHeap with
      | .ok () beforeRelease => .error cause (source.release lock beforeRelease)
      | .error cleanup beforeRelease => .error cleanup (source.release lock beforeRelease) := by
  unfold RawMarkedOpenInterpreter.openTable
  rw [source.calls.withOpenAdmission_afterPrefix]
  simp only [Bind.bind, EStateM.bind, opened, finishFailedOpen, openWithLock, acquired, ↓reduceIte,
    failed, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    EStateM.Backtrackable.restore, EStateM.dummyRestore, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  cases source.calls.unlock lock failedHeap with
  | ok value beforeRelease => cases value; rfl
  | error cleanup beforeRelease => rfl

/-- Compose scoped frames at the reached initialization error and the
two lock cleanup callbacks. The public error identifies the final heap. -/
theorem RawMarkedOpenInterpreter.framesCacheInitializationError (source : RawMarkedOpenInterpreter heap stream)
    {lock : IO.FS.Handle} {issued held failedHeap reached : heap} {cause publicCause : IO.Error}
    (opened : source.calls.beforeFlock input entry = .ok (directory, lock) issued)
    (acquired : source.calls.flock lock issued = .ok true held)
    (failed : source.cacheInitialization directory held = .error cause failedHeap)
    (returned : source.openTable input entry = .error publicCause reached)
    {frame : heap → heap → Prop} (trans : ∀ {a b c}, frame a b → frame b c → frame a c)
    (resolve : frame entry (reachedState (source.calls.realPath input entry)))
    (lookup : ∀ path atHeap, frame atHeap (reachedState (source.calls.lookup path atHeap)))
    (append : ∀ {before}, source.calls.openAppend (directory.file .lock) before = .ok lock issued →
      frame before issued)
    (flock : frame issued held) (initializer : frame held failedHeap)
    (unlock : frame failedHeap (reachedState (source.calls.unlock lock failedHeap)))
    (release : let beforeRelease := reachedState (source.calls.unlock lock failedHeap)
      frame beforeRelease (source.release lock beforeRelease)) : frame entry reached := by
  have actual := (source.returnsCacheInitializationError opened acquired failed).symm.trans returned
  have endpoint : source.release lock (reachedState (source.calls.unlock lock failedHeap)) = reached := by
    cases unlocked : source.calls.unlock lock failedHeap with
    | ok value beforeRelease =>
      cases value
      rw [unlocked] at actual
      exact (EStateM.Result.error.inj actual).2
    | error cleanup beforeRelease =>
      rw [unlocked] at actual
      exact (EStateM.Result.error.inj actual).2
  exact endpoint ▸ trans (source.calls.framesBeforeFlockSuccess opened trans resolve lookup append)
    (trans flock (trans initializer (trans unlock release)))

/-- A flock error on the actual append handle bypasses the held worker.
The error reaches the caller after the interpreter releases that handle. -/
theorem RawFlockRejection.returnsMarkedInterpreter (source : RawMarkedOpenInterpreter heap stream)
    (seen : RawFlockRejection view source.calls directory source.release input entry) :
    source.openTable input entry = .error seen.report.cause seen.reached := by
  simpa only [seen.finalized.finalized, RawFlockRejection.reached] using
    source.returnsRefusedFlock seen.report.opened (.inl seen.report.flock)

/-- A contending opener never initializes a cache or enters recovery.
It closes the exact descriptor returned by the guarded append-open. -/
theorem RawContendedAliasOpen.returnsMarkedInterpreter (source : RawMarkedOpenInterpreter heap stream)
    {description : Nat} {namespaceView : DirectoryReadNamespace} {root : DeviceInode}
    (seen : RawContendedAliasOpen view source.calls source.release directory description namespaceView root input entry) :
    source.openTable input entry = .error seen.diagnostic seen.finalized.reached := by
  simpa only [seen.finalized.finalized, RawContendedAliasOpen.diagnostic] using
    source.returnsRefusedFlock seen.opened (.inr ⟨seen.busy, rfl⟩)

end Alvoki.Storage.DiskSession
