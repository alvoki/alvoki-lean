import Alvoki.Storage.Disk.NativeMarkedOpenInterpreter
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.NativeContendedAliasAdmission

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

private theorem optionalMetadata_reachedState
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) :
    reachedState (optionalMetadataWith lookup entry) = reachedState (lookup entry) := by
  unfold optionalMetadataWith
  apply reachedState_bindWithoutEffects
  intro result reached
  cases result with
  | ok => rfl
  | error cause =>
    cases cause <;> try rfl
    rename_i name code message
    by_cases missing : code = 2
    · subst code
      rfl
    · simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reachedState]

private theorem rejectFlatWal_reachedState
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) :
    reachedState (rejectFlatWalWith directory (optionalMetadataWith lookup) entry) = reachedState (lookup entry) := by
  rw [← optionalMetadata_reachedState lookup]
  unfold rejectFlatWalWith
  apply reachedState_bindWithoutEffects
  intro metadata reached
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

/-- A flock error on the actual append handle bypasses the held worker.
The error reaches the caller after the interpreter releases that handle. -/
theorem RawFlockRejection.returnsMarkedInterpreter (source : RawMarkedOpenInterpreter heap stream)
    (seen : RawFlockRejection view source.calls directory source.release input entry) :
    source.openTable input entry = .error seen.report.cause seen.reached := by
  unfold RawMarkedOpenInterpreter.openTable
  rw [source.calls.withOpenAdmission_afterPrefix]
  simp only [Bind.bind, EStateM.bind, seen.report.opened, finishFailedOpen, openWithLock, seen.report.flock,
    seen.finalized.finalized, RawFlockRejection.reached]

/-- A contending opener never initializes a cache or enters recovery.
It closes the exact descriptor returned by the guarded append-open. -/
theorem RawContendedAliasOpen.returnsMarkedInterpreter (source : RawMarkedOpenInterpreter heap stream)
    {description : Nat} {namespaceView : DirectoryReadNamespace} {root : DeviceInode}
    (seen : RawContendedAliasOpen view source.calls source.release directory description namespaceView root input entry) :
    source.openTable input entry = .error seen.diagnostic seen.finalized.reached := by
  unfold RawMarkedOpenInterpreter.openTable
  rw [source.calls.withOpenAdmission_afterPrefix]
  simp only [Bind.bind, EStateM.bind, seen.opened, finishFailedOpen, openWithLock, seen.busy, Bool.false_eq_true,
    ↓reduceIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw, seen.finalized.finalized,
    RawContendedAliasOpen.diagnostic]

end Alvoki.Storage.DiskSession
