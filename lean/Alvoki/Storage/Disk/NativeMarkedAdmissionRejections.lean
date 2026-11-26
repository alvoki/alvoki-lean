import Alvoki.Storage.Disk.NativeMarkedOpenInterpreter
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.NativeContendedAliasAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

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
