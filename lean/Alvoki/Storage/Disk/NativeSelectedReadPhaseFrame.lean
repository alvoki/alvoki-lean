import Alvoki.Storage.Disk.NativeMarkedOpenPhaseFrame
import Alvoki.Storage.Disk.NativeCheckpointReadReturn

namespace Alvoki.Storage.DiskSession.KeepsPhase

open System Manifest

variable {heap α β : Type} {observe : heap → Option (Phase Installed)}

private theorem onSuccess {run : EStateM IO.Error heap α} (frame : KeepsPhase observe run)
    {before after : heap} {value : α} (returned : run before = .ok value after) : observe after = observe before := by
  simpa only [returned] using frame before

private theorem onError {run : EStateM IO.Error heap α} (frame : KeepsPhase observe run)
    {before after : heap} {cause : IO.Error} (returned : run before = .error cause after) : observe after = observe before := by
  simpa only [returned] using frame before

/-- The actual reported size guard cannot modify the original phase.
If the bounded prefix is reached, its phase guarantee starts at the
precise heap returned by the size callback. -/
theorem readsExactFile (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (sized : KeepsPhase observe (readSize path)) (payload : KeepsPhase observe (readPrefix path expected)) :
    KeepsPhase observe (readExactRecoveryFileWith path expected mismatch readSize readPrefix) := by
  intro entry
  have outcome := ExactRecoveryFileReturn.classifies path expected mismatch readSize readPrefix entry
  generalize readExactRecoveryFileWith path expected mismatch readSize readPrefix entry = result at outcome ⊢
  cases outcome with
  | sizeError failed => exact sized.onError failed
  | wrongSize measured _ => exact sized.onSuccess measured
  | prefixError measured _ failed => exact (payload.onError failed).trans (sized.onSuccess measured)
  | wrongPrefix measured _ returned | accepted measured _ returned _ =>
    exact (payload.onSuccess returned).trans (sized.onSuccess measured)

private theorem traverses (items : List α) {action : α → EStateM IO.Error heap β}
    (frame : ∀ item, KeepsPhase observe (action item)) : KeepsPhase observe (items.mapM action) := by
  induction items with
  | nil => exact .pure []
  | cons item rest earlier =>
    simp only [List.mapM_cons]
    exact (frame item).bind fun value => earlier.bind fun values => .pure (value :: values)

/-- Read stamped runs in manifest order, retaining the old phase at the
success or first failure of the actual checkpoint loop. -/
theorem readsIntegrityRunBytes (directory : DiskDirectory) (manifest : IntegrityCheckpoint)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (sizes : ∀ path, KeepsPhase observe (readSize path))
    (prefixes : ∀ path count, KeepsPhase observe (readPrefix path count)) :
    KeepsPhase observe (readIntegrityRunBytesSized directory manifest readSize readPrefix) := by
  simp only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM]
  apply traverses
  intro index
  change KeepsPhase observe ((do
    let some stamp := manifest.runs.toArray[index]? | MonadExcept.throw (IO.userError checkpointIntegrityMismatch)
    readExactRecoveryFileWith (directory.file (.run manifest.header.generation index))
      stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) readSize readPrefix) :
    EStateM IO.Error heap ByteArray)
  split
  · exact readsExactFile _ _ _ (sizes _) (prefixes _ _)
  · simpa only [MonadExcept.throw, throwThe] using
      (KeepsPhase.throw (observe := observe) (α := ByteArray) (IO.userError checkpointIntegrityMismatch))

private theorem readingExcept (result : Except IO.Error α) :
    KeepsPhase observe (liftExcept result : EStateM IO.Error heap α) := by
  cases result with
  | ok value => exact .pure value
  | error cause => exact .throw cause

theorem readsIntegrityCheckpoint (directory : DiskDirectory)
    {readManifest : EStateM IO.Error heap (Option ByteArray)}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (manifest : KeepsPhase observe readManifest)
    (sizes : ∀ path, KeepsPhase observe (readSize path))
    (prefixes : ∀ path count, KeepsPhase observe (readPrefix path count)) :
    KeepsPhase observe (readIntegrityCheckpointSized directory readManifest readSize readPrefix) := by
  unfold readIntegrityCheckpointSized
  apply manifest.bind
  intro found
  cases found with
  | none => exact .pure none
  | some bytes =>
    apply (readingExcept ((IntegrityCheckpoint.decode bytes).mapError IO.userError)).bind
    intro decoded
    apply (readsIntegrityRunBytes directory decoded sizes prefixes).bind
    intro runs
    exact (readingExcept ((loadIntegrityRunSet decoded runs).mapError IO.userError)).bind
      fun table => .pure (some (table, decoded.header.generation))

end Alvoki.Storage.DiskSession.KeepsPhase
