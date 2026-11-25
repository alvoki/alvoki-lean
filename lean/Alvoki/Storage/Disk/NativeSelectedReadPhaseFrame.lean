import Alvoki.Storage.Disk.NativeMarkedOpenPhaseFrame
import Alvoki.Storage.Disk.NativeCheckpointReadReturn
import Alvoki.Storage.Disk.NativeWalPayloadReturn

namespace Alvoki.Storage.DiskSession.KeepsPhase

open System Manifest WalSegmentRepair

variable {heap α β : Type} {observe : heap → Option (Phase Installed)}

private theorem onSuccess {run : EStateM IO.Error heap α} (frame : KeepsPhase observe run)
    {before after : heap} {value : α} (returned : run before = .ok value after) : observe after = observe before := by
  simpa only [returned] using frame before

private theorem onError {run : EStateM IO.Error heap α} (frame : KeepsPhase observe run)
    {before after : heap} {cause : IO.Error} (returned : run before = .error cause after) : observe after = observe before := by
  simpa only [returned] using frame before

private def phaseAtResult (observe : heap → Option (Phase Installed)) (entry : heap)
    (result : EStateM.Result IO.Error heap α) : Prop :=
  match result with | .ok _ after | .error _ after => observe after = observe entry

private theorem checkedFileOutcome {path : FilePath} {expected : Nat} {mismatch : IO.Error}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {entry : heap} {result : EStateM.Result IO.Error heap ByteArray}
    (outcome : ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry result)
    (sized : KeepsPhase observe (readSize path)) (payload : KeepsPhase observe (readPrefix path expected)) :
    phaseAtResult observe entry result := by
  cases outcome with
  | sizeError failed => exact sized.onError failed
  | wrongSize measured _ => exact sized.onSuccess measured
  | prefixError measured _ failed => exact (payload.onError failed).trans (sized.onSuccess measured)
  | wrongPrefix measured _ returned | accepted measured _ returned _ =>
    exact (payload.onSuccess returned).trans (sized.onSuccess measured)

/-- The actual reported size guard cannot modify the original phase.
If the bounded prefix is reached, its phase guarantee starts at the
precise heap returned by the size callback. -/
theorem readsExactFile (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (sized : KeepsPhase observe (readSize path)) (payload : KeepsPhase observe (readPrefix path expected)) :
    KeepsPhase observe (readExactRecoveryFileWith path expected mismatch readSize readPrefix) := by
  intro entry
  change phaseAtResult observe entry _
  exact checkedFileOutcome (ExactRecoveryFileReturn.classifies path expected mismatch readSize readPrefix entry) sized payload

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

/-- Each actual seal and keeper outcome of the selected WAL reader
preserves the original phase. The phase frame for an accepted seal
links its reached heap to that of the subsequent selected file. -/
theorem readsCachedWalPayloads (directory : DiskDirectory) (through : Nat)
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (seals : ∀ path length, KeepsPhase observe (readSeal path length))
    (keepers : ∀ path length size, KeepsPhase observe (readKeeper path length size))
    (required : List (Nat × IO.FS.Metadata)) :
    KeepsPhase observe (readCachedWalPayloads directory through readSeal readKeeper required) := by
  intro entry
  change phaseAtResult observe entry _
  have outcome := CachedWalPayloadReturn.classifies directory through readSeal readKeeper required entry
  generalize readCachedWalPayloads directory through readSeal readKeeper required entry = result at outcome ⊢
  induction outcome with
  | noKeeper _ | invalidOrder _ => rfl
  | keeperError failed => exact (keepers _ _ _).onError failed
  | invalidKeeper read _ | kept read _ => exact (keepers _ _ _).onSuccess read
  | sealError _ failed => exact checkedFileOutcome failed (.pure _) (seals _ _)
  | sealedThenError _ read _ remaining | sealed _ read _ remaining =>
    exact remaining.trans (checkedFileOutcome read (.pure _) (seals _ _))

private theorem filters (items : List α) {action : α → EStateM IO.Error heap (Option β)}
    (frame : ∀ item, KeepsPhase observe (action item)) : KeepsPhase observe (items.filterMapM action) := by
  induction items with
  | nil => exact .pure []
  | cons item rest earlier =>
    simp only [List.filterMapM_cons]
    apply (frame item).bind
    intro found
    cases found with
    | none => exact earlier
    | some value => exact earlier.bind fun values => .pure (value :: values)

theorem readsWalExtents (directory : DiskDirectory) (names : List String)
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    (stats : ∀ path, KeepsPhase observe (stat path)) :
    KeepsPhase observe (readWalSegmentExtentsWith directory stat names) := by
  have readExtent (name : String) : KeepsPhase observe (readWalSegmentExtentWith directory stat name) := by
    unfold readWalSegmentExtentWith
    split
    · apply (stats _).bind
      intro reported
      split
      · exact .throw _
      · exact .pure _
      · exact .pure _
    · exact .pure _
  unfold readWalSegmentExtentsWith
  exact (filters names readExtent).bind fun _ => .pure _

/-- The actual selected WAL reading program preserves the original phase
from checked listing and lstat through every selected payload callback. -/
theorem readsSelectedWal (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    {list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)}
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (lists : KeepsPhase observe (list directory.path)) (stats : ∀ path, KeepsPhase observe (stat path))
    (seals : ∀ path count, KeepsPhase observe (readSeal path count))
    (keepers : ∀ path count size, KeepsPhase observe (readKeeper path count size)) :
    KeepsPhase observe (readSelectedWithCachedExtents directory watermark length list stat readSeal readKeeper) := by
  unfold readSelectedWithCachedExtents
  by_cases valid : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize
  · simp only [valid]
    apply lists.bind
    intro entries
    apply (readsWalExtents directory (entries.toList.map (·.fileName)) stats).bind
    intro extents
    split
    · apply (readsCachedWalPayloads directory _ seals keepers _).bind
      rintro ⟨files, size⟩
      exact .pure _
    · exact .throw _
  · intro before
    simp [valid, Bind.bind, EStateM.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.DiskSession.KeepsPhase
