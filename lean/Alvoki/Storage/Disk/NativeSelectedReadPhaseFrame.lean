import Alvoki.Storage.Disk.NativeMarkedOpenPhaseFrame
import Alvoki.Storage.Disk.NativeCheckpointReadReturn
import Alvoki.Storage.Disk.NativeWalPayloadReturn

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair SyncHandleRouting

/-- A read's return retains a scoped observation from its entry heap,
including when one of its callbacks reports an error. -/
def KeepsReadFrame {heap α : Type} (frame : heap → heap → Prop) (run : EStateM IO.Error heap α) : Prop :=
  ∀ before, frame before (reachedState (run before))

namespace KeepsReadFrame

variable {heap α β : Type} {frame : heap → heap → Prop}

theorem bind {run : EStateM IO.Error heap α} {next : α → EStateM IO.Error heap β}
    (first : KeepsReadFrame frame run)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (rest : ∀ value, KeepsReadFrame frame (next value)) :
    KeepsReadFrame frame (run >>= next) := by
  intro before
  have kept := first before
  cases returned : run before with
  | error cause after => simpa only [Bind.bind, EStateM.bind, returned, reachedState] using kept
  | ok value after =>
    rw [returned] at kept
    simpa only [Bind.bind, EStateM.bind, returned] using trans kept (rest value after)

theorem pure (refl : ∀ atHeap, frame atHeap atHeap) (value : α) :
    KeepsReadFrame frame (Pure.pure value) := refl

theorem throw (refl : ∀ atHeap, frame atHeap atHeap) (cause : IO.Error) :
    KeepsReadFrame frame (MonadExceptOf.throw cause : EStateM IO.Error heap α) := refl

theorem fromExcept (refl : ∀ atHeap, frame atHeap atHeap) (result : Except IO.Error α) :
    KeepsReadFrame frame (liftExcept result : EStateM IO.Error heap α) := by
  cases result with
  | ok value => exact .pure refl value
  | error cause => exact .throw refl cause

private theorem traverses (items : List α) {action : α → EStateM IO.Error heap β}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (keeps : ∀ item, KeepsReadFrame frame (action item)) : KeepsReadFrame frame (items.mapM action) := by
  induction items with
  | nil => exact .pure refl []
  | cons item rest earlier =>
    simp only [List.mapM_cons]
    exact (keeps item).bind trans fun value => earlier.bind trans fun values => .pure refl (value :: values)

private theorem checkedFileOutcome {path : FilePath} {expected : Nat} {mismatch : IO.Error}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {entry : heap} {result : EStateM.Result IO.Error heap ByteArray}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (outcome : ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry result)
    (sized : KeepsReadFrame frame (readSize path)) (payload : KeepsReadFrame frame (readPrefix path expected)) :
    frame entry (reachedState result) := by
  cases outcome with
  | sizeError failed => simpa only [failed, reachedState] using sized entry
  | wrongSize measured _ => simpa only [measured, reachedState] using sized entry
  | @prefixError afterSize _ _ measured _ returned
  | @wrongPrefix afterSize _ _ measured _ returned _
  | @accepted afterSize _ _ measured _ returned _ =>
    have measuredFrame : frame entry afterSize := by simpa only [measured, reachedState] using sized entry
    exact trans measuredFrame (by simpa only [returned, reachedState] using payload afterSize)

/-- The size guard preserves the reached state. A reached payload read
continues from the heap returned by the size callback. -/
theorem readsExactFile (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (sized : KeepsReadFrame frame (readSize path)) (payload : KeepsReadFrame frame (readPrefix path expected)) :
    KeepsReadFrame frame (readExactRecoveryFileWith path expected mismatch readSize readPrefix) := by
  intro entry
  exact checkedFileOutcome trans (ExactRecoveryFileReturn.classifies path expected mismatch readSize readPrefix entry)
    sized payload

/-- Follow each reached run in manifest order, including the first
returned failure. -/
theorem readsIntegrityRunBytes (directory : DiskDirectory) (manifest : IntegrityCheckpoint)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (sizes : ∀ path, KeepsReadFrame frame (readSize path))
    (prefixes : ∀ path count, KeepsReadFrame frame (readPrefix path count)) :
    KeepsReadFrame frame (readIntegrityRunBytesSized directory manifest readSize readPrefix) := by
  simp only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM]
  apply traverses _ refl trans
  intro index
  change KeepsReadFrame frame ((do
    let some stamp := manifest.runs.toArray[index]? | MonadExcept.throw (IO.userError checkpointIntegrityMismatch)
    readExactRecoveryFileWith (directory.file (.run manifest.header.generation index))
      stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) readSize readPrefix) :
    EStateM IO.Error heap ByteArray)
  split
  · exact readsExactFile _ _ _ trans (sizes _) (prefixes _ _)
  · simpa only [MonadExcept.throw, throwThe] using
      (KeepsReadFrame.throw (α := ByteArray) refl (IO.userError checkpointIntegrityMismatch))

/-- The actual strict reader carries the same frame through manifest
admission, each reached run and restoration or error. -/
theorem readsIntegrityCheckpoint (directory : DiskDirectory)
    {readManifest : EStateM IO.Error heap (Option ByteArray)}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (manifest : KeepsReadFrame frame readManifest)
    (sizes : ∀ path, KeepsReadFrame frame (readSize path))
    (prefixes : ∀ path count, KeepsReadFrame frame (readPrefix path count)) :
    KeepsReadFrame frame (readIntegrityCheckpointSized directory readManifest readSize readPrefix) := by
  unfold readIntegrityCheckpointSized
  apply manifest.bind trans
  intro found
  cases found with
  | none => exact .pure refl none
  | some bytes =>
    apply (fromExcept refl ((IntegrityCheckpoint.decode bytes).mapError IO.userError)).bind trans
    intro decoded
    apply (readsIntegrityRunBytes directory decoded refl trans sizes prefixes).bind trans
    intro runs
    exact (fromExcept refl ((loadIntegrityRunSet decoded runs).mapError IO.userError)).bind trans
      fun table => .pure refl (some (table, decoded.header.generation))

end KeepsReadFrame

namespace KeepsPhase

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

private theorem asReadFrame {run : EStateM IO.Error heap α} (kept : KeepsPhase observe run) :
    KeepsReadFrame (fun before after => observe after = observe before) run := by
  intro before
  cases returned : run before <;> simpa only [returned, reachedState] using kept before

private theorem fromReadFrame {run : EStateM IO.Error heap α}
    (kept : KeepsReadFrame (fun before after => observe after = observe before) run) : KeepsPhase observe run := by
  intro before
  cases returned : run before <;> simpa only [returned, reachedState] using kept before

private theorem checkedFileOutcome {path : FilePath} {expected : Nat} {mismatch : IO.Error}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {entry : heap} {result : EStateM.Result IO.Error heap ByteArray}
    (outcome : ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry result)
    (sized : KeepsPhase observe (readSize path)) (payload : KeepsPhase observe (readPrefix path expected)) :
    phaseAtResult observe entry result := by
  have kept := KeepsReadFrame.checkedFileOutcome (fun left right => right.trans left)
    outcome sized.asReadFrame payload.asReadFrame
  cases result <;> exact kept

theorem readsExactFile (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (sized : KeepsPhase observe (readSize path)) (payload : KeepsPhase observe (readPrefix path expected)) :
    KeepsPhase observe (readExactRecoveryFileWith path expected mismatch readSize readPrefix) :=
  fromReadFrame (KeepsReadFrame.readsExactFile path expected mismatch (fun a b => b.trans a)
    sized.asReadFrame payload.asReadFrame)

theorem readsIntegrityRunBytes (directory : DiskDirectory) (manifest : IntegrityCheckpoint)
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (sizes : ∀ path, KeepsPhase observe (readSize path))
    (prefixes : ∀ path count, KeepsPhase observe (readPrefix path count)) :
    KeepsPhase observe (readIntegrityRunBytesSized directory manifest readSize readPrefix) :=
  fromReadFrame (KeepsReadFrame.readsIntegrityRunBytes directory manifest (fun _ => rfl) (fun a b => b.trans a)
    (fun path => (sizes path).asReadFrame) (fun path count => (prefixes path count).asReadFrame))

theorem readsIntegrityCheckpoint (directory : DiskDirectory)
    {readManifest : EStateM IO.Error heap (Option ByteArray)}
    {readSize : FilePath → EStateM IO.Error heap Nat}
    {readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    (manifest : KeepsPhase observe readManifest)
    (sizes : ∀ path, KeepsPhase observe (readSize path))
    (prefixes : ∀ path count, KeepsPhase observe (readPrefix path count)) :
    KeepsPhase observe (readIntegrityCheckpointSized directory readManifest readSize readPrefix) :=
  fromReadFrame (KeepsReadFrame.readsIntegrityCheckpoint directory (fun _ => rfl) (fun a b => b.trans a)
    manifest.asReadFrame (fun path => (sizes path).asReadFrame) (fun path count => (prefixes path count).asReadFrame))

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

end KeepsPhase

end Alvoki.Storage.DiskSession
