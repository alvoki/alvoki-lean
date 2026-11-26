import Alvoki.Storage.Disk.NativeRawOpenPhaseFrame
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

/-- Each accepted seal carries the same frame to the next payload.
The traversal stops at the actual keeper, seal, or length failure. -/
theorem readsCachedWalPayloads (directory : DiskDirectory) (through : Nat)
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (seals : ∀ path length, KeepsReadFrame frame (readSeal path length))
    (keepers : ∀ path length size, KeepsReadFrame frame (readKeeper path length size))
    (required : List (Nat × IO.FS.Metadata)) :
    KeepsReadFrame frame (readCachedWalPayloads directory through readSeal readKeeper required) := by
  intro entry
  have outcome := CachedWalPayloadReturn.classifies directory through readSeal readKeeper required entry
  have atResult {run : EStateM IO.Error heap ByteArray} {before : heap} {result : EStateM.Result IO.Error heap ByteArray}
      (keeps : KeepsReadFrame frame run) (returned : run before = result) : frame before (reachedState result) :=
    returned ▸ keeps before
  generalize readCachedWalPayloads directory through readSeal readKeeper required entry = result at outcome ⊢
  induction outcome with
  | noKeeper _ | invalidOrder _ => exact refl _
  | keeperError failed => exact atResult (keepers _ _ _) failed
  | invalidKeeper read _ | kept read _ => exact atResult (keepers _ _ _) read
  | sealError _ failed => exact checkedFileOutcome (frame := frame) trans failed (.pure refl _) (seals _ _)
  | sealedThenError _ read _ remaining | sealed _ read _ remaining =>
    exact trans (checkedFileOutcome (frame := frame) trans read (.pure refl _) (seals _ _)) remaining

private theorem filters (items : List α) {action : α → EStateM IO.Error heap (Option β)}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (keeps : ∀ item, KeepsReadFrame frame (action item)) : KeepsReadFrame frame (items.filterMapM action) := by
  induction items with
  | nil => exact .pure refl []
  | cons item rest earlier =>
    simp only [List.filterMapM_cons]
    apply (keeps item).bind trans
    intro found
    cases found with
    | none => exact earlier
    | some value => exact earlier.bind trans fun values => .pure refl (value :: values)

theorem readsWalExtents (directory : DiskDirectory) (names : List String)
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (stats : ∀ path, KeepsReadFrame frame (stat path)) :
    KeepsReadFrame frame (readWalSegmentExtentsWith directory stat names) := by
  have readExtent (name : String) : KeepsReadFrame frame (readWalSegmentExtentWith directory stat name) := by
    unfold readWalSegmentExtentWith
    split
    · apply (stats _).bind trans
      intro reported
      split
      · exact .throw refl _
      · exact .pure refl _
      · exact .pure refl _
    · exact .pure refl _
  unfold readWalSegmentExtentsWith
  exact (filters names refl trans readExtent).bind trans fun _ => .pure refl _

/-- The actual selected WAL reader carries the scope through the checked
listing, extent probes and each reached payload callback. -/
theorem readsSelectedWal (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    {list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)}
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (lists : KeepsReadFrame frame (list directory.path)) (stats : ∀ path, KeepsReadFrame frame (stat path))
    (seals : ∀ path count, KeepsReadFrame frame (readSeal path count))
    (keepers : ∀ path count size, KeepsReadFrame frame (readKeeper path count size)) :
    KeepsReadFrame frame (readSelectedWithCachedExtents directory watermark length list stat readSeal readKeeper) := by
  rw [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate]
  split
  · apply lists.bind trans
    intro entries
    apply (readsWalExtents directory (entries.toList.map (·.fileName)) refl trans stats).bind trans
    intro extents
    split
    · apply (readsCachedWalPayloads directory _ refl trans seals keepers _).bind trans
      rintro ⟨files, size⟩
      exact .pure refl _
    · exact .throw refl _
  · exact .throw refl _

/-- Prepare the actual checkpoint and marker-bounded WAL with the same
frame at their reached returns. Validation and replay are pure. -/
theorem preparesMarked (directory : DiskDirectory)
    {checkpoint : EStateM IO.Error heap (Option (PackedTable × UInt64))}
    {readOptional : FilePath → EStateM IO.Error heap (Option ByteArray)}
    {readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat)}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (checkpointFrame : KeepsReadFrame frame checkpoint)
    (markerFrame : KeepsReadFrame frame (readOptional (directory.file .walBoundary)))
    (walFrame : ∀ watermark length, KeepsReadFrame frame (readWal watermark length)) :
    KeepsReadFrame frame (prepareBoundedMarkedFromReaders directory checkpoint readOptional readWal) := by
  unfold prepareBoundedMarkedFromReaders
  apply checkpointFrame.bind trans
  intro selected
  apply markerFrame.bind trans
  intro marker
  cases marker with
  | none => exact .throw refl _
  | some bytes =>
    apply (fromExcept (frame := frame) refl ((WAL.Boundary.decode bytes).mapError IO.userError)).bind trans
    intro length
    apply (walFrame (selected.getD (.empty, 0)).1.committed.toNat length).bind trans
    rintro ⟨reads, keeperSize⟩
    apply (fromExcept (frame := frame) refl
      ((recoverMarkedWalSegments (selected.getD (.empty, 0)).1 length reads.files).mapError IO.userError)).bind trans
    rintro ⟨_, table⟩
    cases found : reads.files.getLast? with
    | none =>
      simpa only [MonadExcept.throw, throwThe] using
        (KeepsReadFrame.throw (α := Plan × Reopened × Nat) refl (IO.userError "no WAL segment covers the commit marker"))
    | some last =>
      obtain ⟨keeper, bytes⟩ := last
      exact .pure refl _

end KeepsReadFrame

namespace KeepsPhase

variable {heap α β : Type} {observe : heap → Option (Phase Installed)}

private theorem asReadFrame {run : EStateM IO.Error heap α} (kept : KeepsPhase observe run) :
    KeepsReadFrame (fun before after => observe after = observe before) run := by
  intro before
  cases returned : run before <;> simpa only [returned, reachedState] using kept before

private theorem fromReadFrame {run : EStateM IO.Error heap α}
    (kept : KeepsReadFrame (fun before after => observe after = observe before) run) : KeepsPhase observe run := by
  intro before
  cases returned : run before <;> simpa only [returned, reachedState] using kept before

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

theorem readsCachedWalPayloads (directory : DiskDirectory) (through : Nat)
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (seals : ∀ path length, KeepsPhase observe (readSeal path length))
    (keepers : ∀ path length size, KeepsPhase observe (readKeeper path length size))
    (required : List (Nat × IO.FS.Metadata)) :
    KeepsPhase observe (readCachedWalPayloads directory through readSeal readKeeper required) :=
  fromReadFrame (KeepsReadFrame.readsCachedWalPayloads (frame := fun before after => observe after = observe before)
    directory through (fun _ => rfl) (fun a b => b.trans a)
    (fun path count => (seals path count).asReadFrame)
    (fun path count size => (keepers path count size).asReadFrame) required)

theorem readsWalExtents (directory : DiskDirectory) (names : List String)
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    (stats : ∀ path, KeepsPhase observe (stat path)) :
    KeepsPhase observe (readWalSegmentExtentsWith directory stat names) :=
  fromReadFrame (KeepsReadFrame.readsWalExtents (frame := fun before after => observe after = observe before)
    directory names (fun _ => rfl) (fun a b => b.trans a)
    (fun path => (stats path).asReadFrame))

theorem readsSelectedWal (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    {list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)}
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    (lists : KeepsPhase observe (list directory.path)) (stats : ∀ path, KeepsPhase observe (stat path))
    (seals : ∀ path count, KeepsPhase observe (readSeal path count))
    (keepers : ∀ path count size, KeepsPhase observe (readKeeper path count size)) :
    KeepsPhase observe (readSelectedWithCachedExtents directory watermark length list stat readSeal readKeeper) :=
  fromReadFrame (KeepsReadFrame.readsSelectedWal (frame := fun before after => observe after = observe before)
    directory watermark length (fun _ => rfl) (fun a b => b.trans a)
    lists.asReadFrame (fun path => (stats path).asReadFrame)
    (fun path count => (seals path count).asReadFrame) (fun path count size => (keepers path count size).asReadFrame))

theorem preparesMarked (directory : DiskDirectory)
    {checkpoint : EStateM IO.Error heap (Option (PackedTable × UInt64))}
    {readOptional : FilePath → EStateM IO.Error heap (Option ByteArray)}
    {readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat)}
    (checkpointFrame : KeepsPhase observe checkpoint)
    (markerFrame : KeepsPhase observe (readOptional (directory.file .walBoundary)))
    (walFrame : ∀ watermark length, KeepsPhase observe (readWal watermark length)) :
    KeepsPhase observe (prepareBoundedMarkedFromReaders directory checkpoint readOptional readWal) :=
  fromReadFrame (KeepsReadFrame.preparesMarked (frame := fun before after => observe after = observe before)
    directory (fun _ => rfl) (fun a b => b.trans a) checkpointFrame.asReadFrame markerFrame.asReadFrame
    (fun watermark length => (walFrame watermark length).asReadFrame))

end KeepsPhase

end Alvoki.Storage.DiskSession
