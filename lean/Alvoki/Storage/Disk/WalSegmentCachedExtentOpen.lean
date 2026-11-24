import Alvoki.Storage.Disk.RecoverySizedReads
import Alvoki.Storage.Disk.WalSegmentSizedCheckpointOpen
import Alvoki.Storage.Disk.WalSegmentCollectionPlan

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

def selectedWalSpanError : IO.Error :=
  IO.userError "invalid selected WAL segment spans"

/-- Keep the call's admitted metadata attached to the selected paths. -/
def selectWalExtentsThrough (extents : List (Nat × IO.FS.Metadata)) (watermark through : Nat) :
    Option (List (Nat × IO.FS.Metadata) × List Nat) := do
  let first ← ((extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max?
  let selected := extents.filter (fun entry => decide (first ≤ entry.1))
  let needed := fun (entry : Nat × IO.FS.Metadata) => decide (entry.1 ≤ through)
  pure (selected.takeWhile needed, (selected.dropWhile needed).map Prod.fst)

/-- Keeping metadata changes neither the selected path order nor the repair names. -/
theorem selectWalExtentsThrough_offsets (extents : List (Nat × IO.FS.Metadata)) (watermark through : Nat) :
    (selectWalExtentsThrough extents watermark through).map (fun selection => (selection.1.map Prod.fst, selection.2)) =
      selectWalSegmentReadsThrough (extents.map Prod.fst) watermark through := by
  unfold selectWalExtentsThrough selectWalSegmentReadsThrough selectWalSegmentReads
  cases ((extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max? <;>
    simp [Option.bind, Bind.bind, Option.map, Pure.pure, List.filter_map, List.takeWhile_map,
      List.dropWhile_map, Function.comp_def]

private def readCachedWalPayloadsFrom [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → m ByteArray)
    (readKeeper : FilePath → Nat → Nat → m ByteArray) :
    List (Nat × IO.FS.Metadata) → List (Nat × ByteArray) → m (List (Nat × ByteArray) × Nat)
  | [], _ => throw (IO.userError "no WAL segment covers the commit marker")
  | [(first, metadata)], read => do
    let count := (through - first) * frameSize
    let fileSize := metadata.byteSize.toNat
    let bytes ← readKeeper (dir.file (.walSegment first)) count fileSize
    unless bytes.size = count ∧ count ≤ fileSize do
      throw (IO.userError "invalid WAL keeper prefix or physical size")
    pure (((first, bytes) :: read).reverse, fileSize)
  | (first, metadata) :: (next, nextMetadata) :: remaining, read => do
    unless first < next do throw selectedWalSpanError
    let bytes ← readExactRecoveryFileWith (dir.file (.walSegment first)) ((next - first) * frameSize)
      selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal
    readCachedWalPayloadsFrom dir through readSeal readKeeper ((next, nextMetadata) :: remaining) ((first, bytes) :: read)

/-- Each seal must match the adjacent selected offset before opening its payload.
The keeper's original lstat extent determines whether repair needs to replace it. -/
def readCachedWalPayloads [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → m ByteArray)
    (readKeeper : FilePath → Nat → Nat → m ByteArray)
    (required : List (Nat × IO.FS.Metadata)) : m (List (Nat × ByteArray) × Nat) :=
  readCachedWalPayloadsFrom dir through readSeal readKeeper required []

def readSelectedWithCachedExtents [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (watermark : Nat) (length : UInt64) (list : FilePath → m (Array IO.FS.DirEntry))
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) (readSeal : FilePath → Nat → m ByteArray)
    (readKeeper : FilePath → Nat → Nat → m ByteArray) : m (WalSegmentMarkerReads × Nat) := do
  let through := length.toNat / frameSize
  unless length.toNat % frameSize = 0 ∧ watermark ≤ through do
    throw (IO.userError "invalid absolute WAL segment marker")
  let entries ← list dir.path
  let extents ← readWalSegmentExtentsWith dir lstat (entries.toList.map (·.fileName))
  let some (required, newer) := selectWalExtentsThrough extents watermark through
    | throw (IO.userError "no WAL segment covers the checkpoint watermark")
  let (files, fileSize) ← readCachedWalPayloads dir through readSeal readKeeper required
  pure (⟨files, newer⟩, fileSize)

private theorem readCachedWalPayloadsFrom_rejectsSeal {state : Type} (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error state ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    (first next : Nat) (metadata nextMetadata : IO.FS.Metadata) (rest : List (Nat × IO.FS.Metadata))
    (read : List (Nat × ByteArray)) (initial : state)
    (wrong : ¬ (metadata.byteSize.toNat = (next - first) * frameSize ∧ (next - first) * frameSize < USize.size)) :
    readCachedWalPayloadsFrom dir through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
      read initial = .error selectedWalSpanError initial := by
  have rejected := readExactRecoveryFileWith_rejectsSize (dir.file (.walSegment first)) ((next - first) * frameSize)
    selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal (initial := initial) rfl wrong
  change readExactRecoveryFileWith (dir.file (.walSegment first)) ((next - first) * frameSize)
    selectedWalSpanError (fun _ => EStateM.pure metadata.byteSize.toNat) readSeal initial =
    .error selectedWalSpanError initial at rejected
  by_cases forward : first < next
  · simp [readCachedWalPayloadsFrom, forward, Bind.bind, EStateM.bind, rejected, Pure.pure]
  · simp [readCachedWalPayloadsFrom, forward, Bind.bind, EStateM.bind, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

/-- A wrong held extent returns before either the seal read or any later read. -/
theorem readCachedWalPayloads_rejectsSeal {state : Type} (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error state ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    (first next : Nat) (metadata nextMetadata : IO.FS.Metadata) (rest : List (Nat × IO.FS.Metadata))
    (initial : state)
    (wrong : ¬ (metadata.byteSize.toNat = (next - first) * frameSize ∧ (next - first) * frameSize < USize.size)) :
    readCachedWalPayloads dir through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest) initial =
      .error selectedWalSpanError initial :=
  readCachedWalPayloadsFrom_rejectsSeal dir through readSeal readKeeper first next metadata nextMetadata rest [] initial wrong

private theorem readCachedWalPayloadsFrom_afterSealed {state : Type} (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error state ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    (first next : Nat) (metadata nextMetadata : IO.FS.Metadata) (rest : List (Nat × IO.FS.Metadata))
    (read : List (Nat × ByteArray)) {initial observed : state} {bytes : ByteArray}
    (forward : first < next) (extent : metadata.byteSize.toNat = (next - first) * frameSize)
    (fits : (next - first) * frameSize < USize.size)
    (reported : readSeal (dir.file (.walSegment first)) ((next - first) * frameSize) initial = .ok bytes observed)
    (size : bytes.size = (next - first) * frameSize) :
    readCachedWalPayloadsFrom dir through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
      read initial = readCachedWalPayloadsFrom dir through readSeal readKeeper ((next, nextMetadata) :: rest)
        ((first, bytes) :: read) observed := by
  have admitted := readExactRecoveryFileWith_accepts (dir.file (.walSegment first)) ((next - first) * frameSize)
    selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal
    (initial := initial) (observed := initial) (final := observed)
    fits (by simp [extent, Pure.pure, EStateM.pure])
    reported size
  change readExactRecoveryFileWith (dir.file (.walSegment first)) ((next - first) * frameSize)
    selectedWalSpanError (fun _ => EStateM.pure metadata.byteSize.toNat) readSeal initial =
    .ok bytes observed at admitted
  simp [readCachedWalPayloadsFrom, forward, Bind.bind, EStateM.bind, Pure.pure, admitted]

/-- A reached extent rejection can follow exact, successful reads of earlier seals. -/
inductive CachedWalExtentFailure {state : Type} (dir : DiskDirectory)
    (readSeal : FilePath → Nat → EStateM IO.Error state ByteArray) :
    List (Nat × IO.FS.Metadata) → state → state → Prop where
  | rejected {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {rest : List (Nat × IO.FS.Metadata)}
      {initial : state}
      (wrong : ¬ (metadata.byteSize.toNat = (next - first) * frameSize ∧ (next - first) * frameSize < USize.size)) :
      CachedWalExtentFailure dir readSeal ((first, metadata) :: (next, nextMetadata) :: rest) initial initial
  | acceptedPrefix {first next : Nat} {metadata nextMetadata : IO.FS.Metadata}
      {rest : List (Nat × IO.FS.Metadata)} {initial observed reached : state} {bytes : ByteArray}
      (forward : first < next) (extent : metadata.byteSize.toNat = (next - first) * frameSize)
      (fits : (next - first) * frameSize < USize.size)
      (reported : readSeal (dir.file (.walSegment first)) ((next - first) * frameSize) initial = .ok bytes observed)
      (size : bytes.size = (next - first) * frameSize)
      (failed : CachedWalExtentFailure dir readSeal ((next, nextMetadata) :: rest) observed reached) :
      CachedWalExtentFailure dir readSeal ((first, metadata) :: (next, nextMetadata) :: rest) initial reached

theorem readCachedWalPayloads_extentFailure {state : Type} {dir : DiskDirectory} (through : Nat)
    {readSeal : FilePath → Nat → EStateM IO.Error state ByteArray}
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    {required : List (Nat × IO.FS.Metadata)} {initial reached : state}
    (failed : CachedWalExtentFailure dir readSeal required initial reached) :
    readCachedWalPayloads dir through readSeal readKeeper required initial = .error selectedWalSpanError reached := by
  have loop (read : List (Nat × ByteArray)) :
      readCachedWalPayloadsFrom dir through readSeal readKeeper required read initial =
        .error selectedWalSpanError reached := by
    induction failed generalizing read with
    | rejected wrong =>
      exact readCachedWalPayloadsFrom_rejectsSeal dir through readSeal readKeeper _ _ _ _ _ read _ wrong
    | @acceptedPrefix first next metadata nextMetadata rest initial observed reached bytes
        forward extent fits reported size failed ih =>
      rw [readCachedWalPayloadsFrom_afterSealed dir through readSeal readKeeper first next metadata nextMetadata rest
        read forward extent fits reported size]
      exact ih _
  exact loop []

/-- Read-only prefix reports preserve the file image from before the first selected seal read. -/
theorem CachedWalExtentFailure.reached_eq_of_readonly {state : Type} {dir : DiskDirectory}
    {readSeal : FilePath → Nat → EStateM IO.Error state ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {initial reached : state}
    (failed : CachedWalExtentFailure dir readSeal required initial reached)
    (readOnly : ∀ path count before bytes after, readSeal path count before = .ok bytes after → after = before) :
    reached = initial := by
  induction failed with
  | rejected => rfl
  | acceptedPrefix _ _ _ reported _ _ ih => exact ih.trans (readOnly _ _ _ _ _ reported)

/-- Exact successful seal reads leading to the final selected keeper. -/
inductive CachedWalKeeperReached {state : Type} (dir : DiskDirectory)
    (readSeal : FilePath → Nat → EStateM IO.Error state ByteArray)
    (keeper : Nat) (keeperMetadata : IO.FS.Metadata) :
    List (Nat × IO.FS.Metadata) → state → state → Prop where
  | noSeals {initial : state} : CachedWalKeeperReached dir readSeal keeper keeperMetadata
      [(keeper, keeperMetadata)] initial initial
  | sealed {first next : Nat} {metadata nextMetadata : IO.FS.Metadata}
      {rest : List (Nat × IO.FS.Metadata)} {initial observed reached : state} {bytes : ByteArray}
      (forward : first < next) (extent : metadata.byteSize.toNat = (next - first) * frameSize)
      (fits : (next - first) * frameSize < USize.size)
      (reported : readSeal (dir.file (.walSegment first)) ((next - first) * frameSize) initial = .ok bytes observed)
      (size : bytes.size = (next - first) * frameSize)
      (remaining : CachedWalKeeperReached dir readSeal keeper keeperMetadata
        ((next, nextMetadata) :: rest) observed reached) :
      CachedWalKeeperReached dir readSeal keeper keeperMetadata
        ((first, metadata) :: (next, nextMetadata) :: rest) initial reached

/-- The keeper error is returned at its reached state after the earlier seals. -/
theorem CachedWalKeeperReached.read_error {state : Type} {dir : DiskDirectory} (through : Nat)
    {readSeal : FilePath → Nat → EStateM IO.Error state ByteArray}
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    {keeper : Nat} {metadata : IO.FS.Metadata} {required : List (Nat × IO.FS.Metadata)}
    {initial reached after : state} {cause : IO.Error}
    (seals : CachedWalKeeperReached dir readSeal keeper metadata required initial reached)
    (failed : readKeeper (dir.file (.walSegment keeper)) ((through - keeper) * frameSize)
      metadata.byteSize.toNat reached = .error cause after) :
    readCachedWalPayloads dir through readSeal readKeeper required initial = .error cause after := by
  have loop (read : List (Nat × ByteArray)) :
      readCachedWalPayloadsFrom dir through readSeal readKeeper required read initial = .error cause after := by
    induction seals generalizing read with
    | noSeals => simp [readCachedWalPayloadsFrom, Bind.bind, EStateM.bind, failed]
    | @sealed first next metadata nextMetadata rest initial observed reached bytes
        forward extent fits reported size remaining ih =>
      rw [readCachedWalPayloadsFrom_afterSealed dir through readSeal readKeeper first next metadata nextMetadata rest
        read forward extent fits reported size]
      exact ih failed _
  exact loop []

/-- Read-only seal observations preserve the state until the keeper read. -/
theorem CachedWalKeeperReached.reached_eq_of_readonly {state : Type} {dir : DiskDirectory}
    {readSeal : FilePath → Nat → EStateM IO.Error state ByteArray}
    {keeper : Nat} {metadata : IO.FS.Metadata} {required : List (Nat × IO.FS.Metadata)} {initial reached : state}
    (seals : CachedWalKeeperReached dir readSeal keeper metadata required initial reached)
    (readOnly : ∀ path count before bytes after, readSeal path count before = .ok bytes after → after = before) :
    reached = initial := by
  induction seals with
  | noSeals => rfl
  | sealed _ _ _ reported _ _ ih => exact ih.trans (readOnly _ _ _ _ _ reported)

/-- Exact size and byte observations for the selected stable file bindings. -/
inductive CachedWalPayloadReports (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray) :
    List (Nat × IO.FS.Metadata) → List (Nat × ByteArray) → Nat → Prop where
  | keeper {first : Nat} {metadata : IO.FS.Metadata} {bytes : ByteArray}
      (size : bytes.size = (through - first) * frameSize)
      (covers : (through - first) * frameSize ≤ metadata.byteSize.toNat)
      (read : readKeeper (dir.file (.walSegment first)) ((through - first) * frameSize) metadata.byteSize.toNat =
        .ok bytes) :
      CachedWalPayloadReports dir through readSeal readKeeper [(first, metadata)] [(first, bytes)] metadata.byteSize.toNat
  | sealed {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {bytes nextBytes : ByteArray}
      {rest : List (Nat × IO.FS.Metadata)} {later : List (Nat × ByteArray)} {fileSize : Nat}
      (forward : first < next) (size : bytes.size = (next - first) * frameSize)
      (extent : metadata.byteSize.toNat = bytes.size) (fits : bytes.size < USize.size)
      (read : readSeal (dir.file (.walSegment first)) bytes.size = .ok bytes)
      (nextRead : CachedWalPayloadReports dir through readSeal readKeeper
        ((next, nextMetadata) :: rest) ((next, nextBytes) :: later) fileSize) :
      CachedWalPayloadReports dir through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
        ((first, bytes) :: (next, nextBytes) :: later) fileSize

/-- Successful payload reports fill exactly the selected start-to-marker range. -/
theorem CachedWalPayloadReports.byteCount {dir : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir through readSeal readKeeper required files fileSize)
    (covered : ∀ entry ∈ required, entry.1 ≤ through) :
    (files.map (fun item => item.2.size)).sum =
      (through - (required.head?.map Prod.fst).getD through) * frameSize := by
  induction reports with
  | keeper size _ _ => simpa using size
  | @sealed first next metadata nextMetadata bytes nextBytes rest later fileSize forward size _ _ _ _ ih =>
    have nextCovered : next ≤ through := covered (next, nextMetadata) (by simp)
    have remainder : ∀ entry ∈ (next, nextMetadata) :: rest, entry.1 ≤ through :=
      fun entry member => covered entry (List.mem_cons_of_mem _ member)
    have width : next - first + (through - next) = through - first := by omega
    change bytes.size + (((next, nextBytes) :: later).map (fun item => item.2.size)).sum =
      (through - first) * frameSize
    rw [size, ih remainder]
    change (next - first) * frameSize + (through - next) * frameSize = (through - first) * frameSize
    rw [← Nat.add_mul, width]

private theorem readCachedWalPayloadsFrom_reported [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    {dir : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray}
    {sealAction : FilePath → Nat → m ByteArray}
    {keeperAction : FilePath → Nat → Nat → m ByteArray}
    (sealOk : ∀ path count bytes, readSeal path count = .ok bytes → sealAction path count = pure bytes)
    (keeperOk : ∀ path count size bytes,
      readKeeper path count size = .ok bytes → keeperAction path count size = pure bytes)
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir through readSeal readKeeper required files fileSize)
    (before : List (Nat × ByteArray)) :
    readCachedWalPayloadsFrom dir through sealAction keeperAction required before =
      pure (before.reverse ++ files, fileSize) := by
  induction reports generalizing before with
  | keeper size covers read =>
    simp [readCachedWalPayloadsFrom, keeperOk _ _ _ _ read, size, covers]
  | sealed forward size extent fits read nextRead ih =>
    simp [readCachedWalPayloadsFrom, forward, readExactRecoveryFileWith, extent, ← size, sealOk _ _ _ read, fits, ih]

theorem readCachedWalPayloads_reported {dir : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir through readSeal readKeeper required files fileSize) :
    readCachedWalPayloads dir through readSeal readKeeper required = .ok (files, fileSize) := by
  change _ = (pure (files, fileSize) : Except IO.Error _)
  simpa [readCachedWalPayloads] using readCachedWalPayloadsFrom_reported
    (m := Except IO.Error) (sealAction := readSeal) (keeperAction := readKeeper)
    (fun _ _ _ exactRead => exactRead) (fun _ _ _ _ exactRead => exactRead) reports []

/-- Exact successful byte reports leave the repair interpreter state unchanged. -/
theorem readCachedWalPayloads_reportedEffects {state : Type} {dir : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir through readSeal readKeeper required files fileSize) :
    (readCachedWalPayloads dir through (fun path count => liftExcept (readSeal path count))
      (fun path count size => liftExcept (readKeeper path count size)) required :
        EStateM IO.Error state (List (Nat × ByteArray) × Nat)) = pure (files, fileSize) := by
  simpa [readCachedWalPayloads] using readCachedWalPayloadsFrom_reported
    (m := EStateM IO.Error state)
    (sealAction := fun path count => liftExcept (readSeal path count))
    (keeperAction := fun path count size => liftExcept (readKeeper path count size))
    (fun _ _ _ exactRead => by rw [exactRead]; rfl)
    (fun _ _ _ _ exactRead => by rw [exactRead]; rfl) reports []

theorem readSelectedWithCachedExtents_reported (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list dir.path = .ok entries)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith dir lstat (entries.toList.map (·.fileName)) = .ok extents)
    (selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, newer))
    {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir (length.toNat / frameSize) readSeal readKeeper required files fileSize) :
    readSelectedWithCachedExtents dir watermark length list lstat readSeal readKeeper =
      .ok (⟨files, newer⟩, fileSize) := by
  simp [readSelectedWithCachedExtents, checked, listed, scanned, selected, readCachedWalPayloads_reported reports,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Use the checked extent for each selected checkpoint run and each selected
WAL segment, then use the shared replay and repair. -/
def reopenMarkedBoundedWithCachedExtents [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (readRunSize : FilePath → m Nat) (readRunPrefix : FilePath → Nat → m ByteArray)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → m ByteArray) (readKeeper : FilePath → Nat → Nat → m ByteArray)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let (plan, reopened, keeperFileSize) ← prepareBoundedMarkedFromReaders dir
    (readIntegrityCheckpointSized dir (readOptional (dir.file .manifest)) readRunSize readRunPrefix)
    readOptional (fun watermark length => readSelectedWithCachedExtents dir watermark length list lstat readSeal readKeeper)
  finishBoundedMarkedOpen dir plan keeperFileSize removeFile write sync renameFile
  return reopened

/-- Equal checkpoint and WAL observations share the same installed table
and filesystem repair. Here both routes already use the sized checkpoint reader. -/
theorem reopenMarkedBoundedWithCachedExtents_eq_of_wal [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (readOptional : FilePath → m (Option ByteArray))
    (readRunSize : FilePath → m Nat) (readRunPrefix : FilePath → Nat → m ByteArray)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → m ByteArray) (readKeeper : FilePath → Nat → Nat → m ByteArray)
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit)
    (wal : ∀ watermark length, readSelectedWithCachedExtents dir watermark length list lstat readSeal readKeeper =
      readSelectedWithPrefix dir watermark length list lstat readBin readPrefix) :
    reopenMarkedBoundedWithCachedExtents dir readOptional readRunSize readRunPrefix list lstat readSeal readKeeper
      removeFile write sync renameFile =
    reopenMarkedBoundedWithSizedCheckpoint dir readOptional readRunSize readRunPrefix list lstat readBin readPrefix
      removeFile write sync renameFile := by
  unfold reopenMarkedBoundedWithCachedExtents reopenMarkedBoundedWithSizedCheckpoint prepareBoundedMarkedFromCheckpoint
  rw [funext (fun watermark => funext (wal watermark))]

end Alvoki.Storage.WalSegmentRepair
