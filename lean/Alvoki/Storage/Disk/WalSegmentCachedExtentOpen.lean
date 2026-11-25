import Alvoki.Storage.Disk.RecoverySizedReads
import Alvoki.Storage.Disk.RecoveryRequestCount
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

open RecoveryRequestCount in
private theorem readCachedWalPayloadsFrom_payloadCallsBound (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error Nat ByteArray)
    (sealBound : ∀ path count before, reached (readSeal path count before) ≤ before + count)
    (keeperBound : ∀ path count size before, reached (readKeeper path count size before) ≤ before + count)
    (required : List (Nat × IO.FS.Metadata)) (within : ∀ extent ∈ required, extent.1 ≤ through)
    (read : List (Nat × ByteArray)) (before : Nat) :
    reached (readCachedWalPayloadsFrom dir through readSeal readKeeper required read before) ≤
      before + (through - (required.head?.map Prod.fst).getD through) * frameSize := by
  induction required generalizing read before with
  | nil =>
    simp [readCachedWalPayloadsFrom, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
  | cons first rest ih =>
    obtain ⟨first, metadata⟩ := first
    cases rest with
    | nil =>
      let count := (through - first) * frameSize
      have charged := keeperBound (dir.file (.walSegment first)) count metadata.byteSize.toNat before
      cases payload : readKeeper (dir.file (.walSegment first)) count metadata.byteSize.toNat before with
      | error cause after =>
        simpa [readCachedWalPayloadsFrom, Bind.bind, EStateM.bind, count, payload, reached] using charged
      | ok bytes after =>
        by_cases exactSize : bytes.size = (through - first) * frameSize ∧ (through - first) * frameSize ≤ metadata.byteSize.toNat <;>
          simpa [readCachedWalPayloadsFrom, Bind.bind, EStateM.bind, count, payload, exactSize, Pure.pure, EStateM.pure,
            throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached] using charged
    | cons next rest =>
      obtain ⟨next, nextMetadata⟩ := next
      by_cases forward : first < next
      · have ends : next ≤ through := within _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have total : ((next - first) * frameSize + (through - next) * frameSize) =
            (through - first) * frameSize := by
          rw [← Nat.add_mul]
          congr 1
          omega
        have later := fun extent member => within extent (List.mem_cons_of_mem _ member)
        simp only [readCachedWalPayloadsFrom, forward, ite_true, List.head?_cons, Option.map_some, Option.getD_some]
        rw [← total]
        apply bind_bound
          (readExactRecoveryFileWith_payloadCallsBound (dir.file (.walSegment first)) ((next - first) * frameSize)
            selectedWalSpanError (fun _ => .ok metadata.byteSize.toNat) readSeal (sealBound _ _) before)
        intro payload after _
        exact ih later ((first, payload) :: read) after
      · simp [readCachedWalPayloadsFrom, forward, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw,
          EStateM.throw, reached]

open RecoveryRequestCount in
/-- Count primitive prefix requests over the actual selected seal and
keeper loop, including any reached failure. Adjacent seal extents and
the marker-bounded keeper telescope to the selected byte interval. -/
theorem readCachedWalPayloads_payloadCallsBound (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error Nat ByteArray)
    (sealBound : ∀ path count before, reached (readSeal path count before) ≤ before + count)
    (keeperBound : ∀ path count size before, reached (readKeeper path count size before) ≤ before + count)
    (required : List (Nat × IO.FS.Metadata)) (within : ∀ extent ∈ required, extent.1 ≤ through)
    (before : Nat) :
    reached (readCachedWalPayloads dir through readSeal readKeeper required before) ≤
      before + (through - (required.head?.map Prod.fst).getD through) * frameSize :=
  readCachedWalPayloadsFrom_payloadCallsBound dir through readSeal readKeeper sealBound keeperBound required within [] before

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

open RecoveryRequestCount renaming issued → counted, reached → callsAfter

private theorem countedExtent (dir : DiskDirectory) (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (name : String) (before : Nat) :
    let observed := readWalSegmentExtentWith dir (fun path => counted (lstat path)) name before
    let budget := ([name].filterMap parseWalSegmentName).length
    callsAfter observed ≤ before + budget ∧
      ∀ extent reached, observed = .ok (some extent) reached → 1 ≤ budget := by
  dsimp only
  cases parsed : parseWalSegmentName name with
  | none =>
    simp [readWalSegmentExtentWith, parsed, Pure.pure, EStateM.pure, callsAfter]
  | some first =>
    cases measured : lstat (dir.file (.walSegment first)) with
    | error cause =>
      simp [readWalSegmentExtentWith, parsed, counted, measured, Bind.bind, EStateM.bind, callsAfter]
    | ok report =>
      cases classified : classifyWalSegmentLookup (dir.file (.walSegment first)) first report with
      | error =>
        simp [readWalSegmentExtentWith, parsed, counted, measured, classified, Bind.bind, EStateM.bind,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter]
      | ok found =>
        cases found <;> simp [readWalSegmentExtentWith, parsed, counted, measured, classified, Bind.bind, EStateM.bind,
          Pure.pure, EStateM.pure, callsAfter]

private theorem countedExtentFilter (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) (before : Nat) :
    let observed := (names.filterMapM (readWalSegmentExtentWith dir (fun path => counted (lstat path)))) before
    let budget := (names.filterMap parseWalSegmentName).length
    callsAfter observed ≤ before + budget ∧
      ∀ extents reached, observed = .ok extents reached → extents.length ≤ budget := by
  induction names generalizing before with
  | nil => simp [List.filterMapM_nil, Pure.pure, EStateM.pure, callsAfter]
  | cons name names ih =>
    dsimp only
    let step := readWalSegmentExtentWith dir (fun path => counted (lstat path))
    have budgets : ((name :: names).filterMap parseWalSegmentName).length =
        ([name].filterMap parseWalSegmentName).length + (names.filterMap parseWalSegmentName).length := by
      rw [show name :: names = [name] ++ names from rfl, List.filterMap_append, List.length_append]
    have stepBudget := countedExtent dir lstat name before
    rw [budgets]
    simp only [List.filterMapM_cons, Bind.bind, EStateM.bind, ← show
      step = readWalSegmentExtentWith dir (fun path => counted (lstat path)) from rfl]
    cases head : step name before with
    | error cause reached =>
      have spent : reached ≤ before + ([name].filterMap parseWalSegmentName).length :=
        by simpa [step, head, callsAfter] using stepBudget.1
      simp only [callsAfter]
      exact ⟨by omega, by simp⟩
    | ok found reached =>
      have spent : reached ≤ before + ([name].filterMap parseWalSegmentName).length :=
        by simpa [step, head, callsAfter] using stepBudget.1
      have rest := ih reached
      change callsAfter _ ≤ _ ∧ _
      cases found with
      | none =>
        exact ⟨Nat.le_trans rest.1 (by omega), fun _ _ observed =>
          Nat.le_trans (rest.2 _ _ observed) (Nat.le_add_left _ _)⟩
      | some found =>
        have requested : 1 ≤ ([name].filterMap parseWalSegmentName).length :=
          stepBudget.2 found reached head
        cases tail : (names.filterMapM step) reached with
        | error cause final =>
          have total : final ≤ reached + (names.filterMap parseWalSegmentName).length := by
            simpa [step, tail, callsAfter] using rest.1
          simp only [EStateM.bind, tail, callsAfter]
          exact ⟨by omega, by simp⟩
        | ok extents final =>
          have total : final ≤ reached + (names.filterMap parseWalSegmentName).length := by
            simpa [step, tail, callsAfter] using rest.1
          have retained := rest.2 extents final tail
          simp only [EStateM.bind, tail, Pure.pure, EStateM.pure, callsAfter, EStateM.Result.ok.injEq]
          exact ⟨by omega, by rintro _ _ ⟨rfl, rfl⟩; simp; omega⟩

private theorem countedExtentScan (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) (before : Nat) :
    let observed := readWalSegmentExtentsWith dir (fun path => counted (lstat path)) names before
    let budget := (names.filterMap parseWalSegmentName).length
    callsAfter observed ≤ before + budget ∧
      ∀ extents reached, observed = .ok extents reached → extents.length ≤ budget := by
  dsimp only
  unfold readWalSegmentExtentsWith
  simp only [Bind.bind, EStateM.bind]
  have count := countedExtentFilter dir lstat names before
  cases result : (names.filterMapM (readWalSegmentExtentWith dir (fun path => counted (lstat path)))) before with
  | error cause reached =>
    rw [result] at count
    exact ⟨count.1, by simp⟩
  | ok extents reached =>
    have length := count.2 extents reached result
    rw [result] at count
    refine ⟨count.1, ?_⟩
    intro result _ exactResult
    simp only [Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at exactResult
    rw [← exactResult.1, List.length_mergeSort]
    exact length

private theorem countedCachedWalPayloads (dir : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray)
    (required : List (Nat × IO.FS.Metadata)) (read : List (Nat × ByteArray)) (before : Nat) :
    callsAfter (readCachedWalPayloadsFrom dir through (fun path count => counted (readSeal path count))
      (fun path count size => counted (readKeeper path count size)) required read before) ≤ before + required.length := by
  induction required generalizing read before with
  | nil =>
    simp [readCachedWalPayloadsFrom, throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter]
  | cons item rest ih =>
    obtain ⟨first, metadata⟩ := item
    cases rest with
    | nil =>
      cases h : readKeeper (dir.file (.walSegment first)) ((through - first) * frameSize) metadata.byteSize.toNat with
      | error =>
        simp [readCachedWalPayloadsFrom, h, counted, Bind.bind, EStateM.bind, Pure.pure, callsAfter]
      | ok bytes =>
        by_cases size : bytes.size = (through - first) * frameSize ∧ (through - first) * frameSize ≤ metadata.byteSize.toNat <;>
          simp [readCachedWalPayloadsFrom, h, size, counted, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter]
    | cons item rest =>
      obtain ⟨next, nextMetadata⟩ := item
      by_cases forward : first < next
      · by_cases extent : metadata.byteSize.toNat = (next - first) * frameSize ∧ (next - first) * frameSize < USize.size
        · cases observed : readSeal (dir.file (.walSegment first)) ((next - first) * frameSize) with
          | error =>
            simp [readCachedWalPayloadsFrom, forward, readExactRecoveryFileWith, extent, observed, counted,
              Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, callsAfter]
          | ok bytes =>
            by_cases size : bytes.size = (next - first) * frameSize
            · simpa [readCachedWalPayloadsFrom, forward, readExactRecoveryFileWith, extent, observed, counted, size,
                Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using ih ((first, bytes) :: read) (before + 1)
            · simp [readCachedWalPayloadsFrom, forward, readExactRecoveryFileWith, extent, observed, counted, size,
                Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
                callsAfter]
        · simp [readCachedWalPayloadsFrom, forward, readExactRecoveryFileWith, extent, Bind.bind, EStateM.bind,
            Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter]
      · simp [readCachedWalPayloadsFrom, forward, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw,
          EStateM.throw, callsAfter]

/-- Count the cached WAL reader's directory, metadata, and payload requests.
Each request is counted when issued, including those that return an error. -/
noncomputable def countCachedWalReadCalls (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray) : Nat :=
  callsAfter (readSelectedWithCachedExtents dir watermark length
    (fun path => counted (list path)) (fun path => counted (lstat path))
    (fun path count => counted (readSeal path count))
    (fun path count size => counted (readKeeper path count size)) 0)

/-- The number of canonical WAL filenames in a successful listing. -/
noncomputable def listedWalNames : Except IO.Error (Array IO.FS.DirEntry) → Nat
  | .ok entries => ((entries.toList.map (·.fileName)).filterMap parseWalSegmentName).length
  | .error _ => 0

/-- A successful selection leaves one possible unlink for each later name. -/
noncomputable def pendingWalUnlinks : EStateM.Result IO.Error Nat (WalSegmentMarkerReads × Nat) → Nat
  | .ok (reads, _) _ => reads.newer.length
  | .error _ _ => 0

/-- The cached reader budgets one listing, one probe per canonical name,
and either a payload read or a later repair unlink per selected name. -/
theorem readSelectedWithCachedExtents_requestBound (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray) (before : Nat) :
    let observed := readSelectedWithCachedExtents dir watermark length
      (fun path => counted (list path)) (fun path => counted (lstat path))
      (fun path count => counted (readSeal path count))
      (fun path count size => counted (readKeeper path count size)) before
    callsAfter observed + pendingWalUnlinks observed ≤ before + (1 + 2 * listedWalNames (list dir.path)) := by
  dsimp only
  unfold readSelectedWithCachedExtents
  by_cases valid : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize
  · cases listed : list dir.path with
    | error cause =>
      simp [valid, listed, counted, Bind.bind, EStateM.bind, callsAfter, pendingWalUnlinks, listedWalNames]
    | ok entries =>
      let names := entries.toList.map IO.FS.DirEntry.fileName
      let scan := readWalSegmentExtentsWith dir (fun path => counted (lstat path)) names
      have measured := countedExtentScan dir lstat names (before + 1)
      simp only [ite_eq_left valid, Bind.bind, EStateM.bind, Pure.pure, counted, listed]
      rw [show readWalSegmentExtentsWith dir (fun path => counted (lstat path)) names (before + 1) =
        scan (before + 1) from rfl]
      change _ ≤ before + (1 + 2 * (names.filterMap parseWalSegmentName).length)
      cases scanned : scan (before + 1) with
      | error cause reached =>
        have spent : reached ≤ before + 1 + (names.filterMap parseWalSegmentName).length := by
          simpa [scan, scanned, callsAfter] using measured.1
        simp only [callsAfter, pendingWalUnlinks]
        omega
      | ok extents reached =>
        have spent : reached ≤ before + 1 + (names.filterMap parseWalSegmentName).length := by
          simpa [scan, scanned, callsAfter] using measured.1
        have size := measured.2 extents reached scanned
        cases selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) with
        | none =>
          simp only [selected, throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter, pendingWalUnlinks]
          omega
        | some selection =>
          obtain ⟨required, newer⟩ := selection
          have selectedCount : required.length + newer.length ≤ extents.length := by
            unfold selectWalExtentsThrough at selected
            cases found : ((extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max? with
            | none => simp [found, Bind.bind, Option.bind] at selected
            | some first =>
              simp only [found, Bind.bind, Option.bind, Pure.pure, Option.some.injEq, Prod.mk.injEq] at selected
              rw [← selected.1, ← selected.2, List.length_map, ← List.length_append, List.takeWhile_append_dropWhile]
              exact List.filter_sublist.length_le
          have payloads := countedCachedWalPayloads dir (length.toNat / frameSize) readSeal readKeeper required [] reached
          simp only [selected, readCachedWalPayloads, EStateM.bind]
          cases payload : readCachedWalPayloadsFrom dir (length.toNat / frameSize)
              (fun path count => counted (readSeal path count))
              (fun path count size => counted (readKeeper path count size)) required [] reached <;>
            rw [payload] at payloads <;> simp only [EStateM.pure, callsAfter, pendingWalUnlinks] at payloads ⊢ <;> omega
  · simp [valid, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, callsAfter, pendingWalUnlinks]

/-- The cached WAL reader issues at most one directory listing, one metadata probe
per canonical name, and one payload request per selected segment. Both the successful
result and error exits satisfy this combined bound on requests to the filesystem adapter. -/
theorem countCachedWalReadCalls_bound (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray) :
    countCachedWalReadCalls dir watermark length list lstat readSeal readKeeper ≤ 1 + 2 * listedWalNames (list dir.path) := by
  have bounded := readSelectedWithCachedExtents_requestBound dir watermark length list lstat readSeal readKeeper 0
  dsimp only at bounded
  unfold countCachedWalReadCalls
  omega

end Alvoki.Storage.WalSegmentRepair
