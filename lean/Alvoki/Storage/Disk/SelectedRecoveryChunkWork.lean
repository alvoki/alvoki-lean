import Alvoki.Storage.Disk.CachedWalChunkReports
import Alvoki.Storage.Disk.WalSegmentCachedOpenWork

namespace Alvoki.Storage

/-- Count one reached chunk read while preserving its cursor and report. -/
def countRecoveryChunk (read : USize → EStateM IO.Error Nat ByteArray) (size : USize) :
    EStateM IO.Error (Nat × Nat) ByteArray := fun (offset, calls) =>
  match read size offset with
  | .ok bytes next => .ok bytes (next, calls + 1)
  | .error cause next => .error cause (next, calls + 1)

/-- Forget the proof-only counter while preserving the file cursor. -/
def forgetRecoveryChunkCount {α : Type} : EStateM.Result IO.Error (Nat × Nat) α → EStateM.Result IO.Error Nat α
  | .ok result (offset, _) => .ok result offset
  | .error error (offset, _) => .error error offset

theorem countExactPrefix_projects (mismatch : IO.Error) (read : USize → EStateM IO.Error Nat ByteArray)
    (remaining : Nat) (bytes : ByteArray) (offset calls : Nat) :
    forgetRecoveryChunkCount (readExactPrefixWith mismatch (countRecoveryChunk read) remaining bytes (offset, calls)) =
      readExactPrefixWith mismatch read remaining bytes offset := by
  by_cases done : remaining = 0
  · subst remaining
    rw [readExactPrefixWith, readExactPrefixWith]
    rfl
  · rw [readExactPrefixWith, readExactPrefixWith]
    simp only [ite_eq_right done, Bind.bind, EStateM.bind]
    cases result : read remaining.toUSize offset with
    | error error next => simp [countRecoveryChunk, result, forgetRecoveryChunkCount]
    | ok chunk next =>
      simp only [countRecoveryChunk, result]
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · rw [dite_eq_left valid, dite_eq_left valid]
        exact countExactPrefix_projects mismatch read (remaining - chunk.size) _ next (calls + 1)
      · rw [dite_eq_right valid, dite_eq_right valid]
        rfl
termination_by remaining
decreasing_by omega

end Alvoki.Storage

namespace Alvoki.Storage.WalSegmentRepair

open System RecoveryRequestCount SyncHandleRouting Manifest
open WAL (frameSize)

/-- Interpret the native prefix loop with the reported file cursor and
a separate counter. A failed read advances the counter as well. -/
noncomputable def CheckpointRunChunkReads.countPrefix (reads : CheckpointRunChunkReads)
    (mismatch : IO.Error) (path : FilePath) (count : Nat) : EStateM IO.Error Nat ByteArray := fun calls =>
  match reads.openRead path with
  | .error cause => .error cause calls
  | .ok (_, slot, offset) =>
    match readExactPrefixWith mismatch (countRecoveryChunk (reads.readChunk slot.description)) count ByteArray.empty (offset, calls) with
    | .ok result (_, reached) => .ok result reached
    | .error cause (_, reached) => .error cause reached

/-- Counting leaves the exact adapter report intact, including errors.
Open and metadata are outside the primitive chunk counter. -/
theorem CheckpointRunChunkReads.countPrefix_projects (reads : CheckpointRunChunkReads)
    (mismatch : IO.Error) (path : FilePath) (count calls : Nat) :
    (match reads.countPrefix mismatch path count calls with
      | .ok bytes _ => Except.ok bytes
      | .error cause _ => Except.error cause) = reads.readFilePrefix mismatch path count := by
  cases opened : reads.openRead path with
  | error cause => simp [CheckpointRunChunkReads.countPrefix, CheckpointRunChunkReads.readFilePrefix, opened, Bind.bind, Except.bind]
  | ok openedFile =>
    obtain ⟨inventory, slot, offset⟩ := openedFile
    have projects := countExactPrefix_projects mismatch (reads.readChunk slot.description) count ByteArray.empty offset calls
    rw [CheckpointRunChunkReads.countPrefix, CheckpointRunChunkReads.readFilePrefix, opened]
    change _ = reads.readOpenedPrefix mismatch (inventory, slot, offset) count
    change _ = (match readExactPrefixWith (m := EStateM IO.Error Nat) mismatch (reads.readChunk slot.description)
      count ByteArray.empty offset with
      | .ok bytes _ => Except.ok bytes
      | .error cause _ => Except.error cause)
    rw [← projects]
    cases outcome : readExactPrefixWith mismatch (countRecoveryChunk (reads.readChunk slot.description)) count ByteArray.empty
      (offset, calls) with
    | ok result state => cases state; simp [outcome, forgetRecoveryChunkCount]
    | error cause state => cases state; simp [outcome, forgetRecoveryChunkCount]

theorem CheckpointRunChunkReads.countPrefix_le (reads : CheckpointRunChunkReads)
    (mismatch : IO.Error) (path : FilePath) (count calls : Nat) :
    reached (reads.countPrefix mismatch path count calls) ≤ calls + count := by
  unfold CheckpointRunChunkReads.countPrefix
  cases reads.openRead path with
  | error cause => simp [reached]
  | ok openedFile =>
    obtain ⟨_, slot, offset⟩ := openedFile
    let read := countRecoveryChunk (reads.readChunk slot.description)
    have charged (size : USize) (state : Nat × Nat) : recoveryCalls Prod.snd (read size state) = state.2 + 1 := by
      cases state with
      | mk offset calls =>
        cases reported : reads.readChunk slot.description size offset <;>
          simp [read, countRecoveryChunk, reported, recoveryCalls]
    have bound := readExactPrefixWith_requestBoundBy mismatch read Prod.snd charged count ByteArray.empty (offset, calls)
    change reached (match readExactPrefixWith mismatch read count ByteArray.empty (offset, calls) with
      | .ok result (_, reached) => .ok result reached
      | .error cause (_, reached) => .error cause reached) ≤ _
    generalize readExactPrefixWith mismatch read count ByteArray.empty (offset, calls) = result at bound ⊢
    cases result with
    | ok bytes state => cases state; exact bound
    | error cause state => cases state; exact bound

/-- The production keeper guard runs before the prefix reader. Remembering
a handle does not issue a primitive chunk request. -/
noncomputable def CheckpointRunChunkReads.countKeeper (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize : Nat) : EStateM IO.Error Nat ByteArray :=
  readKeeperWith pure (reads.countPrefix (IO.userError "short or oversized WAL keeper read"))
    (fun _ _ => pure ()) path count fileSize

theorem CheckpointRunChunkReads.countKeeper_le (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize calls : Nat) :
    reached (reads.countKeeper path count fileSize calls) ≤ calls + count := by
  unfold CheckpointRunChunkReads.countKeeper
  by_cases admitted : count ≤ fileSize ∧ count < USize.size
  · have counted := reads.countPrefix_le (IO.userError "short or oversized WAL keeper read") path count calls
    cases reported : reads.countPrefix (IO.userError "short or oversized WAL keeper read") path count calls <;>
      cases aligned : count == fileSize <;>
      simpa [readKeeperWith, admitted, aligned, reported, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using counted
  · simp [readKeeperWith, admitted, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      reached]

/-- The counted keeper preserves the exact cache-bearing adapter's
reported success or error after discarding cache state. -/
theorem CheckpointRunChunkReads.countKeeper_projects (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize calls : Nat) :
    (match reads.countKeeper path count fileSize calls with
      | .ok bytes _ => Except.ok bytes
      | .error cause _ => Except.error cause) = readWalKeeperBytes reads path count fileSize := by
  by_cases admitted : count ≤ fileSize ∧ count < USize.size
  · let mismatch := IO.userError "short or oversized WAL keeper read"
    have projected := reads.countPrefix_projects mismatch path count calls
    have raw : readWalKeeperBytes reads path count fileSize = reads.readFilePrefix mismatch path count := by
      unfold readWalKeeperBytes readWalKeeperWithChunks CheckpointRunChunkReads.readFilePrefix
      cases opened : reads.openRead path with
      | error cause =>
        simp [readKeeperWith, admitted, opened, withCache, Bind.bind, EStateM.bind, Except.bind, liftExcept,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      | ok handle =>
        cases read : reads.readOpenedPrefix mismatch handle count <;>
          cases aligned : count == fileSize <;>
          simp [readKeeperWith, admitted, opened, aligned, mismatch, read, withCache, Bind.bind, EStateM.bind,
            Except.bind, liftExcept, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    rw [raw, ← projected]
    unfold CheckpointRunChunkReads.countKeeper
    cases counted : reads.countPrefix mismatch path count calls <;> cases aligned : count == fileSize <;>
      simp [readKeeperWith, admitted, aligned, mismatch, counted, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  · simp [CheckpointRunChunkReads.countKeeper, readWalKeeperBytes, readWalKeeperWithChunks, readKeeperWith,
      admitted, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem stampPayloadBytes (manifest : IntegrityCheckpoint) (files : List ByteArray)
    (valid : manifest.validateRuns files = true) :
    (manifest.runs.map (·.byteCount.toNat)).sum = (files.map ByteArray.size).sum := by
  obtain ⟨_, length, validSizes⟩ := (manifest.validateRuns_iff files).mp valid
  congr 1
  apply List.ext_getElem
  · simpa only [List.length_map] using length
  · intro index stampIndex runIndex
    have stampIn : index < manifest.runs.length := by simpa only [List.length_map] using stampIndex
    have runIn : index < files.length := by simpa only [List.length_map] using runIndex
    rw [List.getElem_map, List.getElem_map]
    exact (validSizes index manifest.runs[index] files[index]
      (List.getElem?_eq_getElem stampIn) (List.getElem?_eq_getElem runIn)).1.symm

private theorem checkpointPayloadCalls (dir : DiskDirectory) {manifestBytes : Option ByteArray}
    {manifest : Option IntegrityCheckpoint} (decoded : manifestBytes.mapM IntegrityCheckpoint.decode = .ok manifest)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (bounded : ∀ path count before, reached (readPrefix path count before) ≤ before + count) (before : Nat) :
    let action := readIntegrityCheckpointSized dir (pure manifestBytes) (fun path => liftExcept (readSize path)) readPrefix
    let bytes := (manifest.map fun m => (m.runs.map (·.byteCount.toNat)).sum).getD 0
    reached (action before) ≤ before + bytes ∧
      ∀ checkpoint after, action before = .ok checkpoint after →
        (checkpoint.getD (.empty, 0)).1.committed.toNat = (manifest.map (·.header.committed.toNat)).getD 0 := by
  cases manifestBytes with
  | none =>
    have absent : none = manifest := by simpa [Option.mapM, Pure.pure, Except.pure] using decoded
    subst manifest
    simp [readIntegrityCheckpointSized, Pure.pure, EStateM.pure, Bind.bind, EStateM.bind, reached, PackedTable.empty]
  | some bytes =>
    cases parsed : IntegrityCheckpoint.decode bytes with
    | error cause => simp [Option.mapM, parsed, Functor.map, Except.map] at decoded
    | ok m =>
      have present : some m = manifest := by simpa [Option.mapM, parsed, Functor.map, Except.map] using decoded
      subst manifest
      let readRuns := readIntegrityRunBytesSized dir m (fun path => liftExcept (readSize path)) readPrefix
      have spent := readIntegrityRunBytesSized_payloadCallsBound dir parsed readSize readPrefix bounded before
      change reached (readRuns before) ≤ _ at spent
      have accepted : (liftExcept ((IntegrityCheckpoint.decode bytes).mapError IO.userError) :
          EStateM IO.Error Nat IntegrityCheckpoint) = pure m := by
        rw [parsed]
        rfl
      simp only [readIntegrityCheckpointSized, pure_bind, accepted, Option.map_some, Option.getD_some]
      change reached ((readRuns >>= _) before) ≤ _ ∧ ∀ checkpoint after, ((readRuns >>= _) before) = .ok checkpoint after → _
      simp only [Bind.bind, EStateM.bind]
      cases read : readRuns before with
      | error cause after =>
        rw [read] at spent
        exact ⟨spent, by simp⟩
      | ok files after =>
        rw [read] at spent
        cases loaded : loadIntegrityRunSet m files with
        | error cause =>
          simp only [loaded, Except.mapError, liftExcept, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
          exact ⟨spent, by simp⟩
        | ok table =>
          obtain ⟨_, _, restored⟩ := loadRunSet_restored (loadIntegrityRunSet_iff.mp loaded).2
          refine ⟨by simpa [loaded, Except.mapError, liftExcept, Pure.pure, EStateM.pure, reached] using spent, ?_⟩
          intro checkpoint final returned
          simp only [loaded, Except.mapError, liftExcept, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
          rw [← returned.1]
          exact congrArg UInt64.toNat (PackedTable.restore_spec restored).2.2.1

private theorem walPayloadCalls (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (stat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error Nat ByteArray)
    (sealBound : ∀ path count before, reached (readSeal path count before) ≤ before + count)
    (keeperBound : ∀ path count size before, reached (readKeeper path count size before) ≤ before + count)
    (accepted : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith directory stat (entries.toList.map (·.fileName)) = .ok extents)
    (selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, newer))
    (before : Nat) :
    let through := length.toNat / frameSize
    let first := (required.head?.map Prod.fst).getD through
    reached (readSelectedWithCachedExtents directory watermark length (fun path => liftExcept (list path))
      (fun path => liftExcept (stat path)) readSeal readKeeper before) ≤ before + (through - first) * frameSize := by
  intro through first
  have within : ∀ extent ∈ required, extent.1 ≤ through := by
    unfold selectWalExtentsThrough at selected
    cases start : ((extents.map Prod.fst).filter (fun offset => decide (offset ≤ watermark))).max? with
    | none => simp [start, Bind.bind, Option.bind] at selected
    | some first =>
      simp only [start, Bind.bind, Option.bind, Pure.pure, Option.some.injEq, Prod.mk.injEq] at selected
      intro extent member
      rw [← selected.1] at member
      exact of_decide_eq_true (List.all_eq_true.mp List.all_takeWhile extent member)
  have bound := readCachedWalPayloads_payloadCallsBound directory through readSeal readKeeper sealBound keeperBound
    required within before
  have exactList : (liftExcept (list directory.path) : EStateM IO.Error Nat _) before = .ok entries before := by
    rw [listed]
    rfl
  have exactScan :
      readWalSegmentExtentsWith (m := EStateM IO.Error Nat) directory (fun path => liftExcept (stat path))
        (entries.toList.map (·.fileName)) before =
        (EStateM.Result.ok extents before : EStateM.Result IO.Error Nat _) := by
    change (readWalSegmentExtentsWith (m := EStateM IO.Error Nat) directory (fun path => liftExcept (stat path))
      (entries.toList.map (·.fileName))) before = _
    rw [readWalSegmentExtentsWith_liftReports, scanned]
    rfl
  simp [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate, accepted, Bind.bind, EStateM.bind,
    exactList, exactScan, selected]
  cases read : readCachedWalPayloads directory through readSeal readKeeper required before with
  | error =>
    simpa [through, first, read, reached] using bound
  | ok value count =>
    cases value
    simpa [through, first, read, Pure.pure, EStateM.pure, reached] using bound

/-- Run the actual marked preparation with a primitive chunk counter.
The checkpoint, seal and keeper callbacks use the shared exact-prefix
reader. Manifest/marker reads and inventory are uncharged here. -/
noncomputable def prepareCachedRecoveryWithChunkCount (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (readSize : FilePath → Except IO.Error Nat)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (stat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (reads : CheckpointRunChunkReads) :
    EStateM IO.Error Nat (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (liftExcept (readOptional (directory.file .manifest)))
      (fun path => liftExcept (readSize path)) (reads.countPrefix (IO.userError checkpointIntegrityMismatch)))
    (fun path => liftExcept (readOptional path))
    (fun watermark length => readSelectedWithCachedExtents directory watermark length
      (fun path => liftExcept (list path)) (fun path => liftExcept (stat path))
      (reads.countPrefix selectedWalSpanError) reads.countKeeper)

/-- A checkpoint payload or validation failure returns its reached counter
and error unchanged before marker or WAL acquisition. Only checkpoint
observations are needed on this path. -/
theorem prepareCachedRecoveryWithChunkCount_checkpointError (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (readSize : FilePath → Except IO.Error Nat)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (stat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (reads : CheckpointRunChunkReads)
    {manifestBytes : Option ByteArray} (visible : readOptional (directory.file .manifest) = .ok manifestBytes)
    {manifest : Option IntegrityCheckpoint} (decoded : manifestBytes.mapM IntegrityCheckpoint.decode = .ok manifest)
    {before count : Nat} {cause : IO.Error}
    (failed : readIntegrityCheckpointSized directory (pure manifestBytes) (fun path => liftExcept (readSize path))
      (reads.countPrefix (IO.userError checkpointIntegrityMismatch)) before = .error cause count) :
    prepareCachedRecoveryWithChunkCount directory readOptional readSize list stat reads before = .error cause count ∧
    count ≤ before + (manifest.map fun m => (m.runs.map (·.byteCount.toNat)).sum).getD 0 := by
  have spent := (checkpointPayloadCalls directory decoded readSize _
    (reads.countPrefix_le (IO.userError checkpointIntegrityMismatch)) before).1
  rw [failed] at spent
  refine ⟨?_, spent⟩
  have actualManifest : (liftExcept (readOptional (directory.file .manifest)) :
      EStateM IO.Error Nat (Option ByteArray)) = pure manifestBytes := by rw [visible]; rfl
  unfold prepareCachedRecoveryWithChunkCount prepareBoundedMarkedFromReaders
  rw [actualManifest]
  simp only [Bind.bind, EStateM.bind, failed]

/-- For the reported manifest, absolute marker and checked selected
inventory, preparation issues at most one run/seal/keeper read request
per byte of the declared run payload and selected WAL interval. This
bound applies to every reached outcome. Validated run payloads give the
same budget by their exact byte sizes. -/
theorem prepareCachedRecoveryWithChunkCount_bound (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (readSize : FilePath → Except IO.Error Nat)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (stat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (reads : CheckpointRunChunkReads)
    {manifestBytes : Option ByteArray} (visible : readOptional (directory.file .manifest) = .ok manifestBytes)
    {manifest : Option IntegrityCheckpoint} (decoded : manifestBytes.mapM IntegrityCheckpoint.decode = .ok manifest)
    {marker : ByteArray} (marked : readOptional (directory.file .walBoundary) = .ok (some marker))
    {length : UInt64} (boundary : WAL.Boundary.decode marker = .ok length)
    (aligned : length.toNat % frameSize = 0)
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith directory stat (entries.toList.map (·.fileName)) = .ok extents)
    (selected : selectWalExtentsThrough extents ((manifest.map (·.header.committed.toNat)).getD 0)
      (length.toNat / frameSize) = some (required, newer))
    (covered : (manifest.map (·.header.committed.toNat)).getD 0 ≤ length.toNat / frameSize)
    (before : Nat) :
    let runBytes := (manifest.map fun m => (m.runs.map (·.byteCount.toNat)).sum).getD 0
    let through := length.toNat / frameSize
    let first := (required.head?.map Prod.fst).getD through
    let outcome := prepareCachedRecoveryWithChunkCount directory readOptional readSize list stat reads before
    reached outcome ≤ before + (runBytes + (through - first) * frameSize) ∧
    ∀ files, (match manifest with | none => files = [] | some m => m.validateRuns files = true) →
      reached outcome ≤ before + ((files.map ByteArray.size).sum + (through - first) * frameSize) := by
  intro runBytes through first outcome
  have checkpoint := checkpointPayloadCalls directory decoded readSize _
    (reads.countPrefix_le (IO.userError checkpointIntegrityMismatch)) before
  dsimp only at checkpoint
  have actualManifest : (liftExcept (readOptional (directory.file .manifest)) :
      EStateM IO.Error Nat (Option ByteArray)) = pure manifestBytes := by
    rw [visible]
    rfl
  have actualMarker : (liftExcept (readOptional (directory.file .walBoundary)) :
      EStateM IO.Error Nat (Option ByteArray)) = pure (some marker) := by
    rw [marked]
    rfl
  have absolute : (liftExcept ((WAL.Boundary.decode marker).mapError IO.userError) : EStateM IO.Error Nat UInt64) =
      pure length := by rw [boundary]; rfl
  have bounded : reached outcome ≤ before + (runBytes + (through - first) * frameSize) := by
    unfold outcome prepareCachedRecoveryWithChunkCount prepareBoundedMarkedFromReaders
    rw [actualManifest]
    apply bind_bound checkpoint.1
    intro restored count completed
    have watermark := checkpoint.2 restored count completed
    simp only [actualMarker, pure_bind, absolute]
    rw [watermark]
    let readWal : EStateM IO.Error Nat (WalSegmentMarkerReads × Nat) :=
      readSelectedWithCachedExtents directory ((manifest.map (·.header.committed.toNat)).getD 0) length
      (fun path => liftExcept (list path)) (fun path => liftExcept (stat path))
      (reads.countPrefix selectedWalSpanError) reads.countKeeper
    have walBound := walPayloadCalls directory _ length list stat
      (reads.countPrefix selectedWalSpanError) reads.countKeeper
      (reads.countPrefix_le selectedWalSpanError) reads.countKeeper_le ⟨aligned, covered⟩ listed scanned selected count
    change reached (readWal count) ≤ _ at walBound
    change reached ((readWal >>= _) count) ≤ _
    simp only [Bind.bind, EStateM.bind]
    cases observed : readWal count with
    | error cause reached =>
      rw [observed] at walBound
      exact walBound
    | ok value reached =>
      rw [observed] at walBound
      obtain ⟨read, size⟩ := value
      cases replayed : recoverMarkedWalSegments (restored.getD (.empty, 0)).1 length read.files with
      | error cause =>
        simpa [replayed, Except.mapError, liftExcept, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          RecoveryRequestCount.reached] using walBound
      | ok replayedValue =>
        obtain ⟨_, table⟩ := replayedValue
        cases last : read.files.getLast? with
        | none =>
          simpa [replayed, last, Except.mapError, liftExcept, Pure.pure, EStateM.pure, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw, RecoveryRequestCount.reached] using walBound
        | some keeper =>
          obtain ⟨first, bytes⟩ := keeper
          simpa [replayed, last, Except.mapError, liftExcept, Pure.pure, EStateM.pure, RecoveryRequestCount.reached]
            using walBound
  refine ⟨bounded, ?_⟩
  intro files valid
  have exactBytes : runBytes = (files.map ByteArray.size).sum := by
    cases manifest with
    | none => simp [runBytes, show files = [] from valid]
    | some manifest => exact stampPayloadBytes manifest files valid
  simpa only [exactBytes] using bounded

end Alvoki.Storage.WalSegmentRepair
