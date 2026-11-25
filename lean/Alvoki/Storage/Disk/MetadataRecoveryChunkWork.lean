import Alvoki.Storage.Disk.HeldMetadataReadObservations
import Alvoki.Storage.Disk.SelectedRecoveryChunkWork

namespace Alvoki.Storage

open Manifest RecoveryRequestCount

theorem countPrefixUntilEof_projects (mismatch : IO.Error) (read : USize → EStateM IO.Error Nat ByteArray)
    (remaining : Nat) (bytes : ByteArray) (offset calls : Nat) :
    forgetRecoveryChunkCount (readPrefixUntilEofWith mismatch (countRecoveryChunk read) remaining bytes (offset, calls)) =
      readPrefixUntilEofWith mismatch read remaining bytes offset := by
  rw [readPrefixUntilEofWith, readPrefixUntilEofWith]
  by_cases done : remaining = 0
  · simp [done, Pure.pure, EStateM.pure, forgetRecoveryChunkCount]
  · simp only [ite_eq_right done, Bind.bind, EStateM.bind]
    cases result : read remaining.toUSize offset with
    | error error next => simp [countRecoveryChunk, result, forgetRecoveryChunkCount]
    | ok chunk next =>
      simp only [countRecoveryChunk, result]
      by_cases empty : chunk.size = 0
      · simp [empty, Pure.pure, EStateM.pure, forgetRecoveryChunkCount]
      · simp only [empty, ↓reduceIte]
        by_cases valid : chunk.size ≤ remaining
        · rw [dite_eq_left valid, dite_eq_left valid]
          exact countPrefixUntilEof_projects mismatch read (remaining - chunk.size) _ next (calls + 1)
        · rw [dite_eq_right valid, dite_eq_right valid]
          rfl
termination_by remaining
decreasing_by omega

/-- Counting the two manifest passes preserves every returned result and
the exact reached cursor, including the first error's cursor. -/
theorem countIntegrityManifestPrefix_projects (read : USize → EStateM IO.Error Nat ByteArray)
    (extent offset calls : Nat) :
    forgetRecoveryChunkCount (readIntegrityManifestPrefixWith (countRecoveryChunk read) extent (offset, calls)) =
      readIntegrityManifestPrefixWith read extent offset := by
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  let counted := readExactPrefixWith mismatch (countRecoveryChunk read) (min 48 extent) .empty
  let raw := readExactPrefixWith mismatch read (min 48 extent) .empty
  have first := countExactPrefix_projects mismatch read (min 48 extent) .empty offset calls
  change forgetRecoveryChunkCount (counted (offset, calls)) = raw offset at first
  unfold readIntegrityManifestPrefixWith
  change forgetRecoveryChunkCount ((counted >>= _) (offset, calls)) = (raw >>= _) offset
  simp only [Bind.bind, EStateM.bind]
  cases outcome : counted (offset, calls) with
  | error cause after =>
    obtain ⟨cursor, count⟩ := after
    rw [outcome] at first
    rw [← first]
    rfl
  | ok header after =>
    obtain ⟨cursor, count⟩ := after
    rw [outcome] at first
    rw [← first]
    by_cases short : header.size < 48
    · simp [short, Pure.pure, EStateM.pure, forgetRecoveryChunkCount]
    · by_cases fits : 48 + min (extent - 48) (IntegrityCheckpoint.declaredStampBytes header + 1) < USize.size
      · simpa only [forgetRecoveryChunkCount, short, fits, ↓reduceIte] using
          countExactPrefix_projects mismatch read _ header cursor count
      · simp [short, fits, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, forgetRecoveryChunkCount]

/-- The header and tail share one checked extent. Charge the first
rejected read as well as the reads that return a chunk. -/
theorem readIntegrityManifestPrefixWith_requestBoundBy {state : Type}
    (read : USize → EStateM IO.Error state ByteArray) (count : state → Nat)
    (charged : ∀ size before, recoveryCalls count (read size before) = count before + 1)
    (extent : Nat) (before : state) :
    recoveryCalls count (readIntegrityManifestPrefixWith read extent before) ≤ count before + extent := by
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  have first := readExactPrefixWith_requestBoundBy mismatch read count charged (min 48 extent) .empty before
  unfold readIntegrityManifestPrefixWith
  change recoveryCalls count ((readExactPrefixWith mismatch read (min 48 extent) .empty >>= _) before) ≤ _
  simp only [Bind.bind, EStateM.bind]
  cases outcome : readExactPrefixWith mismatch read (min 48 extent) .empty before with
  | error cause after =>
    rw [outcome] at first
    exact Nat.le_trans first (Nat.add_le_add_left (Nat.min_le_right ..) _)
  | ok header after =>
    rw [outcome] at first
    simp only [recoveryCalls] at first
    by_cases short : header.size < 48
    · simpa only [short, ↓reduceIte, Pure.pure, EStateM.pure, recoveryCalls] using
        Nat.le_trans first (Nat.add_le_add_left (Nat.min_le_right 48 extent) (count before))
    · simp only [short, ↓reduceIte]
      let rest := min (extent - 48) (IntegrityCheckpoint.declaredStampBytes header + 1)
      change recoveryCalls count ((if 48 + rest < USize.size then
        readExactPrefixWith mismatch read rest header else
        throw (IO.userError "integrity manifest prefix exceeds machine size")) after) ≤ _
      split
      · have later := readExactPrefixWith_requestBoundBy mismatch read count charged rest header after
        have atMost : rest ≤ extent - 48 := Nat.min_le_left ..
        exact Nat.le_trans later (by omega)
      · simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw, recoveryCalls]
        exact Nat.le_trans first (Nat.add_le_add_left (Nat.min_le_right ..) _)

end Alvoki.Storage

namespace Alvoki.Storage.WalSegmentRepair

open System RecoveryRequestCount DiskSession

/-- Interpret the same optional metadata reader and its same opened
description, keeping the reported cursor plus a primitive chunk count. -/
def CheckpointRunChunkReads.countMetadata (reads : CheckpointRunChunkReads)
    (directory : DiskDirectory) (path : FilePath) : EStateM IO.Error (Nat × Nat) (Option ByteArray) :=
  readOptionalCachedOpenFileWith directory path (pure ((reads.stat path).map Prod.fst))
    (fun path (cursor, calls) => match reads.openRead path with
      | .error cause => .error cause (cursor, calls)
      | .ok (_, slot, offset) => .ok slot (offset, calls))
    (fun slot => countRecoveryChunk (reads.readChunk slot.description))

private def someMetadataResult {state : Type} (result : EStateM.Result IO.Error state ByteArray) :
    EStateM.Result IO.Error state (Option ByteArray) :=
  match result with
  | .ok bytes reached => .ok (some bytes) reached
  | .error cause reached => .error cause reached

private theorem someMetadataResult_projects {counted : EStateM.Result IO.Error (Nat × Nat) ByteArray}
    {raw : EStateM.Result IO.Error Nat ByteArray} (same : forgetRecoveryChunkCount counted = raw) :
    forgetRecoveryChunkCount (someMetadataResult counted) = someMetadataResult raw := by
  rw [← same]
  cases counted <;> rfl

/-- The counted optional metadata read gives the exact cursor-bearing
native report when the extra counter is erased. -/
theorem CheckpointRunChunkReads.countMetadata_projects (reads : CheckpointRunChunkReads)
    (directory : DiskDirectory) (path : FilePath) (offset calls : Nat) :
    forgetRecoveryChunkCount (reads.countMetadata directory path (offset, calls)) =
      runCachedMetadataRead reads directory path offset := by
  unfold CheckpointRunChunkReads.countMetadata runCachedMetadataRead
  simp only [readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  cases reads.stat path with
  | error cause =>
    cases cause <;> simp [Except.map, forgetRecoveryChunkCount, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]
    case noFileOrDirectory filename osCode details =>
      by_cases missing : osCode = 2 <;> simp [missing, EStateM.pure, EStateM.throw]
  | ok found =>
    obtain ⟨metadata, object⟩ := found
    simp only [Except.map]
    by_cases regular : (metadata.type == .file) = true
    · simp only [regular, ↓reduceIte]
      cases reads.openRead path with
      | error cause => rfl
      | ok found =>
        obtain ⟨inventory, slot, start⟩ := found
        simp only [EStateM.bind, EStateM.pure]
        by_cases marker : (path == directory.file .walBoundary) = true
        · simp only [marker, ↓reduceIte]
          have same := countPrefixUntilEof_projects (IO.userError "invalid WAL boundary length")
            (reads.readChunk slot.description) WAL.Boundary.acquisitionLimit ByteArray.empty start calls
          generalize readPrefixUntilEofWith (IO.userError "invalid WAL boundary length")
            (countRecoveryChunk (reads.readChunk slot.description)) WAL.Boundary.acquisitionLimit ByteArray.empty
            (start, calls) = found at same ⊢
          generalize readPrefixUntilEofWith (IO.userError "invalid WAL boundary length")
            (reads.readChunk slot.description) WAL.Boundary.acquisitionLimit ByteArray.empty start = projected at same ⊢
          have mapped := someMetadataResult_projects same
          cases found <;> cases projected <;> exact mapped
        · simp only [marker, Bool.false_eq_true, ↓reduceIte]
          have same := countIntegrityManifestPrefix_projects (reads.readChunk slot.description) metadata.byteSize.toNat
            start calls
          generalize readIntegrityManifestPrefixWith (countRecoveryChunk (reads.readChunk slot.description))
            metadata.byteSize.toNat (start, calls) = found at same ⊢
          generalize readIntegrityManifestPrefixWith (reads.readChunk slot.description) metadata.byteSize.toNat start =
            projected at same ⊢
          have mapped := someMetadataResult_projects same
          cases found <;> cases projected <;> exact mapped
    · simp [regular, throw, throwThe, MonadExceptOf.throw, EStateM.throw, forgetRecoveryChunkCount]

/-- Charge only chunk reads, after the no-follow guard and read-open.
A missing or rejected file performs no chunk read. The manifest has a
checked physical extent and the marker uses its independent cap. -/
theorem CheckpointRunChunkReads.countMetadata_le (reads : CheckpointRunChunkReads)
    (directory : DiskDirectory) (path : FilePath) (before : Nat × Nat) :
    recoveryCalls Prod.snd (reads.countMetadata directory path before) ≤ before.2 +
      (if path == directory.file .walBoundary then WAL.Boundary.acquisitionLimit else
        ((reads.stat path).toOption.map (fun (metadata, _) => metadata.byteSize.toNat)).getD 0) := by
  unfold CheckpointRunChunkReads.countMetadata
  simp only [readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  cases reads.stat path with
  | error cause =>
    cases cause <;> simp [Except.map, Except.toOption, recoveryCalls, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]
    case noFileOrDirectory filename osCode details =>
      by_cases missing : osCode = 2 <;> simp [missing, EStateM.pure, EStateM.throw]
  | ok found =>
    obtain ⟨metadata, object⟩ := found
    simp only [Except.map, Except.toOption, Option.map_some, Option.getD_some]
    by_cases regular : (metadata.type == .file) = true
    · simp only [regular, ↓reduceIte]
      cases reads.openRead path with
      | error cause => simp [EStateM.bind, recoveryCalls]
      | ok found =>
        obtain ⟨inventory, slot, offset⟩ := found
        simp only [EStateM.bind, EStateM.pure]
        let chunk := countRecoveryChunk (reads.readChunk slot.description)
        have charged (size : USize) (state : Nat × Nat) : recoveryCalls Prod.snd (chunk size state) = state.2 + 1 := by
          rcases state with ⟨cursor, calls⟩
          cases returned : reads.readChunk slot.description size cursor <;> simp [chunk, countRecoveryChunk, returned, recoveryCalls]
        by_cases marker : (path == directory.file .walBoundary) = true
        · simp [marker]
          let read := readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") chunk
            WAL.Boundary.acquisitionLimit ByteArray.empty
          have bounded := readPrefixUntilEofWith_requestBoundBy (IO.userError "invalid WAL boundary length")
            chunk Prod.snd charged WAL.Boundary.acquisitionLimit ByteArray.empty (offset, before.2)
          cases outcome : read (offset, before.2) <;> simpa only [read, chunk, outcome, recoveryCalls] using bounded
        · simp [marker]
          let read := readIntegrityManifestPrefixWith chunk metadata.byteSize.toNat
          have bounded := readIntegrityManifestPrefixWith_requestBoundBy chunk Prod.snd charged
            metadata.byteSize.toNat (offset, before.2)
          cases outcome : read (offset, before.2) <;> simpa only [read, chunk, outcome, recoveryCalls] using bounded
    · simp [regular, recoveryCalls, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.WalSegmentRepair
