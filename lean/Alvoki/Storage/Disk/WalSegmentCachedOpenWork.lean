import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen
import Alvoki.Storage.Disk.WalSegmentRecoveryWork
import Alvoki.Storage.Disk.ReadRecoveryPrefix

namespace Alvoki.Storage

open RecoveryRequestCount

/-- Read the work counter from either outcome of a recovery action. -/
def recoveryCalls {state payload : Type} (count : state → Nat) : EStateM.Result IO.Error state payload → Nat
  | .ok _ reached | .error _ reached => count reached

/-- Count each reached primitive callback while retaining the rest of the
reader state. Only a nonempty accepted chunk can repeat the callback. -/
theorem readExactPrefixWith_requestBoundBy {state : Type} (mismatch : IO.Error)
    (read : USize → EStateM IO.Error state ByteArray) (count : state → Nat)
    (charged : ∀ size before, recoveryCalls count (read size before) = count before + 1)
    (remaining : Nat) (bytes : ByteArray) (before : state) :
    recoveryCalls count (readExactPrefixWith mismatch read remaining bytes before) ≤ count before + remaining := by
  rw [readExactPrefixWith]
  by_cases finished : remaining = 0
  · simp [finished, Pure.pure, EStateM.pure, recoveryCalls]
  · have one := charged remaining.toUSize before
    rw [ite_eq_right finished]
    simp only [Bind.bind, EStateM.bind]
    cases report : read remaining.toUSize before with
    | error cause after =>
      simp only [report, recoveryCalls] at one
      simp only [recoveryCalls]
      omega
    | ok chunk after =>
      simp only [report, recoveryCalls] at one
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · simp only [valid]
        have rest := readExactPrefixWith_requestBoundBy mismatch read count charged (remaining - chunk.size)
          (if bytes.isEmpty then chunk else bytes ++ chunk) after
        have total : count after + (remaining - chunk.size) ≤ count before + remaining := by omega
        exact Nat.le_trans rest total
      · simp only [valid, ↓reduceDIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw, recoveryCalls]
        omega
termination_by remaining
decreasing_by omega

theorem readExactPrefixWith_requestBound (mismatch : IO.Error)
    (read : USize → EStateM IO.Error Nat ByteArray)
    (charged : ∀ count calls, reached (read count calls) = calls + 1)
    (remaining : Nat) (bytes : ByteArray) (before : Nat) :
    reached (readExactPrefixWith mismatch read remaining bytes before) ≤ before + remaining := by
  have same (result : EStateM.Result IO.Error Nat ByteArray) : recoveryCalls id result = reached result := by
    cases result <;> rfl
  simpa only [same, id] using readExactPrefixWith_requestBoundBy mismatch read id
    (fun size state => (same _).trans (charged size state)) remaining bytes before

/-- Count every reached read in a capped prefix, including the EOF witness
and reads returning an error. Only positive chunks continue the loop. -/
theorem readPrefixUntilEofWith_requestBoundBy {state : Type} (mismatch : IO.Error)
    (read : USize → EStateM IO.Error state ByteArray) (count : state → Nat)
    (charged : ∀ size before, recoveryCalls count (read size before) = count before + 1)
    (remaining : Nat) (bytes : ByteArray) (before : state) :
    recoveryCalls count (readPrefixUntilEofWith mismatch read remaining bytes before) ≤ count before + remaining := by
  rw [readPrefixUntilEofWith]
  by_cases finished : remaining = 0
  · simp [finished, Pure.pure, EStateM.pure, recoveryCalls]
  · have one := charged remaining.toUSize before
    rw [ite_eq_right finished]
    simp only [Bind.bind, EStateM.bind]
    cases report : read remaining.toUSize before with
    | error cause after =>
      simp only [report, recoveryCalls] at one
      simp only [recoveryCalls]
      omega
    | ok chunk after =>
      simp only [report, recoveryCalls] at one
      by_cases empty : chunk.size = 0
      · simp only [empty, ↓reduceIte, Pure.pure, EStateM.pure, recoveryCalls]
        omega
      · by_cases fits : chunk.size ≤ remaining
        · simp only [empty, ↓reduceIte, fits]
          have rest := readPrefixUntilEofWith_requestBoundBy mismatch read count charged (remaining - chunk.size)
            (if bytes.isEmpty then chunk else bytes ++ chunk) after
          exact Nat.le_trans rest (by omega)
        · simp only [empty, ↓reduceIte, fits, ↓reduceDIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw, recoveryCalls]
          omega
termination_by remaining
decreasing_by omega

theorem readPrefixUntilEofWith_requestBound (mismatch : IO.Error)
    (read : USize → EStateM IO.Error Nat ByteArray)
    (charged : ∀ count calls, reached (read count calls) = calls + 1)
    (remaining : Nat) (bytes : ByteArray) (before : Nat) :
    reached (readPrefixUntilEofWith mismatch read remaining bytes before) ≤ before + remaining := by
  have same (result : EStateM.Result IO.Error Nat ByteArray) : recoveryCalls id result = reached result := by
    cases result <;> rfl
  simpa only [same, id] using readPrefixUntilEofWith_requestBoundBy mismatch read id
    (fun size state => (same _).trans (charged size state)) remaining bytes before

end Alvoki.Storage

namespace Alvoki.Storage.WalSegmentRepair

open System RecoveryRequestCount
open WAL (frameSize)

/-- Count requests issued by the marked cached recovery worker under its
acquired lock. The counter retains attempted calls on each error exit. -/
noncomputable def countCachedMarkedOpenRequests (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (readRunSize : FilePath → Except IO.Error Nat) (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit))
    (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit) (renameFile : FilePath → FilePath → Except IO.Error Unit) : Nat :=
  reached (reopenMarkedBoundedWithCachedExtents dir (fun path => issued (readOptional path))
    (fun path => issued (readRunSize path)) (fun path count => issued (readRunPrefix path count))
    (fun path => issued (list path)) (fun path => issued (lstat path))
    (fun path count => issued (readSeal path count)) (fun path count size => issued (readKeeper path count size))
    (fun path => issued (removeFile path)) (fun path bytes => issued (write path bytes))
    (fun paths => issued (sync paths)) (fun source dest => issued (renameFile source dest)) 0)

private theorem replay_finish_bound (dir : DiskDirectory) (base : PackedTable) (generation length : UInt64)
    (wal : EStateM IO.Error Nat (WalSegmentMarkerReads × Nat)) (before walBudget : Nat)
    (walBound : reached (wal before) + pendingWalUnlinks (wal before) ≤ before + walBudget)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit))
    (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit) (renameFile : FilePath → FilePath → Except IO.Error Unit) :
    reached ((do
      let (plan, opened, size) ← (do
        let (reads, size) ← wal
        let (_, table) ← liftExcept ((recoverMarkedWalSegments base length reads.files).mapError IO.userError)
        let some (keeper, keeperBytes) := reads.files.getLast?
          | throw (IO.userError "no WAL segment covers the commit marker")
        pure (⟨length.toNat / frameSize, keeper, reads.newer, keeperBytes⟩,
          ⟨table, generation, length, keeper⟩, size) : EStateM IO.Error Nat (Plan × Reopened × Nat))
      finishBoundedMarkedOpen dir plan size
        (fun path => issued (removeFile path)) (fun path bytes => issued (write path bytes))
        (fun paths => issued (sync paths)) (fun source dest => issued (renameFile source dest))
      pure opened : EStateM IO.Error Nat Reopened) before)
      ≤ before + (walBudget + 6) := by
  cases observed : wal before with
  | error cause count =>
    simp only [observed, reached, pendingWalUnlinks] at walBound
    simp only [Bind.bind, EStateM.bind, observed, reached]
    omega
  | ok value count =>
    obtain ⟨reads, size⟩ := value
    simp only [observed, reached, pendingWalUnlinks] at walBound
    simp only [Bind.bind, EStateM.bind, observed]
    cases replayed : recoverMarkedWalSegments base length reads.files with
    | error cause =>
      simp [Except.mapError, liftExcept, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
      omega
    | ok value =>
      obtain ⟨_, table⟩ := value
      simp only [Except.mapError, liftExcept, Pure.pure, EStateM.pure]
      cases last : reads.files.getLast? with
      | none =>
        simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
        omega
      | some value =>
        obtain ⟨keeper, bytes⟩ := value
        have repaired := finishBoundedMarkedOpen_requestBound dir
          ⟨length.toNat / frameSize, keeper, reads.newer, bytes⟩ size removeFile write sync renameFile count
        simp only [EStateM.pure]
        have bound := Nat.le_trans repaired (show count + (reads.newer.length + 6) ≤ before + (walBudget + 6) by omega)
        cases repair : finishBoundedMarkedOpen dir ⟨length.toNat / frameSize, keeper, reads.newer, bytes⟩ size
            (fun path => issued (removeFile path)) (fun path bytes => issued (write path bytes))
            (fun paths => issued (sync paths)) (fun source dest => issued (renameFile source dest)) count <;>
          simpa only [repair, reached] using bound

/-- Across checkpoint read, WAL selection, and repair, the cached marked
recovery worker issues at most nine fixed requests, two requests for each
decoded run, and two requests for each canonical listed WAL name. Each
selected name contributes at most one payload read or one later unlink.
The bound applies on every returned outcome. Individual requests can read
files of arbitrary size or issue several system calls. -/
theorem countCachedMarkedOpenRequests_bound (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (readRunSize : FilePath → Except IO.Error Nat) (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit))
    (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit) (renameFile : FilePath → FilePath → Except IO.Error Unit) :
    countCachedMarkedOpenRequests dir readOptional readRunSize readRunPrefix list lstat readSeal readKeeper
      removeFile write sync renameFile ≤
    9 + 2 * decodedCheckpointRunCount (readOptional (dir.file .manifest)) + 2 * listedWalNames (list dir.path) := by
  let runBudget := 1 + 2 * decodedCheckpointRunCount (readOptional (dir.file .manifest))
  let walBudget := 1 + 2 * listedWalNames (list dir.path)
  have budgets : runBudget + (1 + (walBudget + 6)) =
      9 + 2 * decodedCheckpointRunCount (readOptional (dir.file .manifest)) + 2 * listedWalNames (list dir.path) := by
    dsimp [runBudget, walBudget]
    omega
  unfold countCachedMarkedOpenRequests reopenMarkedBoundedWithCachedExtents prepareBoundedMarkedFromReaders
  simp only [bind_assoc]
  rw [← budgets, ← Nat.zero_add (runBudget + (1 + (walBudget + 6)))]
  apply bind_bound (readIntegrityCheckpointSized_requestBound dir (readOptional (dir.file .manifest)) readRunSize readRunPrefix 0)
  intro checkpoint after _
  apply bind_bound (by simp only [reached_issued, Nat.le_refl])
  intro marker count _
  cases marker with
  | none => simp [Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
  | some marker =>
    cases decoded : WAL.Boundary.decode marker with
    | error cause =>
      simp [decoded, liftExcept, Except.mapError, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
    | ok length =>
      simp only [decoded, Except.mapError, liftExcept, pure_bind]
      let base := (checkpoint.getD (.empty, 0)).1
      let generation := (checkpoint.getD (.empty, 0)).2
      exact replay_finish_bound dir base generation length _ count walBudget
        (readSelectedWithCachedExtents_requestBound dir base.committed.toNat length list lstat readSeal readKeeper count)
        removeFile write sync renameFile

end Alvoki.Storage.WalSegmentRepair
