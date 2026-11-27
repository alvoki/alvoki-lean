import Alvoki.Storage.Disk.WAL.WalSegmentCommit

namespace Alvoki.Storage.SyncPathGroup

open System

private def syncError (path : FilePath) (error : IO.Error) : IO.Error :=
  IO.userError s!"sync failed for '{path}': {error}"

/-- Apply the native grouped barrier's control flow to a supplied sync
callback. Remaining members are attempted even when an earlier member has
failed. The first error determines the reported diagnostic. -/
@[inline] def run [Monad m] [MonadExceptOf IO.Error m]
    (sync : FilePath → m Unit) (paths : Array FilePath) : m Unit := do
  let mut failure := none
  for path in paths do
    try sync path catch error =>
      if failure.isNone then failure := some (syncError path error)
  if let some error := failure then throw error

/-- A one-file barrier returns the reached state on both outcomes and
adds the pathname to a reported failure. -/
theorem run_single {σ : Type} (sync : FilePath → EStateM IO.Error σ Unit)
    (path : FilePath) (initial : σ) :
    run sync #[path] initial =
      match sync path initial with
      | .ok () after => .ok () after
      | .error error after => .error (syncError path error) after := by
  unfold run
  rw [← Array.forIn_toList]
  cases report : sync path initial with
  | ok result after =>
    cases result
    simp [List.forIn_cons, List.forIn_nil, report, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
      StateT.pure, tryCatchThe, EStateM.tryCatch, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  | error cause after =>
    simp [List.forIn_cons, List.forIn_nil, report, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
      StateT.pure, tryCatchThe, EStateM.tryCatch, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      EStateM.Backtrackable.restore, EStateM.dummyRestore]

/-- The two-file WAL barrier attempts the staged marker against the exact
state left by the keeper sync, including any effect left by a failed sync.
The group succeeds only if both operations succeed. -/
theorem run_pair {σ : Type} (sync : FilePath → EStateM IO.Error σ Unit)
    (keeper staged : FilePath) (initial : σ) :
    run sync #[keeper, staged] initial =
      match sync keeper initial with
      | .ok () afterKeeper =>
        match sync staged afterKeeper with
        | .ok () afterMarker => .ok () afterMarker
        | .error error afterMarker => .error (syncError staged error) afterMarker
      | .error error afterKeeper =>
        match sync staged afterKeeper with
        | .ok () afterMarker | .error _ afterMarker => .error (syncError keeper error) afterMarker := by
  unfold run
  rw [← Array.forIn_toList]
  simp only [List.forIn_cons, List.forIn_nil]
  cases first : sync keeper initial with
  | ok result afterKeeper =>
    cases result
    cases second : sync staged afterKeeper <;>
      simp [MonadExcept.tryCatch, MonadExceptOf.tryCatch, StateT.pure, tryCatchThe, EStateM.tryCatch,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, MonadExcept.throw, throwThe, MonadExceptOf.throw,
        EStateM.throw, EStateM.Backtrackable.restore, EStateM.dummyRestore, first, second]
  | error cause afterKeeper =>
    cases second : sync staged afterKeeper <;>
      simp [MonadExcept.tryCatch, MonadExceptOf.tryCatch, StateT.pure, tryCatchThe, EStateM.tryCatch,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, MonadExcept.throw, throwThe, MonadExceptOf.throw,
        EStateM.throw, EStateM.Backtrackable.restore, EStateM.dummyRestore, first, second]

/-- With a successful append and staged write, the native publication
schedule can reach rename only after both member callbacks return
successfully. A failed group returns the exact final callback state. -/
theorem failedWalPublication {σ : Type} (directory : DiskDirectory) (activeFirst newBytes : Nat)
    (event : WAL.Write) (append write : FilePath → ByteArray → EStateM IO.Error σ Unit)
    (sync : FilePath → EStateM IO.Error σ Unit)
    (rename : FilePath → FilePath → EStateM IO.Error σ Unit) {initial appended staged after : σ}
    {cause : IO.Error}
    (appendReport : append (directory.file (.walSegment activeFirst)) (WAL.encodeFrame event) initial = .ok () appended)
    (stageReport : write (directory.file .stagedWalBoundary) (WAL.Boundary.encode newBytes.toUInt64) appended =
      .ok () staged)
    (failure : run sync #[directory.file (.walSegment activeFirst), directory.file .stagedWalBoundary] staged =
      .error cause after) :
    WalSegmentCommit.commitAt directory activeFirst event newBytes append write (run sync) rename initial =
      .error cause after := by
  rw [WalSegmentCommit.commitAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, appendReport, stageReport, failure]

end Alvoki.Storage.SyncPathGroup
