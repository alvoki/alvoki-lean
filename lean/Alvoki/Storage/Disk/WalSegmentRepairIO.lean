import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.WriteAheadLog
import Alvoki.Storage.Publication.DiskPublication
import Alvoki.Storage.Publication.RunCollection

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The keeper's original bytes and the later regular names observed by
read-only preparation under the database lock. Offsets count WAL frames. -/
structure Plan where
  through : Nat
  keeper : Nat
  newer : List Nat
  keeperBytes : ByteArray

def Plan.keeperSize (plan : Plan) : Nat :=
  (plan.through - plan.keeper) * WAL.frameSize

def Plan.valid (plan : Plan) : Bool :=
  decide (plan.keeper ≤ plan.through) &&
    decide (plan.keeperSize ≤ plan.keeperBytes.size) &&
    plan.newer.all (fun first => decide (plan.through < first))

theorem Plan.valid_iff (plan : Plan) :
    plan.valid = true ↔ plan.keeper ≤ plan.through ∧ plan.keeperSize ≤ plan.keeperBytes.size ∧
      ∀ first ∈ plan.newer, plan.through < first := by
  simp [Plan.valid, Bool.and_eq_true, List.all_eq_true, and_assoc]

inductive Step where
  | unlink (first : Nat)
  | syncPruned
  | replace (step : Publication.Step)
  | syncKeeper
  deriving DecidableEq, Repr

/-- Settle suffix absence before shortening the keeper. Sync the directory
even when the retry inventory already hides every later name. -/
def steps (newer : List Nat) (replaceKeeper : Bool) : List Step :=
  newer.map Step.unlink ++ [.syncPruned] ++
    if replaceKeeper then Publication.steps.map Step.replace else [.syncKeeper]

def performPaths [Monad m] (dir : DiskDirectory) (plan : Plan)
    (removeFile : FilePath → m (Except IO.Error Unit)) (raise : IO.Error → m Unit)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : Step → m Unit
  | .unlink first => RunCollection.performPaths removeFile (fun path => sync #[path]) raise
    (fun offset => dir.file (.walSegment offset)) dir.path (.unlink first)
  | .syncPruned => sync #[dir.path]
  | .replace step => Publication.performReplacement
    (fun path => write path (plan.keeperBytes.extract 0 plan.keeperSize)) sync renameFile
    (dir.file .stagedWal) dir.path (fun _ => dir.file (.walSegment plan.keeper)) #[] step
  | .syncKeeper => sync #[dir.file (.walSegment plan.keeper)]

/-- Prepare under the held database lock, then settle the prepared visible
marker before pruning. Preparation checks the exact selected data and
returns fresh observations on each retry. The caller owns the stable
directory and its WAL staging name for the duration of the schedule. -/
def runAt [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (prepare : m Plan)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Unit := do
  let plan ← prepare
  if plan.valid then
    sync #[dir.path]
    (steps plan.newer (decide (plan.keeperSize < plan.keeperBytes.size))).forM
      (performPaths dir plan removeFile throw write sync renameFile)
  else throw (IO.userError "invalid WAL segment repair plan")

theorem runAt_fileEffects [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (prepare : m Plan)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) :
    runAt dir prepare removeFile write sync renameFile = (do
      let plan ← prepare
      if plan.valid then
        sync #[dir.path]
        (steps plan.newer (decide (plan.keeperSize < plan.keeperBytes.size))).forM fun step =>
          match step with
          | .unlink first => do
            match RunCollection.ownedUnlinkResult (← removeFile (dir.file (.walSegment first))) with
            | .ok () => pure ()
            | .error err => throw err
          | .syncPruned => sync #[dir.path]
          | .replace .writeStaged => write (dir.file .stagedWal) (plan.keeperBytes.extract 0 plan.keeperSize)
          | .replace .syncStaged => sync #[dir.file .stagedWal]
          | .replace .renameStaged => renameFile (dir.file .stagedWal) (dir.file (.walSegment plan.keeper))
          | .replace .syncDirectory => sync #[dir.path]
          | .syncKeeper => sync #[dir.file (.walSegment plan.keeper)]
      else throw (IO.userError "invalid WAL segment repair plan")) := by
  unfold runAt
  congr 1
  funext plan
  split
  · congr 1
    funext _
    congr 1
    funext step
    cases step with
    | replace step => cases step <;> rfl
    | unlink _ | syncPruned | syncKeeper => rfl
  · rfl

end Alvoki.Storage.WalSegmentRepair
