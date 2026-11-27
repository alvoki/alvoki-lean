import Alvoki.Storage.Disk.Proofs.Filesystem.SyncHandleEffects
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCommitEffects

namespace Alvoki.Storage.SyncHandleRouting

open System WAL.Boundary WalSegmentCommit

/-- The reached state includes effects left by a failing callback. -/
def reachedState {ε state value : Type} : EStateM.Result ε state value → state
  | .ok _ after | .error _ after => after

/-- Project the physical write state and success status for crash accounting. -/
def projectWriteGroup {handle : Type} :
    EStateM.Result IO.Error (Cache handle × WriteFiles) Unit → EStateM.Result Unit WriteFiles Unit
  | .ok value (_, after) => .ok value after
  | .error _ (_, after) => .error () after

/-- Assemble the two syscall reports into the write model's grouped outcome.
The keeper can have incomplete crash tails even when the staged marker is
durable. A keeper error does not suppress the staged attempt. -/
def writeGroupOutcome (keeper staged : EStateM.Result IO.Error WriteFiles Unit)
    (wal : WalSyncEffect) (stagedSynced : Bool) : Except GroupSyncFailure Unit :=
  match keeper, staged with
  | .ok _ _, .ok _ _ => .ok ()
  | _, _ => .error ⟨wal, stagedSynced⟩

private def projectPair (keeper staged : EStateM.Result IO.Error WriteFiles Unit) :
    EStateM.Result Unit WriteFiles Unit :=
  match keeper, staged with
  | .ok _ _, .ok _ after => .ok () after
  | _, _ => .error () (reachedState staged)

private theorem syncWal_prior {before : WriteFiles} {prior : List ByteArray}
    (previous : before.crashTails = ByteArray.empty :: prior) : before.syncWal (.incomplete prior) = before := by
  cases before
  simp_all [WriteFiles.syncWal]

private theorem markerStep_matches {before : WriteFiles} (effects : WriteEffects) (bytes : ByteArray)
    (prior : List ByteArray) (wal : WalSyncEffect) {keeperEffective stagedSynced : Bool}
    {keeperResult stagedResult : EStateM.Result IO.Error WriteFiles Unit}
    (previous : before.crashTails = ByteArray.empty :: prior)
    (scratch : before.marker.staged = some (bytes, false))
    (first : FsyncResult before (before.syncWal wal) keeperEffective keeperResult)
    (complete : ∀ after, keeperResult = .ok () after → wal = .complete)
    (second : FsyncResult (reachedState keeperResult)
      (((reachedState keeperResult).stepMarker bytes .syncStaged).getD (reachedState keeperResult)) stagedSynced stagedResult)
    (reported : effects.sync = writeGroupOutcome keeperResult stagedResult
      (if keeperEffective then wal else .incomplete prior) stagedSynced) :
    projectPair keeperResult stagedResult = effects.markerStep bytes .syncStaged before := by
  have noWal := syncWal_prior previous
  cases first <;> cases second
  case completed.completed =>
    simpa [projectPair, reachedState, complete _ rfl] using
      (effects.markerStep_syncStaged_success bytes scratch reported).symm
  all_goals simp_all [projectPair, writeGroupOutcome, WriteEffects.markerStep, WriteFiles.stepMarker, WriteFiles.syncWal,
    Publication.Image.step, reachedState]

/-- The exact two file syncs behind the write callback's `syncStaged` step.
The cache starts with the current keeper and the freshly staged marker. The
first syscall leaves the stage's pathname binding in place. Each syscall
report names its captured live description at the state it actually reaches.
The returned cache has consumed the stage on every outcome. The original
diagnostic stays in the executable result and is erased for the write model. -/
theorem groupedWrite_effects {handle : Type} (dir keeper staged : FilePath)
    (cache : Cache handle) (before : WriteFiles) (effects : WriteEffects) (bytes : ByteArray)
    (openRead : FilePath → EStateM IO.Error WriteFiles handle) (fsync : handle → EStateM IO.Error WriteFiles Unit)
    (description inode : handle → Nat) (bindings : WriteFiles → FilePath → Option Nat)
    {keeperHandle stagedHandle : handle}
    (keeperNotDirectory : keeper ≠ dir) (stagedNotDirectory : staged ≠ dir)
    (keeperMiss : cache.pending.find? (fun entry => entry.1 == keeper) = none)
    (active : cache.active = some (keeper, keeperHandle))
    (pending : cache.pending.find? (fun entry => entry.1 == staged) = some (staged, stagedHandle))
    (owned : cache.Agrees dir inode (bindings before))
    (distinct : inode keeperHandle ≠ inode stagedHandle)
    (prior : List ByteArray) (wal : WalSyncEffect)
    (previous : before.crashTails = ByteArray.empty :: prior)
    (scratch : before.marker.staged = some (bytes, false))
    (stableStage : bindings (reachedState (fsync keeperHandle before)) staged = bindings before staged)
    (keeperReport : FsyncObservation description inode keeperHandle before (fun _ state => state.syncWal wal)
      (fsync keeperHandle before))
    (complete : ∀ after, fsync keeperHandle before = .ok () after → wal = .complete)
    (stagedReport : FsyncObservation description inode stagedHandle (reachedState (fsync keeperHandle before))
      (fun _ state => (state.stepMarker bytes .syncStaged).getD state)
      (fsync stagedHandle (reachedState (fsync keeperHandle before))))
    (reported : effects.sync = writeGroupOutcome (fsync keeperHandle before)
      (fsync stagedHandle (reachedState (fsync keeperHandle before)))
      (if keeperReport.effective then wal else .incomplete prior) stagedReport.effective) :
    let result := SyncPathGroup.run (sync dir openRead fsync) #[keeper, staged] (cache, before)
    bindings before keeper = some keeperReport.effectInode ∧
      bindings (reachedState (fsync keeperHandle before)) staged = some stagedReport.effectInode ∧
      keeperReport.effectInode ≠ stagedReport.effectInode ∧
      (reachedState result).1 = cache.consume staged ∧
      projectWriteGroup result = effects.markerStep bytes .syncStaged before := by
  dsimp only
  have projected := markerStep_matches effects bytes prior wal previous scratch keeperReport.effect
    complete stagedReport.effect reported
  refine ⟨keeperReport.sameInode ▸ owned.active active, stableStage.trans (stagedReport.sameInode ▸ owned.pending pending),
    ?_, ?_⟩
  · simpa only [keeperReport.sameInode, stagedReport.sameInode] using distinct
  · rw [groupedActivePending keeperNotDirectory stagedNotDirectory keeperMiss active pending openRead fsync before]
    cases first : fsync keeperHandle before with
    | ok value afterKeeper =>
      cases value
      cases second : fsync stagedHandle afterKeeper <;>
        exact ⟨by simp [second, reachedState], by
          simpa [first, second, reachedState, projectPair, projectWriteGroup] using projected⟩
    | error cause afterKeeper =>
      cases second : fsync stagedHandle afterKeeper <;>
        exact ⟨by simp [second, reachedState], by
          simpa [first, second, reachedState, projectPair, projectWriteGroup] using projected⟩

end Alvoki.Storage.SyncHandleRouting
