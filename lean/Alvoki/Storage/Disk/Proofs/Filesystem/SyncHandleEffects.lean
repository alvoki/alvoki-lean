import Alvoki.Storage.Disk.SyncHandleRouting
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedDelayedDirectorySync
import Alvoki.Storage.Disk.Proofs.Keeper.SegmentedKeeperDescriptor

namespace Alvoki.Storage.SyncHandleRouting

open System DiskSession WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- The effect flag distinguishes an error before and after the reported
effect even when that effect leaves the modeled state unchanged. -/
inductive FsyncResult {state : Type} (before persisted : state) :
    Bool → EStateM.Result IO.Error state Unit → Prop where
  | completed : FsyncResult before persisted true (.ok () persisted)
  | errorBefore (cause : IO.Error) : FsyncResult before persisted false (.error cause before)
  | errorAfter (cause : IO.Error) : FsyncResult before persisted true (.error cause persisted)

/-- A raw successful return and the effect report determine the exact
settled state. The caller need only observe that the syscall succeeded. -/
theorem FsyncResult.completed_of_return {state : Type} {before persisted : state}
    {effective : Bool} {returned : EStateM.Result IO.Error state Unit}
    (observed : FsyncResult before persisted effective returned)
    (succeeded : ∃ reached, returned = .ok () reached) :
    returned = .ok () persisted := by
  cases observed <;> simp_all

/-- The native report for one reached fsync. The captured description and
object identities must come from the same stable namespace as the binding
observation. A live slot retains the description through the reported drops.
The kernel and filesystem must account for the actual returned effect. -/
structure FsyncObservation {handle state : Type} (description inode : handle → Nat)
    (descriptor : handle) (before : state) (persist : Nat → state → state)
    (returned : EStateM.Result IO.Error state Unit) where
  references : HeldLockReferences (description descriptor)
  issuer : LockReference
  drops : List LockReferenceDrop
  live : issuer ∈ references.remaining drops
  effectDescription : Nat
  effectInode : Nat
  sameDescription : effectDescription = description descriptor
  sameInode : effectInode = inode descriptor
  effective : Bool
  effect : FsyncResult before (persist effectInode before) effective returned

/-- The delayed directory report provides the same identity, lifetime and
completion observations, with the directory-specific persistence effect. -/
def FsyncObservation.ofDirectory {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    (before : LockedFileState FileImage) :
    FsyncObservation DirectoryDescriptorIdentity.description DirectoryDescriptorIdentity.inode report.captured before
      (fun _ state => { state with image := state.image.syncDirectory }) (report.run before) where
  references := report.references
  issuer := report.issuer
  drops := report.drops
  live := report.retained
  effectDescription := report.effectTarget.description
  effectInode := report.effectTarget.inode
  sameDescription := congrArg DirectoryDescriptorIdentity.description report.sameTarget
  sameInode := congrArg DirectoryDescriptorIdentity.inode report.sameTarget
  effective := report.outcome.effective
  effect := by
    cases outcome : report.outcome <;>
      simp only [DelayedDirectorySync.run, outcome, DelayedDirectorySyncOutcome.effective] <;> constructor

/-- Keeper persistence uses the reported survival choices for the exact
inode. The syscall outcome must account for that effect at its return. -/
def FsyncObservation.ofKeeper (report : DelayedKeeperSync) (before : WalInodeImage)
    {effective : Bool} {returned : EStateM.Result IO.Error WalInodeImage Unit}
    (effect : FsyncResult before (report.effect before) effective returned) :
    FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode report.captured before
      (fun inode state => state.reportFileSync inode report.outcomes) returned where
  references := report.references
  issuer := report.issuer
  drops := report.drops
  live := report.retained
  effectDescription := report.effectTarget.description
  effectInode := report.effectTarget.inode
  sameDescription := congrArg KeeperDescriptorIdentity.description report.sameTarget
  sameInode := congrArg KeeperDescriptorIdentity.inode report.sameTarget
  effective := effective
  effect := effect

/-- A failed selection returns the reached cache and file state. No fsync
report is needed, since the shared selector never invokes its callback. -/
theorem sync_resolutionError {handle state : Type} (dir path : FilePath) (cache : Cache handle)
    (before : state) (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit)
    {returned : EStateM.Result IO.Error (Cache handle × state) Unit}
    (execution : returned = sync dir openRead fsync path (cache, before))
    {cause : IO.Error} {reached : Cache handle × state}
    (failed : cache.resolve dir path openRead before = .error cause reached) :
    returned = .error cause reached := by
  rw [execution]
  simp only [sync, failed]

/-- Apply a reached syscall report to the descriptor chosen by the real
shared selector. `syncWithHandles_cache` supplies the execution equation.
The selected object's binding and lifetime are explicit native observations.
The resulting cache remains the one reached before the callback on both
success and error, including when an error follows the filesystem effect. -/
theorem sync_observedEffect {handle state : Type} (dir path : FilePath) (cache : Cache handle)
    (before : state) (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) (description inode : handle → Nat)
    (bindings : state → FilePath → Option Nat) (persist : Nat → state → state)
    {returned : EStateM.Result IO.Error (Cache handle × state) Unit}
    (execution : returned = sync dir openRead fsync path (cache, before))
    (owned : cache.Agrees dir inode (bindings before))
    (fresh : ∀ {opened reached}, openRead path before = .ok opened reached →
      bindings reached path = some (inode opened))
    {descriptor : handle} {next : Cache handle} {atEffect : state}
    (resolved : cache.resolve dir path openRead before = .ok descriptor (next, atEffect))
    (report : FsyncObservation description inode descriptor atEffect persist (fsync descriptor atEffect)) :
    bindings atEffect path = some report.effectInode ∧
      FsyncResult (next, atEffect) (next, persist report.effectInode atEffect) report.effective returned := by
  refine ⟨?_, ?_⟩
  · rw [report.sameInode]
    exact Cache.resolve_owned owned fresh resolved
  · rw [execution]
    simp only [sync, resolved]
    have liftResult {effective result} (effect : FsyncResult atEffect (persist report.effectInode atEffect) effective result) :
        FsyncResult (next, atEffect) (next, persist report.effectInode atEffect) effective (withCache next result) := by
      cases effect <;> constructor
    exact liftResult report.effect

end Alvoki.Storage.SyncHandleRouting
