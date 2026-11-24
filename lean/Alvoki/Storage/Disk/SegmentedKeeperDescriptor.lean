import Alvoki.Storage.Disk.ReplacedWalDescriptor
import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.WalSegmentRepair

open WAL.Boundary DiskSession

/-- The open file description and filesystem object observed together.
Both identifiers are stable over the lifetime of the retained reference. -/
structure KeeperDescriptorIdentity where
  description : Nat
  inode : Nat

/-- A file sync effect reported for a surviving descriptor. The issuing slot
is still live after the observed drops, and its effect report names the
same description and inode captured before replacement. These identities
come from observation in the same filesystem object namespace. -/
structure DelayedKeeperSync where
  captured : KeeperDescriptorIdentity
  references : HeldLockReferences captured.description
  issuer : LockReference
  drops : List LockReferenceDrop
  retained : issuer ∈ references.remaining drops
  effectTarget : KeeperDescriptorIdentity
  sameTarget : effectTarget = captured
  outcomes : List ByteArray

/-- Project the path's keeper binding and byte survival choices from the
inode model. The staged file, metadata, sealed files and later names come
from the existing path model. -/
def FileImage.withKeeperInodes (files : FileImage) (inodes : WalInodeImage) : FileImage :=
  let projected := (inodes.project files.directory).wal
  { files with keeper := { projected with staged := files.keeper.staged } }

def DelayedKeeperSync.effect (report : DelayedKeeperSync) (image : WalInodeImage) : WalInodeImage :=
  image.reportFileSync report.effectTarget.inode report.outcomes

/-- Once only the live binding can survive, a report on a different inode
cannot change any field of the segmented repair projection, even when it
changes the old inode's crash bytes. -/
theorem DelayedKeeperSync.unchangedProjection (report : DelayedKeeperSync) (files : FileImage)
    (inodes : WalInodeImage) (settled : inodes.crashBindings = [inodes.active])
    (stale : report.captured.inode ≠ inodes.active) :
    files.withKeeperInodes (report.effect inodes) = files.withKeeperInodes inodes := by
  have different : inodes.active ≠ report.effectTarget.inode := by
    rw [report.sameTarget]
    exact Ne.symm stale
  simp [FileImage.withKeeperInodes, WalInodeImage.project, DelayedKeeperSync.effect,
    WalInodeImage.reportFileSync, settled, different]

/-- A delayed sync on the pre-replacement inode preserves the exact ready
image and locks after the new keeper name is settled. The observed effect
targets the old retained description even though the pathname now resolves
to the replacement. The resulting state is the same admitted retry
endpoint. -/
theorem DelayedKeeperSync.preservesSettledReplacement (report : DelayedKeeperSync)
    (previous : WalInodeImage) (replacement : Nat)
    {directory : DiskDirectory} {target : Target} {admits : Target → Prop}
    {initial before : LockedFileState FileImage}
    (trace : BoundedReopenTrace directory admits initial before)
    (ready : before.image.Ready target)
    (oldTarget : report.captured.inode = previous.active) (distinct : previous.active ≠ replacement) :
    let current := (previous.renameSynced replacement target.trimmed).settleBinding
    let after := { before with image := before.image.withKeeperInodes (report.effect current) }
    after = before ∧ BoundedReopenTrace directory admits initial after := by
  intro current after
  have keeper : before.image.withKeeperInodes current = before.image := by
    simp [current, FileImage.withKeeperInodes, WalInodeImage.project, WalInodeImage.settleBinding,
      WalInodeImage.renameSynced]
    rw [← ready.keeperDurable, ← ready.keeper]
  have unchanged := report.unchangedProjection before.image current rfl (oldTarget ▸ distinct)
  have exactState : after = before := by
    dsimp only [after]
    rw [unchanged, keeper]
  exact ⟨exactState, exactState.symm ▸ trace⟩

end Alvoki.Storage.WalSegmentRepair
