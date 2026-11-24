import Alvoki.Storage.Disk.LockDescriptionLifetime
import Alvoki.Storage.Disk.CheckpointLockHandoff

namespace Alvoki.Storage.DiskSession

/-- A reported successful close or the observation that all references
to the poisoned writer's lock have been dropped. -/
inductive SegmentedFailureRelease (writer : Nat) where
  | closed
  | references (held : HeldLockReferences writer) (drops : List LockReferenceDrop)
      (last : held.remaining drops = [])

def SegmentedFailureRelease.Observed {image : Type} {directory : DiskDirectory} {writer : Nat}
    (release : SegmentedFailureRelease writer) (poisoned : Phase Installed × LockedFileState image)
    (released : LockedFileState image) : Prop :=
  match release with
  | .closed => runCloseWithFiles directory writer .success poisoned = .ok () (.closed, released)
  | .references held drops _ => held.afterFileDrops drops directory poisoned.2 = released

end Alvoki.Storage.DiskSession
