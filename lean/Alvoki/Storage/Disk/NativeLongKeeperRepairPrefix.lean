import Alvoki.Storage.Disk.LongWalBindingPublication

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The checked long-keeper prefix reaches the original replacement
continuation with the actual stage already written. Later callbacks
can return either success or error on that same execution. -/
theorem finishBoundedMarkedOpen_afterStage {heap : Type} (directory : DiskDirectory) (plan : Plan)
    (physicalSize : Nat) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (longer : plan.keeperSize < physicalSize) {entry authorized pruned staged : heap}
    (authorize : sync #[directory.path] entry = .ok () authorized)
    (prune : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () pruned)
    (written : write (directory.file .stagedWal) plan.keeperBytes pruned = .ok () staged) :
    let perform := performPaths directory plan remove throw write sync rename
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry =
      (do
        perform (.replace .syncStaged)
        perform (.replace .renameStaged)
        perform (.replace .syncDirectory)
        pure () : EStateM IO.Error heap Unit) staged := by
  intro perform
  rw [finishBoundedMarkedOpen_long directory plan physicalSize remove write sync rename valid size longer]
  change (do
    sync #[directory.path]
    ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform)
    perform (.replace .writeStaged)
    perform (.replace .syncStaged)
    perform (.replace .renameStaged)
    perform (.replace .syncDirectory)
    pure () : EStateM IO.Error heap Unit) entry = _
  change ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) authorized = .ok () pruned at prune
  have exact : plan.keeperBytes.extract 0 plan.keeperSize = plan.keeperBytes := by
    rw [← size, ByteArray.extract_zero_size]
  have stagedWrite : perform (.replace .writeStaged) pruned = .ok () staged := by
    simp only [perform, performPaths, Publication.performReplacement, exact, written]
  simp only [Bind.bind, EStateM.bind, authorize, prune, stagedWrite]

end Alvoki.Storage.WalSegmentRepair
