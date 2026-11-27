import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeCoveredWalUnlinkError
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeCoveredWalUnlinkReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeCoveredWalUnlinkError

variable {state : NativeReadyState}

/-- A returned unlink error supplies its actual reached names and original
held writer to the same reboot observer used for stopped unlinks. -/
def crashCut (error : NativeCoveredWalUnlinkError state) : NativeCoveredWalCrashCut state where
  calls := error.calls
  inventory := error.inventory
  census := error.census
  sameCensus := error.sameCensus
  afterView := error.afterView
  after := error.after
  objects := error.objects
  frameChild other := error.unlinked.keepsOtherChild other
  intact _ := error.unlinked.framesWal
  survivorAllowed valid sealed survives := by
    obtain ⟨layout⟩ := (error.selects valid).2 sealed survives
    exact layout.retained

end NativeCoveredWalUnlinkError

abbrev NativeCoveredWalUnlinkErrorCrash {state : NativeReadyState} (error : NativeCoveredWalUnlinkError state) :=
  NativeCoveredWalCrash error.crashCut

/-- A returned error keeps its original poisoned state and diagnostic.
The reported power loss before close supplies the next marked opener
with one allowed surviving file image. -/
structure NativeCoveredWalUnlinkErrorReboot (current : NativeReadPosition history log)
    {error : NativeCoveredWalUnlinkError current.state} (crash : NativeCoveredWalUnlinkErrorCrash error)
    (input : FilePath) : Prop
    extends NativeCoveredWalReopened current crash input where
  failed : NativeReturnedCoveredWalUnlinkError current error
  custody : current.state.owner ∈ error.census.slots ∧ current.state.directorySlot ∈ error.census.slots ∧
    error.afterView.child error.inventory.lifetime.root "LOCK" = some error.inventory.lifetime.lock ∧
    error.afterView.modelObject error.inventory.lifetime.lock = error.census.inode current.state.owner.description ∧
    error.afterView.modelObject error.inventory.lifetime.root = error.census.inode current.state.directorySlot.description

theorem NativeReadPosition.recoversCoveredWalUnlinkErrorPowerLoss (current : NativeReadPosition history log)
    (error : NativeCoveredWalUnlinkError current.state) (crash : NativeCoveredWalUnlinkErrorCrash error)
    {input : FilePath} (observe : crash.ReopenReports input) : NativeCoveredWalUnlinkErrorReboot current crash input :=
  ⟨current.reopensCoveredWalCut crash observe, current.returnsCoveredWalUnlinkError error,
    error.retainsCustody current.readPrefix.refines.1⟩

end Alvoki.Storage.DiskSession
