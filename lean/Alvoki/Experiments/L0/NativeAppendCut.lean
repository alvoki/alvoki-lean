import Alvoki.Experiments.L0.NativeMutationScope
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCut

namespace ExperimentalL0.NativeAppendCut

open NativeScope (W)
open NativeRead (Footprint tableNamespace)
open WalRecoverySlice.Segmented (Restart)
open WalRecoverySlice.Segmented.Model (Disk)
open WalRecoverySlice.Segmented.Native.AppendCut (Survivor)
open NativeReadScope (RestartFiles)

/-- Restart effects are stated as physical projections. The table frame
protects the committed inode/name pairs only. The manifest projection
chooses the visible bytes for process exit or a durable survivor for
power loss. It carries no WAL or client invariant. -/
structure Restarted (physical : W → Footprint inode) (root : System.FilePath)
    (tables : Catalog) (origin : W) (d : Disk) (mode : Restart) (after : W) : Prop where
  files : Survivor d mode (physical after).disk
  catalog : (tableNamespace physical root).Keeps origin after tables
  manifest : match mode with
    | .processExit => (physical after).manifest.active = (physical origin).manifest.active
    | .powerLoss => (physical after).manifest.active ∈ (physical origin).manifest.survivors

theorem Restarted.filesAt (restart : Restarted physical root image.tables origin d mode after)
    (manifest : (physical origin).manifest.Stable (L0Manifest.encode image.version))
    (catalog : (tableNamespace physical root).Represents origin image.tables)
    (wal : WalRecoverySlice.Segmented.Recoverable image.view pending d) :
    RestartFiles pending physical root image after := by
  refine ⟨catalog.frame restart.catalog, ?_, restart.files.recoverable wal⟩
  have survivor := restart.manifest
  cases mode with
  | processExit => exact survivor.trans manifest.1
  | powerLoss => simpa only [manifest.2, List.mem_singleton] using survivor

theorem Restarted.uncertain (restart : Restarted physical root image.tables origin d mode after)
    (manifest : (physical origin).manifest.Stable (L0Manifest.encode image.version))
    (catalog : (tableNamespace physical root).Represents origin image.tables)
    (wal : WalRecoverySlice.Segmented.Recoverable image.view (some (.append (encode change))) d)
    (trace : Execution.Run events (some session) image) :
    NativeMutationScope.Retry physical root ((events ++ [.writeUncertain change]) ++ [.stop])
      image (some (.append (encode change))) after :=
  .uncertain trace (restart.filesAt manifest catalog wal)

end ExperimentalL0.NativeAppendCut
