import Alvoki.Experiments.L0.NativeWrite
import Alvoki.Experiments.L0.PendingReadScope

namespace ExperimentalL0.NativeMutationScope
open NativeRead (Footprint)
open NativeScope (W Wal Ref)
open NativeReadScope (RestartFiles)
open PendingReadScope (Admitted)
open WalRecoverySlice.Segmented (Contract.Request PermittedView)

/-- The state handed to the next public open. An undelivered success has
a settled extended view. A reported append error can still have either
survivor of precisely the issued mutation. -/
structure Retry (physical : W → Footprint inode) (root : System.FilePath)
    (events : List Event) (image : Selected) (pending : Option WalRecoverySlice.Segmented.Contract.Request) (w : W) : Prop where
  files : RestartFiles pending physical root image w
  trace : Admitted events image pending

theorem Retry.known (trace : Execution.Run events none image) (files : RestartFiles none physical root image w) :
    Retry physical root events image none w := by
  refine ⟨files, fun v allowed => ?_⟩
  have eq : v = image.view := by simpa [PermittedView] using allowed
  subst v
  exact trace

theorem Retry.uncertain (run : Execution.Run events (some session) image)
    (files : RestartFiles (some (.append (encode change))) physical root image w) :
    Retry physical root ((events ++ [.writeUncertain change]) ++ [.stop]) image (some (.append (encode change))) w :=
  ⟨files, PendingReadScope.afterWrite run change⟩

theorem Retry.rejected (run : Execution.Run events (some session) image)
    (files : RestartFiles none physical root image w) :
    Retry physical root ((events ++ [.writeUncertain change]) ++ [.stop]) image none w :=
  .known ((run.uncertainAtView (change := change) (.inl rfl)).stop) files

/-- Delivery and loss are observations of the same successful append and
the same cleanup world. A later loss of the reply cannot undo its bytes. -/
theorem Retry.written (run : Execution.Run events (some session) image)
    (files : RestartFiles none physical root (image.append (encode change)) w) :
    Retry physical root ((events ++ [.written change]) ++ [.stop]) (image.append (encode change)) none w ∧
    Retry physical root ((events ++ [.writeUncertain change]) ++ [.stop]) (image.append (encode change)) none w := by
  have delivered := run.written (fun h installed => Installed.append (history := h) installed change)
  have lost := run.uncertainAtView (change := change) (.inr rfl)
  exact ⟨.known delivered.stop files, .known lost.stop files⟩

end ExperimentalL0.NativeMutationScope
