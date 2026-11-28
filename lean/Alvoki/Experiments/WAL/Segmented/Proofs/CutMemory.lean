import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.ChildCutIO

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Model (Disk)
open Alvoki.NativePost (W)

/-- Heap instructions and advisory unlock leave every file unchanged
except for permitted independent background writebacks. -/
inductive Volatile : {α : Type} → IO α → Prop where
  | lock (m : Std.BaseMutex) : Volatile (liftM m.lock)
  | leave (m : Std.BaseMutex) : Volatile (liftM m.unlock)
  | get (r : IO.Ref α) : Volatile (r.get : IO α)
  | set (r : IO.Ref α) (x : α) : Volatile (r.set x : IO Unit)
  | swap (r : IO.Ref α) (x : α) : Volatile (r.swap x : IO α)
  | release (h : IO.FS.Handle) : Volatile h.unlock

structure VolatileIO (disk : W → Disk) (stop : ControlCutIO.Stops) : Prop where
  returned : ∀ {α} (a : IO α), Volatile a → ∀ w, Writebacks (disk w) (disk (returnedWorld (a w)))
  stopped : ∀ {α} (a : IO α), Volatile a → ∀ w d, stop a w d → Writebacks (disk w) d

private theorem baseWorld (a : BaseIO α) (w : W) : returnedWorld ((liftM a : IO α) w) = (a w).state := by
  change returnedWorld (BaseIO.toEIO a w) = _
  cases run : a w
  simp [BaseIO.toEIO, returnedWorld,run]

theorem VolatileIO.lock (io : VolatileIO disk stop) (m : Std.BaseMutex) (w : W) :
    Writebacks (disk w) (disk (m.lock w).state) := by
  simpa only [baseWorld] using io.returned _ (.lock m) w

theorem VolatileIO.get (io : VolatileIO disk stop) (r : IO.Ref α) (w : W) :
    Writebacks (disk w) (disk ((r.get : BaseIO _) w).state) := by
  exact io.returned _ (.get r) w

theorem VolatileIO.set (io : VolatileIO disk stop) (r : IO.Ref α) (v : α) (w : W) :
    Writebacks (disk w) (disk ((r.set v : BaseIO _) w).state) := by
  exact io.returned _ (.set r v) w

theorem VolatileIO.swap (io : VolatileIO disk stop) (r : IO.Ref α) (v : α) (w : W) :
    Writebacks (disk w) (disk ((r.swap v : BaseIO _) w).state) := by
  exact io.returned _ (.swap r v) w

theorem VolatileIO.childEntry (io : VolatileIO disk stop) (site : ChildEntry h w a t)
    (cut : stop a t d) : Writebacks (disk w) d := by
  cases site with
  | mutex _ => exact io.stopped _ (.lock _) _ _ cut
  | read _ => exact (io.lock _ _).trans (io.stopped _ (.get _) _ _ cut)

theorem VolatileIO.close (io : VolatileIO disk stop) (op : AppendIO.CloseOperand h fd w)
    (site : ClosePoint h fd w op a t) (cut : stop a t d) : Writebacks (disk w) d := by
  have first := io.lock op.mutex w
  have read := first.trans (io.get op.cell _)
  have closed := read.trans (io.set op.cell .closed _)
  cases site with
  | close => exact read.trans (io.stopped _ (.set _ _) _ d cut)
  | unlock => exact closed.trans (io.stopped _ (.release _) _ d cut)
  | leave => exact (closed.trans (io.returned _ (.release fd) op.issue)).trans (io.stopped _ (.leave _) _ d cut)

theorem VolatileIO.closeSite (io : VolatileIO disk stop) (site : CloseSite h w a t) (cut : stop a t d) :
    Writebacks (disk w) d := by
  cases site with
  | entry early => exact io.childEntry early cut
  | closed _ _ => exact ((io.lock _ _).trans (io.get _ _)).trans (io.stopped _ (.leave _) _ _ cut)
  | observed op point => exact io.close op point cut

theorem VolatileIO.oldClose (io : VolatileIO disk stop) (site : OldClose s w a t)
    (cut : stop a t d) : Writebacks (disk w) d := by
  cases site with
  | detach => exact io.stopped _ (.swap _ _) _ _ cut
  | child taken site => exact (io.swap s.active none w).trans (io.closeSite site cut)

end WalRecoverySlice.Segmented.Native.AppendCut
