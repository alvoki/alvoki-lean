import Alvoki.Experiments.L0.NativeScope
import Alvoki.Experiments.L0.NativeReadClient

namespace ExperimentalL0.NativeRead
open Lifecycle

/-- Public reads have all reported errors caught. The concrete callback
therefore passes its exact reply list and reached world to scope cleanup. -/
theorem readMany_callback (ready : Online physical root lock ref wal session image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables start))
    (prior : Execution.Run events (some session) image) (keys : List UInt64)
    (cleanup : ∀ replies t, Execution.Run (events ++ readEvents keys replies) (some session) image →
      Online physical root lock ref wal session image history t →
      allReleased life ref (root / "tables") handle keys start →
      NativeScope.Release ref lock t (ok replies) err) :
    NativeScope.Callback ref lock (readMany handle keys : IO (List Reply)) start ok err := by
  obtain ⟨trace, _, reached, released⟩ := readMany_run ready binding read prim .refl prior keys
  have done_ := cleanup _ _ trace reached released
  unfold NativeScope.Callback NativeScope.Post
  change (match readMany handle keys start with | ⟨xs, t⟩ => _)
  generalize h : readMany handle keys start = r at *
  cases r
  exact done_

end ExperimentalL0.NativeRead
