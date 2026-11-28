import Alvoki.Experiments.L0.InterruptedMutation
import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.WAL.Segmented.Proofs.PublicAppendCut

namespace ExperimentalL0.InterruptedMutation

open NativeScope
open NativeRead (SessionAt)
open WalRecoverySlice.Segmented.Native (PhaseMemory Store)
open WalRecoverySlice.Segmented.Native.AppendCut (CutRuntime Stop PublicStop recoverPublic)
open NativeMutationScope (AppendPrimitives Retry Reopens)

/-- The mutex and phase cell belonging to the public WAL handle. -/
structure Worker (p : Prefix path root start) where
  cell : IO.Ref (WalRecoverySlice.Segmented.Native.Phase Store)
  mutex : Std.BaseMutex
  parts : p.wal.Parts cell mutex

abbrev Worker.phase (worker : Worker p) : WalRecoverySlice.Segmented.Native.Phase Store :=
  ((worker.cell.get : BaseIO _) (worker.mutex.lock p.issue).state).val

/-- An interruption before the mutex or phase read returns requires only
the issued primitive. Once the phase has returned, the remaining cut
comes from the exact store and session that it selected. -/
inductive Worker.Cut (worker : Worker p) (change : Change) (stop : Stop)
    (d : WalRecoverySlice.Segmented.Model.Disk) : Prop where
  | lock : stop (liftM worker.mutex.lock : IO Unit) p.issue d → worker.Cut change stop d
  | read : stop (worker.cell.get : IO _) (worker.mutex.lock p.issue).state d → worker.Cut change stop d
  | ready : worker.phase = .ready store session →
      PublicStop worker.cell worker.mutex store session (encode change) p.issue stop d →
      worker.Cut change stop d

/-- The public mutation reaches this same WAL handle from the recovered
L0 session. A nonreturning observation in its mutex, phase update or
worker produces a physical survivor for the first actual reopen. The
second public reopen consumes the first one's reached state. -/
theorem Worker.interrupted {p : Prefix path root start} (worker : Worker p)
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (prior : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (fits : image.view.tail + 1 < UInt64.size)
    (io : AppendPrimitives runtime change)
    (linux : System.Platform.isWindows = false)
    (prim : ∀ store session, worker.phase = .ready store session →
      CutRuntime (fun w => (physical w).disk) store session stop)
    (cut : worker.Cut change stop d)
    (restart : NativeAppendCut.Restarted physical root image.tables p.issue d mode after)
    (reopens : Reopens physical heap path root image life (some (.append (encode change))))
    (a b : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    Retry physical root (NativeMutationScope.uncertainEvents before change) image (some (.append (encode change))) after ∧
      PendingReadScope.TwoReads (some (.append (encode change))) physical path root image life
        (NativeMutationScope.uncertainEvents before change) after a b rootLife := by
  obtain ⟨trace, history, issued, _⟩ := p.issued entry files heap (runtime _ _) prior change scans fits
  let ops := runtime p.lock p.ref
  obtain ⟨reg, pathEq, slot, view, active⟩ := NativeMutationScope.atIssue ops issued
  have registered := (ops.cleanup.cached _ issued.owned _ reg).mp slot
  let op := (io p.lock p.ref p.wal p.session history p.issue reg pathEq issued slot active).worker
  have selected := (heap.read (heap.lock worker.mutex (worker.parts.1 ▸ registered.2.1))).1
  have actual : PublicStop op.cell op.mutex reg.store reg.session (encode change) p.issue stop d := by
    rw [op.parts.1.symm.trans worker.parts.1, op.parts.2.symm.trans worker.parts.2]
    cases cut with
    | lock stopped => exact .lock stopped
    | read stopped => exact .read stopped
    | ready observed site =>
      obtain ⟨rfl, rfl⟩ := WalRecoverySlice.Segmented.Native.Phase.ready.inj (selected.symm.trans observed)
      exact site
  have room : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
    rw [view]
    change image.view.tail + 1 < 18446744073709551616 at fits
    change image.view.tail < 18446744073709551615
    omega
  have recoverable := recoverPublic op (prim _ _ selected) active
    ⟨issued.owned, issued.phase, issued.catalog, issued.manifest⟩ (encode_size change) room linux actual
  have retry := restart.uncertain issued.manifest issued.catalog (view ▸ recoverable) trace
  exact ⟨retry, retry.readTwice reopens a b rootLife⟩

end ExperimentalL0.InterruptedMutation
