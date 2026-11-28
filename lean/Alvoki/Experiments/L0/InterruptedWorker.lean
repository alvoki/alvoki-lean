import Alvoki.Experiments.L0.InterruptedMutation
import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.WAL.Segmented.Proofs.PublicAppendCut

namespace ExperimentalL0.InterruptedMutation

open NativeScope
open NativeRead (SessionAt)
open WalRecoverySlice.Segmented.Native (PhaseMemory Store)
open WalRecoverySlice.Segmented.Native.AppendCut (CutRuntime Stop PublicStop recoverPublic BeforeWorker AfterSuccess VolatileIO recoverAfterSuccess)
open NativeMutationScope (AppendPrimitives Retry Reopens)
open WalRecoverySlice.Segmented.Native.AppendIO (LocalIO Active)

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

private theorem Worker.prepared {p : Prefix path root start} (worker : Worker p)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (io : AppendPrimitives runtime change)
    (issued : SessionAt physical root p.lock p.ref p.wal p.session image history p.issue (.updating p.wal))
    (fits : image.view.tail + 1 < UInt64.size) :
    ∃ reg : WalRecoverySlice.Segmented.Native.Registration, ∃ pathEq : reg.store.root = (runtime p.lock p.ref).wal.acquire.canonical,
      let mem := ((runtime p.lock p.ref).wal.worker reg.store pathEq).children.memory
      ∃ _op : LocalIO mem heap (NativeRecoverAt.Held physical root p.lock p.ref image (.updating p.wal))
          p.wal reg (encode change) p.issue,
        Active mem heap p.wal reg p.issue ∧ worker.phase = .ready reg.store reg.session ∧
          reg.session.view = image.view ∧ reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
  let ops := runtime p.lock p.ref
  obtain ⟨reg, pathEq, slot, view, active⟩ := NativeMutationScope.atIssue ops issued
  have registered := (ops.cleanup.cached _ issued.owned _ reg).mp slot
  let op := (io p.lock p.ref p.wal p.session history p.issue reg pathEq issued slot active).worker
  have selected := (heap.read (heap.lock worker.mutex (worker.parts.1 ▸ registered.2.1))).1
  have room : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
    rw [view]
    change image.view.tail + 1 < 18446744073709551616 at fits
    change image.view.tail < 18446744073709551615
    omega
  exact ⟨reg, pathEq, op, active, selected, view, room⟩

/-- The complete public append admits either survivor on an unspecified
abrupt instruction and hands the selected disk to two public reopens. -/
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
  obtain ⟨reg, _, op, active, selected, view, room⟩ := worker.prepared heap runtime io issued fits
  have cell := op.parts.1.symm.trans worker.parts.1
  have mutex := op.parts.2.symm.trans worker.parts.2
  have held : NativeRecoverAt.Held physical root p.lock p.ref image (.updating p.wal) p.issue :=
    ⟨issued.owned, issued.phase, issued.catalog, issued.manifest⟩
  have actual : PublicStop op.cell op.mutex reg.store reg.session (encode change) p.issue stop d := by
    rw [cell, mutex]
    cases cut with
    | lock stopped => exact .lock stopped
    | read stopped => exact .read stopped
    | ready observed site =>
      obtain ⟨rfl, rfl⟩ := WalRecoverySlice.Segmented.Native.Phase.ready.inj (selected.symm.trans observed)
      exact site
  have pending := recoverPublic op (prim _ _ selected) active held (encode_size change) room linux actual
  have retry := restart.uncertain issued.manifest issued.catalog (view ▸ pending) trace
  exact ⟨retry, retry.readTwice reopens a b rootLife⟩

/-- The mutex, read and poison before the worker can only write back the
existing files. These observations need only the volatile primitive laws. -/
theorem Worker.beforeReopens {p : Prefix path root start} (worker : Worker p)
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (prior : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (fits : image.view.tail + 1 < UInt64.size)
    (volatile : VolatileIO (fun w => (physical w).disk) stop)
    (restart : NativeAppendCut.Restarted physical root image.tables p.issue d mode after)
    (original : Reopens physical heap path root image life none)
    (a b : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    ∃ store session, worker.phase = .ready store session ∧
      (BeforeWorker worker.cell worker.mutex store p.issue stop d →
        Retry physical root (NativeMutationScope.uncertainEvents before change) image none after ∧
        PendingReadScope.TwoReads none physical path root image life (NativeMutationScope.uncertainEvents before change)
          after a b rootLife) := by
  obtain ⟨trace, _, reached, _⟩ := p.issued entry files heap (runtime _ _) prior change scans fits
  obtain ⟨reg, slot, _, installed, view⟩ := reached.child
  have registered := ((runtime _ _).cleanup.cached _ reached.owned _ reg).mp slot
  have selected := (heap.read (heap.lock worker.mutex (worker.parts.1 ▸ registered.2.1))).1
  refine ⟨reg.store, reg.session, selected, ?_⟩
  intro cut
  have known := (cut.writes volatile).recoverable (installed.installed.offline (request := none) (.inl view))
  have retry := Retry.rejected (change := change) trace (restart.filesAt reached.manifest reached.catalog known)
  exact ⟨retry, retry.readTwice original a b rootLife⟩

/-- Once the actual worker succeeded, interrupting phase publication or
mutex release retains its durable extension. The first and second reopen
are pinned to the same extended view even if no reply was delivered. -/
theorem Worker.afterSuccessReopens {p : Prefix path root start} (worker : Worker p)
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (prior : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (fits : image.view.tail + 1 < UInt64.size)
    (io : AppendPrimitives runtime change)
    (linux : System.Platform.isWindows = false)
    (volatile : VolatileIO (fun w => (physical w).disk) stop)
    (restart : NativeAppendCut.Restarted physical root image.tables p.issue d mode after)
    (extended : Reopens physical heap path root (image.append (encode change)) life none)
    (a b : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    ∃ store session, worker.phase = .ready store session ∧
      (AfterSuccess worker.cell worker.mutex store session (encode change) p.issue stop d →
        Retry physical root (NativeMutationScope.uncertainEvents before change) (image.append (encode change)) none after ∧
        PendingReadScope.TwoReads none physical path root (image.append (encode change)) life
          (NativeMutationScope.uncertainEvents before change) after a b rootLife) := by
  obtain ⟨trace, history, issued, _⟩ := p.issued entry files heap (runtime _ _) prior change scans fits
  obtain ⟨reg, _, op, active, selected, view, room⟩ := worker.prepared heap runtime io issued fits
  have cell := op.parts.1.symm.trans worker.parts.1
  have mutex := op.parts.2.symm.trans worker.parts.2
  have held : NativeRecoverAt.Held physical root p.lock p.ref image (.updating p.wal) p.issue :=
    ⟨issued.owned, issued.phase, issued.catalog, issued.manifest⟩
  refine ⟨reg.store, reg.session, selected, ?_⟩
  intro cut
  have known := recoverAfterSuccess op volatile active held (encode_size change) room linux
    (by rw [cell, mutex]; exact cut)
  have saved : NativeReadScope.Files physical root (image.append (encode change)) after :=
    restart.filesAt (image := image.append (encode change)) issued.manifest issued.catalog
      (by simpa only [view, Selected.append] using known)
  have retry := (Retry.written trace saved).2
  exact ⟨retry, retry.readTwice extended a b rootLife⟩

end ExperimentalL0.InterruptedMutation
