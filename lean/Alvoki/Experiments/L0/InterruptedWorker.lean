import Alvoki.Experiments.L0.InterruptedMutation
import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.WAL.Segmented.Proofs.CutRuntime

namespace ExperimentalL0.InterruptedMutation

open System Lifecycle NativeScope
open NativeRead (Footprint SessionAt)
open WalRecoverySlice.Segmented.Native (PhaseMemory Store Registration)
open NativeMutationScope (AppendPrimitives Retry Reopens)
open WalRecoverySlice.Segmented.Native.AppendCut (CutRuntime sites recoverBody)
open WalRecoverySlice.Segmented.Native.AppendIO (LocalIO Active issuedWorld)

/-- The actual outer WAL phase read under its mutex identifies the worker;
the active child identity and its files will come from the successful open. -/
structure Worker (p : Prefix path root start) where
  cell : IO.Ref (WalRecoverySlice.Segmented.Native.Phase Store)
  mutex : Std.BaseMutex
  store : Store
  session : WalRecoverySlice.Segmented.Session
  parts : p.wal.Parts cell mutex
  read : ((cell.get : BaseIO _) (mutex.lock p.issue).state).val = .ready store session

def Worker.begin (worker : Worker p) : W :=
  issuedWorld worker.cell worker.mutex worker.store p.issue

/-- A nonreturning instruction inside the shared append schedule. The
same root, recovered handle, store, active child, batch and issued worlds
are used to obtain a permitted disk at the physical reboot. Both reads
start their actual reopen from the immediately preceding reached world. -/
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
    (prim : CutRuntime (fun w => (physical w).disk) worker.store worker.session stop)
    (cut : ((sites worker.store worker.session stop).appendSession worker.session (encode change)).cuts
      worker.begin d)
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
  have got := (heap.read (heap.lock worker.mutex (worker.parts.1 ▸ registered.2.1))).1
  obtain ⟨store, session⟩ := WalRecoverySlice.Segmented.Native.Phase.ready.inj (got.symm.trans worker.read)
  have world : issuedWorld op.cell op.mutex reg.store p.issue = worker.begin := by
    unfold Worker.begin
    rw [op.parts.1.symm.trans worker.parts.1, op.parts.2.symm.trans worker.parts.2, store]
  have room : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
    rw [view]
    change image.view.tail + 1 < 18446744073709551616 at fits
    change image.view.tail < 18446744073709551615
    omega
  have recoverable := recoverBody op (by simpa only [store, session] using prim) active
    ⟨issued.owned, issued.phase, issued.catalog, issued.manifest⟩ (encode_size change) room linux
    (by rw [world, store, session]; exact cut)
  have retry := restart.uncertain issued.manifest issued.catalog (view ▸ recoverable) trace
  exact ⟨retry, retry.readTwice reopens a b rootLife⟩

end ExperimentalL0.InterruptedMutation
