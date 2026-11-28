import Alvoki.Experiments.L0.NativeMutationReopens
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRuntime

namespace ExperimentalL0.NativeMutationScope
open NativeRead (Footprint SessionAt)
open NativeScope (W)
open WalRecoverySlice.Segmented.Native (PhaseMemory Registration)
open WalRecoverySlice.Segmented.Native.AppendIO (Active LocalIO)

/-- Append effects and L0 reference frames use the same child memory. On
success the frame is indexed by the registration installed by this call. -/
structure MutationIO {disk : W → WalRecoverySlice.Segmented.Model.Disk}
    (mem : WalRecoverySlice.Segmented.Native.ChildMemory disk) (heap : PhaseMemory)
    (Q : W → Prop) (ref : NativeScope.Ref) (wal : NativeScope.Wal) (reg : Registration)
    (session : Session) (change : Change) (issued : W) where
  worker : LocalIO mem heap Q wal reg (encode change) issued
  publication : ∀ pos t, WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .ok pos t →
    ∀ next, heap.Registered wal next t →
      NativeWriteRelease.PublishFrames mem ref wal next t {session with mem := insert session.mem change}

/-- Primitive append operations for the very store, active child memory and
registration obtained from the opener at the issued callback. -/
def AppendPrimitives {physical : W → Footprint inode} {heap : PhaseMemory}
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap) (change : Change) :=
  ∀ lock ref wal session history issued (reg : Registration)
    (path : reg.store.root = (runtime lock ref).wal.acquire.canonical),
    SessionAt physical root lock ref wal session image history issued (.updating wal) →
    (physical issued).readyWal wal = some reg →
    let mem := ((runtime lock ref).wal.worker reg.store path).children.memory
    Active mem heap wal reg issued →
    MutationIO mem heap (NativeRecoverAt.Held physical root lock ref image (.updating wal)) ref wal reg session change issued

theorem withOpen {physical : W → Footprint inode}
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.RestartFiles none physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (release : ∀ lock ref img req, NativeWriteRelease.Laws heap req physical root lock ref img)
    (run : Execution.Run before none image) (change : Change)
    (scans : ∀ lock ref wal session history u, SessionAt physical root lock ref wal session image history u (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables u)
    (io : AppendPrimitives runtime change) (linux : System.Platform.isWindows = false) :
    NativeScope.Post (Native.withOpen path (fun h => Native.mutation h change)) start
      (fun _ => Written physical heap root (before ++ [.reopened]) image change)
      (Failure physical heap root before image change) := by
  apply withOpen_of_append entry files heap runtime release run change scans
  intro lock ref wal session history issued entered fits
  obtain ⟨reg, slot, origin, installed, view⟩ := entered.child
  let ops := runtime lock ref
  obtain ⟨pathEq, hist, shape, layout, auth, live⟩ :=
    NativeRecoverAt.ChildCache.authority (ops := ops.wal) ops.childCache entered.owned slot origin installed
  let mem := (ops.wal.worker reg.store pathEq).children.memory
  have disk := installed.installed
  obtain ⟨_, _, _, lc, dc⟩ := disk
  have active : Active mem heap wal reg issued := by
    refine ⟨origin.2.1, (ops.cleanup.cached _ entered.owned _ reg).mp slot, auth, _, live,
      hist, shape, layout, lc, dc, ?_⟩
    rw [layout.active.position]
  have room : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
    rw [view]
    change image.view.tail + 1 < 18446744073709551616 at fits
    change image.view.tail < 18446744073709551615
    omega
  let input := io lock ref wal session history issued reg pathEq entered slot active
  have result := input.worker.append active
    ⟨entered.owned, entered.phase, entered.catalog, entered.manifest⟩ (encode_size change) room linux
  unfold Alvoki.NativePost.IOReturns at *
  cases actual : WalRecoverySlice.Segmented.Native.append wal (encode change) issued with
  | error e t =>
    rw [actual] at result
    obtain ⟨held, pending, slot', custody⟩ := result
    exact ⟨.ofRecover held (view ▸ pending), reg.store, slot', custody⟩
  | ok pos t =>
    rw [actual] at result
    obtain ⟨next, _, _, nextActive, held, step, _, posEq⟩ := result
    have observed : next.session.view = reg.session.view.append (encode change) := by
      cases step with
      | ack chosen => simpa [WalRecoverySlice.Segmented.Contract.Request.apply, room] using chosen.symm
    exact ⟨view ▸ posEq, ⟨held.owned, held.phaseEq, held.catalog, held.manifest⟩,
      next, mem, nextActive, view ▸ observed, input.publication pos t actual next nextActive.2.1⟩

theorem mutationThenReadTwice {physical : W → Footprint inode}
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.RestartFiles none physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (release : ∀ lock ref img req, NativeWriteRelease.Laws heap req physical root lock ref img)
    (run : Execution.Run before none image) (change : Change)
    (scans : ∀ lock ref wal session history u, SessionAt physical root lock ref wal session image history u (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables u)
    (io : AppendPrimitives runtime change) (linux : System.Platform.isWindows = false)
    (original : Reopens physical heap path root image life none)
    (uncertain : Reopens physical heap path root image life (some (.append (encode change))))
    (extended : Reopens physical heap path root (image.append (encode change)) life none)
    (a b : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    MutationReopens physical heap path root before image change start life a b rootLife :=
  withOpen_twice (withOpen entry files heap runtime release run change scans io linux)
    original uncertain extended a b rootLife

end ExperimentalL0.NativeMutationScope
