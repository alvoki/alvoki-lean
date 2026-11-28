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

theorem atIssue {physical : W → Footprint inode}
    (ops : WithOpenReads.Runtime physical root lock ref image life heap)
    (entered : SessionAt physical root lock ref wal session image history issued stage) :
    ∃ reg : Registration, ∃ path : reg.store.root = ops.wal.acquire.canonical,
      (physical issued).readyWal wal = some reg ∧ reg.session.view = image.view ∧
      Active (ops.wal.worker reg.store path).children.memory heap wal reg issued := by
  obtain ⟨reg, slot, origin, installed, view⟩ := entered.child
  obtain ⟨pathEq, hist, shape, layout, auth, live⟩ :=
    NativeRecoverAt.ChildCache.authority (ops := ops.wal) ops.childCache entered.owned slot origin installed
  let mem := (ops.wal.worker reg.store pathEq).children.memory
  have disk := installed.installed
  obtain ⟨_, _, _, lc, dc⟩ := disk
  have active : Active mem heap wal reg issued := by
    refine ⟨origin.2.1, (ops.cleanup.cached _ entered.owned _ reg).mp slot, auth, _, live,
      hist, shape, layout, lc, dc, ?_⟩
    rw [layout.active.position]
  exact ⟨reg, pathEq, slot, view, active⟩

theorem appendAt {physical : W → Footprint inode}
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (io : AppendPrimitives runtime change)
    (entered : SessionAt physical root lock ref wal session image history issued (.updating wal))
    (fits : image.view.tail + 1 < UInt64.size) (linux : System.Platform.isWindows = false) :
    Alvoki.NativePost.IOReturns (WalRecoverySlice.Segmented.Native.append wal (encode change)) issued
      (fun pos t => pos = image.view.tail + 1 ∧
        NativeRecoverAt.Held physical root lock ref (image.append (encode change)) (.updating wal) t ∧
        ∃ (reg : Registration) (mem : WalRecoverySlice.Segmented.Native.ChildMemory (fun w => (physical w).disk)),
          Active mem heap wal reg t ∧ reg.session.view = image.view.append (encode change) ∧
          NativeWriteRelease.PublishFrames mem ref wal reg t {session with mem := insert session.mem change})
      (fun t => NativeRecoverAt.Held physical root lock ref image (.updating wal) t ∧
        WalRecoverySlice.Segmented.Recoverable image.view (some (.append (encode change))) (physical t).disk ∧
        ∃ store slot, NativeWriteRelease.WalCustody heap wal store slot t) := by
  obtain ⟨reg, pathEq, slot, view, active⟩ := atIssue (runtime lock ref) entered
  let mem := ((runtime lock ref).wal.worker reg.store pathEq).children.memory
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
    exact ⟨held, view ▸ pending, reg.store, slot', custody⟩
  | ok pos t =>
    rw [actual] at result
    obtain ⟨next, _, _, nextActive, held, step, _, posEq⟩ := result
    have observed : next.session.view = reg.session.view.append (encode change) := by
      cases step with
      | ack chosen => simpa [WalRecoverySlice.Segmented.Contract.Request.apply, room] using chosen.symm
    exact ⟨view ▸ posEq, ⟨held.owned, held.phaseEq, held.catalog, held.manifest⟩,
      next, mem, nextActive, view ▸ observed, input.publication pos t actual next nextActive.2.1⟩

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
  have result := appendAt runtime io entered fits linux
  unfold Alvoki.NativePost.IOReturns at *
  cases actual : WalRecoverySlice.Segmented.Native.append wal (encode change) issued <;> rw [actual] at result
  case ok => exact result
  case error => exact ⟨.ofRecover result.1 result.2.1, result.2.2⟩

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
