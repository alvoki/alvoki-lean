import Alvoki.Experiments.L0.NativeWriteRelease
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendIngress
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


open NativeReadScope (Grant)
open NativeReadRelease (Closed)
open WalRecoverySlice.Segmented.Native (PhaseMemory ChildMemory Registration)
open WalRecoverySlice.Segmented.Native.AppendIO (Active)

/-- The client can lose the acknowledgement after the native append and
phase publication completed. Both observations describe the same disk. -/
structure Written (physical : W → Footprint inode) (heap : PhaseMemory) (root : System.FilePath)
    (events : List Event) (image : Selected) (change : Change) (w : W) : Prop where
  delivered : Retry physical root ((events ++ [.written change]) ++ [.stop]) (image.append (encode change)) none w
  lost : Retry physical root ((events ++ [.writeUncertain change]) ++ [.stop]) (image.append (encode change)) none w
  storage : ∃ lock ref wal reg issued appended published session handle entered, ∃ mem : ChildMemory (fun t => (physical t).disk),
    WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .ok (image.view.tail + 1) appended ∧
    Active mem heap wal reg appended ∧ reg.session.view = image.view.append (encode change) ∧
    Native.Handle.AtRoot handle root ref ∧ Native.mutation handle change entered = .ok () published ∧
    NativeWrite.afterWrite ref (.ok session appended) = .ok () published ∧
    (physical published).phase = .online wal session ∧ Active mem heap wal reg published ∧
    Closed physical root lock ref (image.append (encode change)) w

inductive Failure (physical : W → Footprint inode) (heap : PhaseMemory) (root : System.FilePath)
    (before : List Event) (image : Selected) (change : Change) (e : IO.Error) (w : W) : Prop where
  | unopened : Retry physical root (before ++ [.openFailed]) image none w →
      Failure physical heap root before image change e w
  | rejected : ¬ image.view.tail + 1 < UInt64.size →
      Closed physical root lock ref image w →
      Retry physical root (((before ++ [.reopened]) ++ [.writeUncertain change]) ++ [.stop]) image none w →
      Failure physical heap root before image change e w
  | reported : WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .error e appended →
      Closed physical root lock ref image w (some (.append (encode change))) →
      Retry physical root (((before ++ [.reopened]) ++ [.writeUncertain change]) ++ [.stop]) image
        (some (.append (encode change))) w → Failure physical heap root before image change e w
  | cleanup : Written physical heap root (before ++ [.reopened]) image change w →
      Failure physical heap root before image change e w

private theorem failedBody {physical : W → Footprint inode}
    (grant : Grant root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (laws : NativeWriteRelease.Laws heap pending physical root lock ref image)
    (held : NativeWriteRelease.Held pending physical root lock ref image (.updating wal) t)
    (owned : NativeWriteRelease.WalCustody heap wal store slot t)
    (error : IO.Error)
    (ran : Native.mutation handle change entered = NativeWrite.afterWrite ref (.error error t))
    (finish : ∀ u, Closed physical root lock ref image u pending → err error u) :
    NativeScope.Callback ref lock (Native.mutation handle change) entered ok err := by
  obtain ⟨_, result, out⟩ := NativeWriteRelease.afterError laws grant phase held owned error
  unfold NativeScope.Callback NativeScope.Post
  rw [ran, result]
  exact NativeWriteRelease.outerOffline wal laws.toRootUnlock grant phase out finish (fun _ => finish)

private theorem successfulBody {physical : W → Footprint inode}
    {mem : ChildMemory (fun t => (physical t).disk)} {reg : Registration}
    (binding : Native.Handle.AtRoot handle root ref) (grant : Grant root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref (image.append (encode change)))
    (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (laws : NativeWriteRelease.Laws heap none physical root lock ref (image.append (encode change)))
    (run : Execution.Run (before ++ [.reopened]) (some session) image)
    (held : NativeRecoverAt.Held physical root lock ref (image.append (encode change)) (.updating wal) appended)
    (active : Active mem heap wal reg appended) (view : reg.session.view = image.view.append (encode change))
    (frames : NativeWriteRelease.PublishFrames mem ref wal reg appended {session with mem := insert session.mem change})
    (report : WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .ok (image.view.tail + 1) appended)
    (ran : Native.mutation handle change entered =
      NativeWrite.afterWrite ref (.ok {session with mem := insert session.mem change} appended)) :
    NativeScope.Callback ref lock (Native.mutation handle change) entered
      (fun _ => Written physical heap root (before ++ [.reopened]) image change)
      (Failure physical heap root before image change) := by
  have facts := active
  obtain ⟨_, ready, _, _, _, model⟩ := facts
  have disk := model.installed.offline (request := none) (.inl view)
  obtain ⟨u, published, online, reusable⟩ := NativeWriteRelease.afterSuccess phase cached held disk active _ frames
  unfold NativeScope.Callback NativeScope.Post
  rw [ran, published]
  have stopped t (closed : Closed physical root lock ref (image.append (encode change)) t) :
      Written physical heap root (before ++ [.reopened]) image change t := by
    obtain ⟨sent, lost⟩ := Retry.written run closed.files
    exact ⟨sent, lost, lock, ref, wal, reg, issued, appended, u, _, handle, entered, mem, report, active, view, binding, ran.trans published, published, online.phase, reusable, closed⟩
  exact NativeWriteRelease.outerAttached laws grant phase online reusable.custody stopped (fun _ t c => .cleanup (stopped t c))

open NativeRead (SessionAt Online)
open WalRecoverySlice.Segmented.Native (Store)
open Alvoki.NativePost (IOReturns)

private theorem SessionAtHeld {physical : W → Footprint inode}
    (atStage : SessionAt physical root lock ref wal s image history w stage) :
    NativeRecoverAt.Held physical root lock ref image stage w :=
  ⟨atStage.owned, atStage.phase, atStage.catalog, atStage.manifest⟩

/-- The public client of the segmented WAL postcondition. The guarded
branch consumes the pre-append registration. The admitted branch consumes
the handle, slot and disk produced by the concrete append on this world. -/
theorem withOpen_of_append {physical : W → Footprint inode}
    (entry : NativeReadScope.Entry physical path root image) (files : RestartFiles none physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (release : ∀ lock ref img req, NativeWriteRelease.Laws heap req physical root lock ref img)
    (run : Execution.Run before none image) (change : Change)
    (scans : ∀ lock ref wal session history u, SessionAt physical root lock ref wal session image history u (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables u)
    (append : ∀ lock ref wal session history issued,
      SessionAt physical root lock ref wal session image history issued (.updating wal) →
      image.view.tail + 1 < UInt64.size →
      IOReturns (WalRecoverySlice.Segmented.Native.append wal (encode change)) issued
        (fun pos t => pos = image.view.tail + 1 ∧
          NativeRecoverAt.Held physical root lock ref (image.append (encode change)) (.updating wal) t ∧
          ∃ (reg : Registration) (mem : ChildMemory (fun w => (physical w).disk)),
            Active mem heap wal reg t ∧ reg.session.view = image.view.append (encode change) ∧
            NativeWriteRelease.PublishFrames mem ref wal reg t {session with mem := insert session.mem change})
        (fun t => NativeWriteRelease.Held (some (.append (encode change))) physical root lock ref image (.updating wal) t ∧
          ∃ store slot, NativeWriteRelease.WalCustody heap wal store slot t)) :
    NativeScope.Post (Native.withOpen path (fun h => Native.mutation h change)) start
      (fun _ => Written physical heap root (before ++ [.reopened]) image change)
      (Failure physical heap root before image change) := by
  apply WithOpenReads.withRecovered entry files heap runtime run
  · exact fun _ _ files trace => .unopened (.known trace files)
  · exact fun _ _ _ _ _ _ closed _ _ trace => .unopened (.known trace closed.files)
  intro lock ref wal session history handle opening recovered grant _ _ binding installed attached trace
  let ops := runtime lock ref
  apply NativeRead.publishOnline (attached.sessionAt installed) (ops.phase.refRead wal) (ops.phase.refSwap wal)
  intro entered online
  have dispatch := NativeWrite.dispatch online binding heap ops.cleanup.cached ops.phase
    (scans lock ref wal session history) change
  by_cases fits : image.view.tail + 1 < UInt64.size
  · simp only [fits, ↓reduceIte] at dispatch
    obtain ⟨issued, atCall, ran⟩ := dispatch
    have leaf := append _ _ _ _ _ _ atCall fits
    unfold IOReturns at leaf
    cases sent : WalRecoverySlice.Segmented.Native.append wal (encode change) issued with
    | ok pos t =>
      rw [sent] at leaf ran
      obtain ⟨rfl, held, reg, mem, active, view, frames⟩ := leaf
      have pubPhase : NativeRecoverAt.PhasePrimitives physical root lock ref (image.append (encode change)) := ⟨ops.phase.read, ops.phase.swap⟩
      exact successfulBody binding grant pubPhase ops.cleanup.cached (release _ _ _ _) trace held active view frames sent ran
    | error e t =>
      rw [sent] at leaf ran
      obtain ⟨held, store, slot, current⟩ := leaf
      exact failedBody grant ops.phase (release _ _ _ _) held current e ran
        (fun _ closed => .reported sent closed (.uncertain trace closed.files))
  · simp only [fits, ↓reduceIte] at dispatch
    obtain ⟨t, rejected, ran⟩ := dispatch
    obtain ⟨reg, slot, source, disk, view⟩ := rejected.child
    have registered := (ops.cleanup.cached _ rejected.owned _ reg).mp slot
    exact failedBody grant ops.phase (release _ _ _ _)
      (.ofRecover (SessionAtHeld rejected) (disk.installed.offline (.inl view)))
      (.ofRegistered registered source.2) _ ran
      (fun _ closed => .rejected fits closed (.rejected trace closed.files))


/-- All observations use the same public reopen implementation. The
request determines whether the first reopen must keep a known view or
resolve a pending mutation. -/
structure Reopens (physical : W → Footprint inode) (heap : PhaseMemory) (path root : System.FilePath)
    (image : Selected) (life : NativeRead.Lifetime) (req : Option WalRecoverySlice.Segmented.Contract.Request) where
  entry : NativeReadScope.RestartEntry req physical path root image
  runtime : ∀ lock ref, PendingReadScope.Runtime req physical root lock ref image life heap
  pinned : ∀ v, PermittedView image.view req v →
    NativeReadScope.Entry physical path root (PendingReadScope.choose image v)
  pinnedRuntime : ∀ v, PermittedView image.view req v → ∀ lock ref,
    WithOpenReads.Runtime physical root lock ref (PendingReadScope.choose image v) life heap

theorem Retry.readTwice (retry : Retry physical root events image req w)
    (ops : Reopens physical heap path root image life req) (a b : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    PendingReadScope.TwoReads req physical path root image life events w a b rootLife :=
  PendingReadScope.twice ops.entry retry.files heap ops.runtime ops.pinned ops.pinnedRuntime retry.trace a b rootLife

abbrev uncertainEvents (before : List Event) (change : Change) :=
  ((before ++ [.reopened]) ++ [.writeUncertain change]) ++ [.stop]

end ExperimentalL0.NativeMutationScope
