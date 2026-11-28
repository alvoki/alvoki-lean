import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.L0.HealthyReads

namespace ExperimentalL0.HealthyMutation
open NativeScope (W Wal Ref)
open NativeRead (Footprint SessionAt Online)
open WalRecoverySlice.Segmented
open WalRecoverySlice.Segmented.Native (PhaseMemory Registration ChildMemory)
open WalRecoverySlice.Segmented.Native.AppendIO (Active healthyReports)
open NativeMutationScope (AppendPrimitives)

/-- Primitive report choices only for the append selected under the recovered
registration. This includes both append-in-place and segment rotation. -/
def Healthy {physical : W → Footprint inode}
    {runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap}
    (io : AppendPrimitives runtime change) (lock : IO.FS.Handle) (ref : Ref) : Prop :=
  ∀ wal session history issued reg path entered slot active,
    ∃ directory removal, (io lock ref wal session history issued reg path entered slot active).worker.reports =
      healthyReports (encode change) directory removal ∧ Model.HealthyRoot removal

/-- A positive public callback using the precise world produced by publication.
It returns the registered append authority in the published world. -/
theorem mutation {physical : W → Footprint inode}
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (online : Online physical root lock ref wal session image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (scans : ∀ w, SessionAt physical root lock ref wal session image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w)
    (change : Change) (fits : image.view.tail + 1 < UInt64.size)
    (io : AppendPrimitives runtime change) (healthy : Healthy io lock ref)
    (linux : System.Platform.isWindows = false) :
    ∃ (issued appended u : W) (reg : Registration) (mem : ChildMemory (fun w => (physical w).disk)),
      WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .ok (image.view.tail + 1) appended ∧
      Native.mutation handle change start = .ok () u ∧
      NativeWrite.afterWrite ref (.ok {session with mem := insert session.mem change} appended) = .ok () u ∧
      Active mem heap wal reg appended ∧ reg.session.view = image.view.append (encode change) ∧ Active mem heap wal reg u ∧
      NativeWriteRelease.Held none physical root lock ref (image.append (encode change))
        (.online wal {session with mem := insert session.mem change}) u := by
  let ops := runtime lock ref
  have dispatch := NativeWrite.dispatch online binding heap ops.cleanup.cached ops.phase scans change
  simp only [fits, ↓reduceIte] at dispatch
  obtain ⟨issued, entered, ran⟩ := dispatch
  obtain ⟨reg, path, slot, view, active⟩ := NativeMutationScope.atIssue ops entered
  have room : reg.session.view.tail < Contract.maxPosition := by
    rw [view]
    change image.view.tail + 1 < 18446744073709551616 at fits
    change image.view.tail < 18446744073709551615
    omega
  let input := io lock ref wal session history issued reg path entered slot active
  obtain ⟨dir, removal, reports, removes⟩ := healthy wal session history issued reg path entered slot active
  obtain ⟨pos,t,returned,_⟩ :=
    input.worker.healthy active ⟨entered.owned, entered.phase, entered.catalog, entered.manifest⟩
      (encode_size change) room linux reports removes
  have safety := NativeMutationScope.appendAt runtime io entered fits linux
  rw [Alvoki.NativePost.IOReturns,returned] at safety
  obtain ⟨posEq,updated,next,mem,nextActive,observed,frames⟩ := safety
  have publishedPhase : NativeRecoverAt.PhasePrimitives physical root lock ref (image.append (encode change)) :=
    ⟨ops.phase.read, ops.phase.swap⟩
  have facts := nextActive
  obtain ⟨_, _, _, _, _, model⟩ := facts
  obtain ⟨u, published, atEnd, reusable⟩ := NativeWriteRelease.afterSuccess publishedPhase ops.cleanup.cached
    updated (model.installed.offline (request := none) (.inl observed)) nextActive _ frames
  rw [returned] at ran
  exact ⟨issued,t,u,next,_,posEq ▸ returned,ran.trans published,published,nextActive,observed,reusable,atEnd⟩

/-- The final root unlock receives the world returned by the real child
close. Its report, including an error after successful publication, is
the result of cleanup. -/
theorem release {physical : W → Footprint inode}
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (online : NativeWriteRelease.Held none physical root lock ref image (.online wal session) w)
    (ready : heap.Registered wal reg w)
    (healthy : ∀ t, (ref.swap .offline : BaseIO _) w = ⟨.online wal session,t⟩ →
      heap.Registered wal reg t → HealthyRootAcquisition.Unlocks wal reg t) :
    ∃ detached endWal, (ref.swap .offline : BaseIO _) w = ⟨.online wal session, detached⟩ ∧
      heap.Registered wal reg detached ∧ WalRecoverySlice.Segmented.Native.close wal detached = .ok () endWal ∧
      Lifecycle.finish (ε := IO.Error) ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close)
        lock.unlock w = lock.unlock endWal := by
  let taken := (ref.swap .offline : BaseIO _) w
  obtain ⟨old, frame⟩ := phase.refSwap wal w online.owned .offline
  have value : taken.val = .online wal session := old.trans online.phase
  have eq : taken = ⟨.online wal session,taken.state⟩ := by rw [← value]
  have off := online.advance frame
  have registered := (cached _ off.owned wal reg).mp (frame.child.trans ((cached _ online.owned wal reg).mpr ready))
  obtain ⟨endWal, closed⟩ := HealthyRootAcquisition.walClose registered (healthy _ eq registered)
  refine ⟨_,_,eq,registered,closed,?_⟩
  have child : (Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close w = .ok () endWal := by
    rw [NativeScope.close_run]
    change (match taken.val.wal with | none => _ | some _ => _) = _
    rw [value]
    exact closed
  rw [Lifecycle.finish_io]
  cases result : lock.unlock endWal <;> simp [EIO.toBaseIO, child, result]

/-- Reports for primitive cleanup operations, indexed by the reached
registration and the world returned by the actual WAL close. -/
structure Cleanup (physical : W → Footprint inode) (heap : PhaseMemory)
    (root : System.FilePath) (lock : IO.FS.Handle) (ref : Ref) (image : Selected)
    (report : Option IO.Error) : Prop where
  child : ∀ wal reg session w detached, NativeWriteRelease.Held none physical root lock ref image (.online wal session) w →
    (ref.swap .offline : BaseIO _) w = ⟨.online wal session, detached⟩ →
    heap.Registered wal reg detached → HealthyRootAcquisition.Unlocks wal reg detached
  rootUnlock : ∀ wal reg session w detached endWal, NativeWriteRelease.Held none physical root lock ref image (.online wal session) w →
    (ref.swap .offline : BaseIO _) w = ⟨.online wal session, detached⟩ →
    heap.Registered wal reg detached → WalRecoverySlice.Segmented.Native.close wal detached = .ok () endWal →
    NativeScope.Post lock.unlock endWal (fun _ _ => report = none) (fun e _ => report = some e)

theorem callback {physical : W → Footprint inode}
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (online : Online physical root lock ref wal session image history start) (grant : NativeReadScope.Grant root lock ref)
    (binding : Native.Handle.AtRoot handle root ref) (trace : Execution.Run events (some session) image)
    (scans : ∀ w, SessionAt physical root lock ref wal session image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w)
    (change : Change) (fits : image.view.tail + 1 < UInt64.size)
    (io : AppendPrimitives runtime change) (healthy : Healthy io lock ref)
    (linux : System.Platform.isWindows = false)
    (laws : NativeWriteRelease.Laws heap none physical root lock ref (image.append (encode change)))
    (cleanup : Cleanup physical heap root lock ref (image.append (encode change)) report) :
    NativeScope.Callback ref lock (Native.mutation handle change) start
      (fun _ t => report = none ∧ NativeMutationScope.Written physical heap root events image change t)
      (fun e t => report = some e ∧ NativeMutationScope.Written physical heap root events image change t) := by
  obtain ⟨issued, appended, u, reg, mem, sent, body, published, active, view, reusable, reached⟩ :=
    mutation runtime online binding scans change fits io healthy linux
  let ops := runtime lock ref
  have phase : NativeRecoverAt.PhasePrimitives physical root lock ref (image.append (encode change)) := ⟨ops.phase.read, ops.phase.swap⟩
  have stopped t (closed : NativeReadRelease.Closed physical root lock ref (image.append (encode change)) t) :
      NativeMutationScope.Written physical heap root events image change t := by
    obtain ⟨delivered, lost⟩ := NativeMutationScope.Retry.written trace closed.files
    exact ⟨delivered,lost,lock,ref,wal,reg,issued,appended,u,_,handle,start,mem,sent,active,view,binding,body,
      published,reached.phase,reusable,closed⟩
  have safe := NativeWriteRelease.outerAttached laws grant phase reached reusable.custody stopped (fun _ => stopped)
  obtain ⟨detached,endWal,took,ready,closed,_⟩ := release phase ops.cleanup.cached reached reusable.2.1 (cleanup.child _ _ _ _ · reached)
  have observed := cleanup.rootUnlock _ _ _ _ _ _ reached took ready closed
  unfold NativeScope.Callback NativeScope.Post
  rw [body]
  unfold NativeScope.Release at safe ⊢
  simp only [took,Lifecycle.Phase.wal,NativeScope.Post,closed] at safe ⊢
  unfold NativeScope.Post at observed
  cases result : lock.unlock endWal <;> rw [result] at observed safe <;> exact ⟨observed,safe⟩

/-- Starting at an initialized empty root, actual acquisition and recovery
produce the public callback. A healthy last unlock delivers success; a
specified last-unlock error returns that error with the same committed append
and both restart traces. -/
theorem withOpen {physical : W → Footprint inode} {Q : W → Prop}
    {mem : ChildMemory (fun w => (physical w).disk)}
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ l r, WithOpenReads.Runtime physical root l r image life heap)
    (prior : Execution.Run before none image)
    (p : HealthyReads.Entry path root start) (manifest : HealthyReads.Manifest root p.fresh.state t)
    (opening : (p.fresh.val.get : IO (Lifecycle.Phase Wal)) t = .ok .opening u)
    (grant : HealthyReads.WalRoot (root / "wal") u)
    (worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore (root / "wal") u = .ok s (HealthyReads.storeEntry grant) →
      s.root = grant.canonical → s.directory = grant.directory → s.lock = grant.lock →
      WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s (fun w => (physical w).disk) Q mem (HealthyReads.storeEntry grant))
    (carry : ∀ wal v reg, WalRecoverySlice.Segmented.Native.Origin (root / "wal") wal reg u v →
      heap.Registered wal reg v → heap.Registered wal reg (HealthyReads.attached p.fresh.val wal v))
    (change : Change) (fits : image.view.tail + 1 < UInt64.size)
    (scans : ∀ wal history w, SessionAt physical root p.lock p.fresh.val wal HealthyReads.empty image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w)
    (io : AppendPrimitives runtime change) (healthy : Healthy io p.lock p.fresh.val)
    (linux : System.Platform.isWindows = false)
    (laws : NativeWriteRelease.Laws heap none physical root p.lock p.fresh.val (image.append (encode change)))
    (cleanup : Cleanup physical heap root p.lock p.fresh.val (image.append (encode change)) report) :
    ∃ stop, Native.withOpen path (fun handle => Native.mutation handle change) start =
        (match report with | none => .ok () stop | some e => .error e stop) ∧
      NativeMutationScope.Written physical heap root (before ++ [.reopened]) image change stop := by
  obtain ⟨h, binding, outer⟩ := p.reached (fun handle => Native.mutation handle change)
  obtain ⟨wal,v,reg,opened,sessionEq,origin,registered,_⟩ := grant.open heap worker
  have recovered := HealthyReads.recover manifest p.fresh.val heap opening opened
    (sessionEq ▸ (carry wal v reg origin registered).ready)
  obtain ⟨atRoot,bytes⟩ := HealthyReads.Entry.openingWorld entry files p
  let ops := runtime p.lock p.fresh.val
  have ready hist (d : Durable image hist) := by
    have r := NativeRecoverAt.recoverAt_checks d atRoot bytes (ops.manifest _ atRoot) heap ops.cleanup.cached
      ops.wal.toOpenIO ops.childCache ops.phase ops.scan (fun wal w a => ops.tables wal w a.1.owned)
    rw [NativeScope.Post,recovered] at r
    exact r.1
  have reopened := prior.reopened (fun hist d => (ready hist d).1)
  obtain ⟨state, _, represented⟩ := prior.refines
  obtain ⟨hist, durable⟩ : ∃ hist, Nonempty (Durable image hist) := by
    cases state with
    | ready db => obtain ⟨_,_,impossible,_⟩ := represented; cases impossible
    | offline known pending => obtain ⟨_,hist,_,d⟩ := represented; exact ⟨_,d⟩
  obtain ⟨d⟩ := durable
  obtain ⟨installed,child,attached⟩ := ready hist d
  have finished : NativeScope.Post (Native.withOpen path (fun handle => Native.mutation handle change)) start
      (fun _ t => report = none ∧ NativeMutationScope.Written physical heap root (before ++ [.reopened]) image change t)
      (fun e t => report = some e ∧ NativeMutationScope.Written physical heap root (before ++ [.reopened]) image change t) := by
    unfold NativeScope.Post
    rw [outer]
    apply NativeScope.withSession_rule
    rw [NativeScope.Post,recovered]
    apply NativeRead.publishOnline (attached.sessionAt installed) (ops.phase.refRead child) (ops.phase.refSwap child)
    intro entered online
    exact callback runtime online ⟨_,_,_,p.openLock,p.exclusive,rfl⟩ binding reopened (scans child hist) change fits
      io healthy linux laws cleanup
  unfold NativeScope.Post at finished
  cases actual : Native.withOpen path (fun handle => Native.mutation handle change) start with
  | ok x stop =>
    rw [actual] at finished
    exact ⟨stop, by rw [finished.1], finished.2⟩
  | error e stop =>
    rw [actual] at finished
    exact ⟨stop, by rw [finished.1], finished.2⟩

end ExperimentalL0.HealthyMutation
