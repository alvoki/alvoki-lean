import Alvoki.Experiments.L0.NativeMutation
import Alvoki.Experiments.L0.InterruptedMutation

namespace ExperimentalL0.MutationSequence
open Lifecycle NativeScope
open NativeRead (Footprint Frame FrameTo)
open NativeRecoverAt (Held Cached PhasePrimitives)
open WalRecoverySlice.Segmented.Native (PhaseMemory Registration ChildMemory ScanFrames scanWorld scanWorld_frame)
open WalRecoverySlice.Segmented.Native.AppendIO (Active nextSession healthyReports)
open NativeWriteRelease (KeepsLive advanceActive)

/-- The same selected child memory follows the public handle across
mutations. The registered handle and segment are updated by append. -/
structure Current (physical : W → Footprint inode) (heap : PhaseMemory)
    (mem : ChildMemory (fun w => (physical w).disk)) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (reg : Registration) (image : Selected) (stage : Phase Wal) (w : W) : Prop where
  held : Held physical root lock ref image stage w
  active : Active mem heap wal reg w
  view : reg.session.view = image.view

variable {physical : W → Footprint inode}
  {mem : ChildMemory (fun w => (physical w).disk)} {heap : PhaseMemory}
  {root : System.FilePath} {lock : IO.FS.Handle} {ref : Ref} {wal : Wal} {reg : Registration}
  {session : Session} {image : Selected}

private theorem Current.advance (cur : Current physical heap mem root lock ref wal reg image stage w)
    (cache : Cached heap physical root lock ref) (frame : FrameTo physical root wal image.tables w t next)
    (kept : KeepsLive mem reg w t) : Current physical heap mem root lock ref wal reg image next t := by
  have held := NativeRecoverAt.Swapped.held frame cur.held
  have before := (cache _ cur.held.owned wal reg).mpr cur.active.2.1
  exact ⟨held, advanceActive cur.active ((cache _ held.owned wal reg).mp (frame.child.trans before)) frame.disk kept, cur.view⟩

/-- Only the actual L0 reference and the three reached scan instructions
need frame the selected child. The WAL append may replace the registration. -/
structure Borrows (physical : W → Footprint inode) (heap : PhaseMemory)
    (mem : ChildMemory (fun w => (physical w).disk)) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (reg : Registration) (image : Selected) (session : Session) : Prop where
  read : ∀ stage w t, Current physical heap mem root lock ref wal reg image stage w →
    (ref.get : IO (Phase Wal)) w = .ok stage t → KeepsLive mem reg w t
  reserve : ∀ w t, Current physical heap mem root lock ref wal reg image (.online wal session) w →
    (ref.swap (.updating wal) : IO _) w = .ok (.online wal session) t → KeepsLive mem reg w t
  scan : ∀ w, Current physical heap mem root lock ref wal reg image (.updating wal) w →
    NativeRecoverAt.ScanPrimitives physical root wal image.tables w ∧
      ∀ (a : WalRecoverySlice.Segmented.Native.AppendIO.ChildAuthority mem
          (WalRecoverySlice.Segmented.Native.segmentPath reg.store.root reg.session.control.active)
          reg.session.control.active reg.session.control.policy reg.child) phase, a.Live w phase → ScanFrames wal w (fun u => a.Live u phase)

private theorem dispatch (cur : Current physical heap mem root lock ref wal reg image (.online wal session) start)
    (bound : Native.Handle.AtRoot h root ref) (cache : Cached heap physical root lock ref)
    (phase : PhasePrimitives physical root lock ref image) (borrows : Borrows physical heap mem root lock ref wal reg image session)
    (change : Change) (fits : image.view.tail + 1 < UInt64.size) :
    let w := NativeWrite.issueWorld ref wal start
    Current physical heap mem root lock ref wal reg image (.updating wal) w ∧
      Native.mutation h change start = NativeWrite.afterWrite ref
        (match WalRecoverySlice.Segmented.Native.append wal (encode change) w with
        | .ok _ t => .ok {session with mem := insert session.mem change} t
        | .error e t => .error e t) := by
  have proof := NativeWrite.dispatchCore (P := Current physical heap mem root lock ref wal reg image)
    cur bound heap phase (fun c => c.held.owned) (fun c => c.held.phaseEq)
    (fun c read step => c.held.phaseEq ▸ c.advance cache step (borrows.read _ _ _ c read))
    (fun c swap step => c.advance cache step (borrows.reserve _ _ c swap))
    (fun c => ⟨reg, c.active.2.1, c.view⟩) (fun c => by
      obtain ⟨frame, child⟩ := borrows.scan _ c
      exact c.held.phaseEq ▸ c.advance cache (scanWorld_frame frame Frame.refl)
        (fun a stage live => scanWorld_frame (child a stage live) live)) change
  simp only [fits, ↓reduceIte] at proof
  intro w
  refine ⟨proof.1, proof.2.trans ?_⟩
  apply congrArg (NativeWrite.afterWrite ref)
  cases WalRecoverySlice.Segmented.Native.append wal (encode change) w <;> rfl

abbrev next (s : Session) (c : Change) : Session := {s with mem := insert s.mem c}

structure StepIO (physical : W → Footprint inode) (heap : PhaseMemory)
    (mem : ChildMemory (fun w => (physical w).disk)) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (reg : Registration) (session : Session) (image : Selected) (change : Change)
    (start : W) where
  borrows : Borrows physical heap mem root lock ref wal reg image session
  append : let w := NativeWrite.issueWorld ref wal start
    Current physical heap mem root lock ref wal reg image (.updating wal) w →
      NativeMutationScope.MutationIO mem heap (Held physical root lock ref image (.updating wal)) ref wal reg session change w

def StepIO.Healthy (op : StepIO physical heap mem root lock ref wal reg session image change start) : Prop :=
  ∀ entry, ∃ directory removal, (op.append entry).worker.reports = healthyReports (encode change) directory removal ∧
    WalRecoverySlice.Segmented.Model.HealthyRoot removal

private theorem walRoom (entered : Current physical heap mem root lock ref wal reg image stage w)
    (fits : image.view.tail + 1 < UInt64.size) : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition := by
  rw [entered.view]
  change image.view.tail + 1 < 18446744073709551616 at fits
  change image.view.tail < 18446744073709551615
  omega

private theorem publish (entered : Current physical heap mem root lock ref wal reg image (.updating wal) w)
    (cache : Cached heap physical root lock ref) (phase : PhasePrimitives physical root lock ref image)
    (input : NativeMutationScope.MutationIO mem heap (Held physical root lock ref image (.updating wal)) ref wal reg session change w)
    (room : reg.session.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition)
    (sent : WalRecoverySlice.Segmented.Native.append wal (encode change) w = .ok pos t)
    (succeeded : WalRecoverySlice.Segmented.Native.AppendIO.Succeeded mem heap
      (Held physical root lock ref image (.updating wal)) wal reg (encode change) pos t) :
    ∃ u, NativeWrite.afterWrite ref (.ok (next session change) t) = .ok () u ∧ ∃ reg',
      reg'.store = reg.store ∧ reg'.session = nextSession reg.session (encode change) ∧
      Current physical heap mem root lock ref wal reg' (image.append (encode change)) (.online wal (next session change)) u := by
  obtain ⟨reg',storeEq,nextEq,nextActive,held,ack,_,_⟩ := succeeded
  have view : reg'.session.view = image.view.append (encode change) := by
    rw [← entered.view]
    cases ack with
    | ack chosen => simpa [WalRecoverySlice.Segmented.Contract.Request.apply, room] using chosen.symm
  have changed : Held physical root lock ref (image.append (encode change)) (.updating wal) t :=
    ⟨held.owned, held.phaseEq, held.catalog, held.manifest⟩
  have nextPhase : PhasePrimitives physical root lock ref (image.append (encode change)) := ⟨phase.read, phase.swap⟩
  obtain ⟨u,pub,updated,reusable,_⟩ := NativeWriteRelease.publishActive nextPhase cache changed nextActive
    (next session change) (input.publication pos t sent reg' nextActive.2.1)
  exact ⟨u,pub,reg',storeEq,nextEq,updated,reusable,view⟩

/-- Both mutations use this same public entry point. The success carries
the actual store, control, and active child for the following operation. -/
theorem healthyStep (cur : Current physical heap mem root lock ref wal reg image (.online wal session) start)
    (bound : Native.Handle.AtRoot h root ref) (cache : Cached heap physical root lock ref)
    (phase : PhasePrimitives physical root lock ref image) (change : Change)
    (fits : image.view.tail + 1 < UInt64.size)
    (io : StepIO physical heap mem root lock ref wal reg session image change start)
    (ok : io.Healthy) (linux : System.Platform.isWindows = false) :
    ∃ t reg', Native.mutation h change start = .ok () t ∧ reg'.store = reg.store ∧
      reg'.session = nextSession reg.session (encode change) ∧
      Current physical heap mem root lock ref wal reg' (image.append (encode change)) (.online wal (next session change)) t := by
  obtain ⟨entered, ran⟩ := dispatch cur bound cache phase io.borrows change fits
  let input := io.append entered
  obtain ⟨dir, removal, reports, removes⟩ := ok entered
  have room := walRoom entered fits
  obtain ⟨pos,t,sent,succeeded⟩ :=
    input.worker.healthy entered.active entered.held (encode_size change) room linux reports removes
  rw [sent] at ran
  obtain ⟨u,pub,reg',storeEq,nextEq,updated⟩ := publish entered cache phase input room sent succeeded
  exact ⟨u,reg',ran.trans pub,storeEq,nextEq,updated⟩

/-- Reported failure preserves both permitted WAL histories through the
actual inner close, including failure of a nested unlock. -/
theorem step (cur : Current physical heap mem root lock ref wal reg image (.online wal session) start)
    (bound : Native.Handle.AtRoot h root ref) (grant : NativeReadScope.Grant root lock ref)
    (cache : Cached heap physical root lock ref) (phase : PhasePrimitives physical root lock ref image)
    (change : Change) (fits : image.view.tail + 1 < UInt64.size)
    (io : StepIO physical heap mem root lock ref wal reg session image change start)
    (release : NativeWriteRelease.Laws heap (some (.append (encode change))) physical root lock ref image)
    (linux : System.Platform.isWindows = false) :
    match Native.mutation h change start with
    | .ok () t => ∃ reg', reg'.store = reg.store ∧ reg'.session = nextSession reg.session (encode change) ∧
      Current physical heap mem root lock ref wal reg' (image.append (encode change)) (.online wal (next session change)) t
    | .error _ t => NativeReadRelease.Custody physical root lock ref image t (some (.append (encode change))) := by
  obtain ⟨entered, ran⟩ := dispatch cur bound cache phase io.borrows change fits
  let input := io.append entered
  have room := walRoom entered fits
  have checked := input.worker.append entered.active entered.held (encode_size change) room linux
  unfold Alvoki.NativePost.IOReturns at checked
  rw [ran]
  cases real : WalRecoverySlice.Segmented.Native.append wal (encode change) (NativeWrite.issueWorld ref wal start) with
  | error e t =>
    rw [real] at checked
    obtain ⟨held, pending, slot, custody⟩ := checked
    obtain ⟨_, eq, stopped⟩ := NativeWriteRelease.afterError release grant phase
      (.ofRecover held (entered.view ▸ pending)) custody e
    rw [eq]
    exact stopped
  | ok pos t =>
    rw [real] at checked
    obtain ⟨u,pub,reg',storeEq,nextEq,updated⟩ := publish entered cache phase input room real checked
    rw [pub]
    exact ⟨reg',storeEq,nextEq,updated⟩

/-- The ordinary public get can use tables or report an allowed read error
after a mutation. Its frame includes the same write authority. -/
theorem get (cur : Current physical heap mem root lock ref wal reg image (.online wal session) start)
    (bound : Native.Handle.AtRoot h root ref) (cache : Cached heap physical root lock ref)
    (phase : PhasePrimitives physical root lock ref image) (installed : Installed session image history)
    (read : ∀ w t, Current physical heap mem root lock ref wal reg image (.online wal session) w →
      (ref.get : IO (Phase Wal)) w = .ok (.online wal session) t → KeepsLive mem reg w t)
    (tables : NativeRead.Primitives (NativeRead.tableNamespace physical root) life
      (Current physical heap mem root lock ref wal reg image (.online wal session))) (key : UInt64) :
    NativeRead.Released life ref (root / "tables") key start ∧
      match Native.get h key start with
      | .ok v t => v = denote history key ∧ Current physical heap mem root lock ref wal reg image (.online wal session) t
      | .error _ t => Current physical heap mem root lock ref wal reg image (.online wal session) t := by
  apply NativeRead.publicGet (wal := wal) ref root bound (NativeRead.tableNamespace physical root) rfl _ cur _ (fun _ c => c.held.catalog)
    installed tables key
  intro w c
  obtain ⟨t, observed, frame⟩ := phase.refRead wal w c.held.owned (c.held.phaseEq.symm ▸ rfl)
  have seen := c.held.phaseEq ▸ observed
  exact ⟨t, seen, c.held.phaseEq ▸ c.advance cache frame (read _ _ c seen)⟩

abbrev extend (i : Selected) (c : Change) := i.append (encode c)

def program (h : Native.Handle) (first second : Change) (key : UInt64) : IO (Option UInt64) := do
  Native.mutation h first
  Native.mutation h second
  Native.get h key

abbrev After (physical : W → Footprint inode) (heap : PhaseMemory)
    (mem : ChildMemory (fun w => (physical w).disk)) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (reg : Registration) (session : Session) (image : Selected)
    (c : Change) (t : W) :=
  Current physical heap mem root lock ref wal reg (extend image c) (.online wal (next session c)) t

/-- The second set of local primitive observations is indexed by the
registration and world returned by the first public operation. -/
structure PairIO (physical : W → Footprint inode) (heap : PhaseMemory)
    (mem : ChildMemory (fun w => (physical w).disk)) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (reg : Registration) (session : Session) (image : Selected)
    (first second : Change) (start : W) where
  firstIO : StepIO physical heap mem root lock ref wal reg session image first start
  secondIO : ∀ t (reg' : Registration), reg'.store = reg.store → reg'.session = nextSession reg.session (encode first) →
    After physical heap mem root lock ref wal reg' session image first t →
      StepIO physical heap mem root lock ref wal reg' (next session first) (extend image first) second t

def PairIO.Healthy (ops : PairIO physical heap mem root lock ref wal reg session image first second start) : Prop :=
  ops.firstIO.Healthy ∧ ∀ t r store control current, (ops.secondIO t r store control current).Healthy

/-- Capacity one forces the first put in place and the second (delete)
through successor creation and CONTROL publication. Both results expose
the same bound L0 handle and child-memory interpretation. -/
theorem putDeleteGet (cur : Current physical heap mem root lock ref wal reg image (.online wal session) start)
    (bound : Native.Handle.AtRoot h root ref) (cache : Cached heap physical root lock ref)
    (phase : PhasePrimitives physical root lock ref image) (key value : UInt64)
    (capacity : reg.session.control.capacity = 1) (count : reg.session.activeCount = 0)
    (room : image.view.tail + 2 < UInt64.size)
    (ops : PairIO physical heap mem root lock ref wal reg session image (key,.put value) (key,.delete) start)
    (healthy : ops.Healthy) (linux : System.Platform.isWindows = false)
    (read : ∀ (r : Registration) w t, r.store = reg.store →
      let first := (key, Mutation.put value)
      let second := (key, Mutation.delete)
      After physical heap mem root lock ref wal r (next session first) (extend image first) second w →
      (ref.get : IO (Phase Wal)) w = .ok (.online wal (next (next session first) second)) t → KeepsLive mem r w t) :
    let first := (key, Mutation.put value)
    let second := (key, Mutation.delete)
    ∃ u v t, ∃ one two : Registration,
      Native.put h key value start = .ok () u ∧ Native.delete h key u = .ok () v ∧ Native.get h key v = .ok none t ∧
      program h first second key start = .ok none t ∧
      one.session.control.active = reg.session.control.active ∧ two.session.control.active = one.session.control.active + 1 ∧
      one.store = reg.store ∧ two.store = reg.store ∧
      After physical heap mem root lock ref wal one session image first u ∧
      After physical heap mem root lock ref wal two (next session first) (extend image first) second t := by
  intro first second
  obtain ⟨u,one,put,firstStore,firstControl,afterFirst⟩ :=
    healthyStep cur bound cache phase first (by omega) ops.firstIO healthy.1 linux
  have secondPhase : PhasePrimitives physical root lock ref (extend image first) := ⟨phase.read,phase.swap⟩
  have fits : (extend image first).view.tail + 1 < UInt64.size := by
    simpa [extend, Selected.append, WalRecoverySlice.Segmented.Contract.View.append, WalRecoverySlice.Segmented.Contract.View.tail,
      Nat.add_assoc] using room
  obtain ⟨v,two,del,secondStore,secondControl,afterSecond⟩ :=
    healthyStep afterFirst bound cache secondPhase second fits
      (ops.secondIO _ _ firstStore firstControl afterFirst) (healthy.2 _ _ firstStore firstControl afterFirst) linux
  have endPhase : PhasePrimitives physical root lock ref (extend (extend image first) second) := ⟨phase.read,phase.swap⟩
  obtain ⟨t, seen, frame⟩ := endPhase.refRead wal v afterSecond.held.owned (afterSecond.held.phaseEq.symm ▸ rfl)
  have phaseValue := afterSecond.held.phaseEq ▸ seen
  have finalState := afterSecond.held.phaseEq ▸ afterSecond.advance cache frame
    (read two v t (secondStore.trans firstStore) afterSecond phaseValue)
  have hit := NativeRead.memHit ref bound phaseValue (key := key) (mutation := .delete)
    (by simp [second, insert])
  have agree : one.session.control = reg.session.control := by simp [firstControl, nextSession, count, capacity]
  have full : one.session.activeCount = one.session.control.capacity := by simp [firstControl, nextSession, count, capacity]
  have rotated : two.session.control.active = one.session.control.active + 1 := by
    simp [secondControl, nextSession, full, WalRecoverySlice.Segmented.Model.successor]
  refine ⟨u,v,t,one,two,put,del,hit,?_,congrArg (·.active) agree,rotated,firstStore,secondStore.trans firstStore,afterFirst,finalState⟩
  simp only [program, Bind.bind, instMonadEIO._aux_13, EST.bind, put, del, hit, Mutation.value]

end ExperimentalL0.MutationSequence
