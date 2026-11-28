import Alvoki.Experiments.L0.MutationIngressCut
import Alvoki.Experiments.L0.InterruptedWorker
import Alvoki.Experiments.L0.ObservedIO

namespace ExperimentalL0.MutationAllCuts
open NativeScope Lifecycle
open ReserveScanCut (Destination View Program)
open MutationExitCut (Tail LeafStop Cut afterStore suffix)
open InterruptedMutation (Prefix Worker BoundaryOr)
open WalRecoverySlice.Segmented.Model (Disk)
open WalRecoverySlice.Segmented.Native (PhaseMemory returnedWorld)
open WalRecoverySlice.Segmented.Native.AppendCut (Stop Observed publicProgram tagAt)

structure Sites where
  localStop : LeafStop
  walStop : Stop
  disk : W → Disk

private def observeBase (sites : Sites) (last : W) (a : BaseIO α) : Observed α :=
  ⟨liftM a, fun w d => (last = w ∨ sites.localStop a w last ∨ last = (a w).state) ∧ d = sites.disk last⟩

private def observedCell (sites : Sites) (last : W) (r : Ref) : Cell Observed Wal where
  read := observeBase sites last r.get
  swap v := observeBase sites last (r.swap v)

noncomputable def worker (sites : Sites) (last : W) (change : Change) (wal : Wal) : Observed Nat :=
  let program := publicProgram wal.parts.choose wal.parts.choose_spec.choose (encode change)
    (tagAt (BoundaryOr sites.disk sites.walStop) last)
  ⟨WalRecoverySlice.Segmented.Native.append wal (encode change),program.cuts⟩

/-- The same position guard and second borrow that run in native IO now
interpret the selected child's complete public append schedule. -/
noncomputable def gate (sites : Sites) (last : W) (ref : Ref) (change : Change) (s : Session) (view : View) : Observed Session :=
  MutationIngressCut.gate (observedCell sites last ref) (fun h => do let _ ← worker sites last change h; pure ()) change s view

private def ordinaryGate (ref : Ref) (change : Change) :=
  MutationIngressCut.gate (Native.phaseCell ref) (MutationIngressCut.append change) change

private theorem gate_run (sites : Sites) (last : W) (r : Ref) (change : Change) (s : Session) (v : View) :
    (gate sites last r change s v).run = ordinaryGate r change s v := by
  unfold gate ordinaryGate MutationIngressCut.gate
  by_cases fits : v.tail + 1 < UInt64.size <;> simp only [fits,↓reduceIte]
  · let send := fun h => (do let _ ← worker sites last change h; pure () : Observed Unit)
    have same : ((observedCell sites last r).borrowWal (IO.userError "L0 cannot use the WAL in this phase") send).run =
        (Native.phaseCell r).borrowWal (IO.userError "L0 cannot use the WAL in this phase") (MutationIngressCut.append change) := by
      unfold Cell.borrowWal
      apply congrArg (Bind.bind (r.get : IO (Phase Wal)))
      funext phase
      dsimp only
      cases phase.wal <;> rfl
    exact congrArg (fun a : IO Unit => a >>= fun _ => pure {s with mem := insert s.mem change}) same
  · rfl

def closeScope (ref : Ref) (lock : IO.FS.Handle) (action : IO Unit) :=
  finish (ε := IO.Error) action (finish (ε := IO.Error) ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close) lock.unlock)

private theorem scoped_congr (eq : a w = b u) (r : Ref) (lock : IO.FS.Handle) :
    closeScope r lock a w = closeScope r lock b u := by
  unfold closeScope
  rw [finish_io a,finish_io b]
  simp only [EIO.toBaseIO,eq]

def restored : Except IO.Error α → W → EST.Out IO.Error IO.RealWorld α
  | .ok x,t => .ok x t
  | .error e,t => .error e t

noncomputable def post (sites : Sites) (d : Disk) (r : Ref) (lock : IO.FS.Handle) (s : Session)
    (rep : Except IO.Error Session) : ObservedIO Unit :=
  ⟨closeScope r lock (fun w => NativeWrite.afterWrite r (restored rep w)),
    fun w last => d = sites.disk last ∧ Cut sites.localStop (afterStore r lock s (restored rep w)) w last⟩

noncomputable def terminal (sites : Sites) (d : Disk) (ref : Ref) (lock : IO.FS.Handle) (change : Change) :
    Destination → ObservedIO Unit
  | .invalid => ⟨closeScope ref lock (throw (IO.userError "L0 requires reopen")),fun w last => d = sites.disk last ∧
      Cut sites.localStop (MutationExitCut.close ref (.call lock.unlock.toBaseIO (fun _ => .done))) w last⟩
  | .skipped s => post sites d ref lock s (.ok s)
  | .scanned s (.error e) => post sites d ref lock s (.error e)
  | .scanned s (.ok v) =>
    let store : ObservedIO Session := ⟨ordinaryGate ref change s v,
      fun w last => (gate sites last ref change s v).cuts w d⟩
    store.thenResult (post sites d ref lock s)

noncomputable def program (sites : Sites) (d : Disk) (r : Ref) (lock : IO.FS.Handle) (change : Change) :
    ObservedIO Unit :=
  (ReserveScanCut.program r (fun _ => true)).observeIf (fun t => d = sites.disk t) sites.localStop
    (terminal sites d r lock change)

private theorem terminal_run (sites : Sites) (d : Disk) (r : Ref) (lock : IO.FS.Handle) (change : Change)
    (dest : Destination) (w : W) :
    (terminal sites d r lock change dest).run w =
      closeScope r lock (ReserveScanCut.applyTail pure (ordinaryGate r change) r dest) w := by
  cases dest with
  | invalid | skipped => rfl
  | scanned s rep =>
    cases rep with
    | error => rfl
    | ok v =>
      change closeScope r lock _ ((ordinaryGate r change s v).toBaseIO w).state = _
      apply scoped_congr
      change NativeWrite.afterWrite r (restored ((ordinaryGate r change s v).toBaseIO w).val
        ((ordinaryGate r change s v).toBaseIO w).state) = NativeWrite.afterWrite r (ordinaryGate r change s v w)
      cases ran : ordinaryGate r change s v w <;> simp only [EIO.toBaseIO,ran,restored]

/-- The returned program includes the actual open scope's finalizers and
preserves the original public error and the final world. -/
theorem erases (p : Prefix path root start) (sites : Sites) (d : Disk) (change : Change) :
    (program sites d p.ref p.lock change).run p.callback =
      Native.withOpen path (fun h => Native.mutation h change) start := by
  obtain ⟨h,binding,invoked⟩ := p.withOpen (fun h => Native.mutation h change)
  rw [invoked, ← MutationIngressCut.source binding change]
  let prog := ReserveScanCut.program p.ref (fun _ => true)
  let k := ReserveScanCut.applyTail pure (ordinaryGate p.ref change) p.ref
  change (prog.observeIf _ _ _).run _ = closeScope p.ref p.lock (prog.resume k) _
  rw [Program.observeIf_run]
  rw [Program.resume_eval, scoped_congr (Program.resume_eval prog k p.callback) p.ref p.lock]
  apply terminal_run

private theorem cutStep (op : BaseIO α) (k : α → Tail) (hit : Cut stop (k (op w).val) (op w).state last) :
    Cut stop (.call op k) w last := by
  cases hit with
  | boundary earlier => exact .boundary (.step earlier)
  | during earlier inFlight => exact .during (.step earlier) inFlight

private theorem liftPrelude (p : Program) (k : Destination → Tail) (hit : Cut stop p.path w last) :
    Cut stop (MutationIngressCut.continueAt k p) w last := by
  induction p generalizing w with
  | reached =>
    cases hit with
    | boundary earlier => cases earlier; exact .boundary .here
    | during earlier _ => cases earlier
  | call op next ih =>
    cases hit with
    | boundary earlier =>
      cases earlier with
      | here => exact .boundary .here
      | step earlier => exact cutStep _ _ (ih _ (.boundary earlier))
    | during earlier stopped =>
      cases earlier with
      | here => exact .during .here stopped
      | step earlier => exact cutStep _ _ (ih _ (.during earlier stopped))

private theorem liftTerminal (p : Program) (k : Destination → Tail)
    (hit : Cut stop (k (p.eval w).val) (p.eval w).state last) :
    Cut stop (MutationIngressCut.continueAt k p) w last := by
  induction p generalizing w with
  | reached => exact hit
  | call op next ih => exact cutStep _ _ (ih (op w).val hit)

noncomputable abbrev canonical (p : Prefix path root start) : Worker p :=
  ⟨p.wal.parts.choose,p.wal.parts.choose_spec.choose,p.wal.parts.choose_spec.choose_spec⟩

private structure Reached (p : Prefix path root start) (image : Selected) : Prop where
  scanned : (ReserveScanCut.program p.ref (fun _ => true)).eval p.callback =
      ⟨.scanned p.session (.ok image.view), NativeWrite.guardWorld p.ref p.wal p.callback⟩
  borrowed : (p.ref.get : IO (Phase Wal)) (NativeWrite.guardWorld p.ref p.wal p.callback) =
      .ok (.updating p.wal) p.issue

private theorem reached (p : Prefix path root start) (online : NativeRead.Online physical root p.lock p.ref p.wal
    p.session image hist p.callback) (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap)
    (scans : ∀ w, NativeRead.SessionAt physical root p.lock p.ref p.wal p.session image hist w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w) : Reached p image := by
  obtain ⟨entered,hidden,rd,swap,owned⟩ := NativeWrite.reserve online ops.phase
  have rdEq := rd
  rw [read_io] at rdEq
  obtain rfl := (EST.Out.ok.inj rdEq).2
  have swapEq := swap
  rw [swap_io] at swapEq
  obtain rfl := (EST.Out.ok.inj swapEq).2
  obtain ⟨read,scan,kept⟩ := NativeWrite.scanAt owned heap ops.cleanup.cached ops.phase scans
  unfold Native.callbackComponents Cell.components Native.storageCallbacks at scan
  rw [NativeWrite.checked_borrow] at scan
  have dest := ReserveScanCut.destination (fun _ => true) rd (fun _ => read) (fun _ => scan)
  obtain ⟨t,get,_⟩ := ops.phase.refRead p.wal _ kept.owned (kept.phase.symm ▸ rfl)
  have atGuard := kept.phase ▸ get
  rw [read_io] at get
  rw [← (EST.Out.ok.inj get).2] at atGuard
  exact ⟨dest,atGuard⟩

inductive Covered (p : Prefix path root start) (change : Change) (image : Selected) (sites : Sites)
    (last : W) (d : Disk) : Prop where
  | before : d = sites.disk last → Cut sites.localStop (MutationIngressCut.prelude p.ref change) p.callback last →
      Covered p change image sites last d
  | rejected : ¬ image.view.tail + 1 < UInt64.size → d = sites.disk last →
      Cut sites.localStop (suffix p.ref p.lock p.session false) (NativeWrite.guardWorld p.ref p.wal p.callback) last →
      Covered p change image sites last d
  | inside : image.view.tail + 1 < UInt64.size → (canonical p).Observation change sites.disk sites.walStop last d →
      Covered p change image sites last d
  | afterReturn : image.view.tail + 1 < UInt64.size → d = sites.disk last →
      Cut sites.localStop (MutationExitCut.remaining p change) (returnedWorld (MutationExitCut.output p change)) last →
      Covered p change image sites last d

private theorem gateCut (p : Prefix path root start) (sites : Sites) (change : Change) (atPhase : Reached p image)
    (fits : image.view.tail + 1 < UInt64.size)
    (raw : (gate sites last p.ref change p.session image.view).cuts (NativeWrite.guardWorld p.ref p.wal p.callback) d) :
    Covered p change image sites last d := by
  let w := NativeWrite.guardWorld p.ref p.wal p.callback
  have get := atPhase.borrowed
  rw [read_io] at get
  unfold gate MutationIngressCut.gate at raw
  simp only [fits,↓reduceIte,Observed.resultCuts] at raw
  unfold Cell.borrowWal at raw
  rw [Observed.bindCuts] at raw
  rcases raw with early | later
  · obtain ⟨location,disk⟩ := early
    apply Covered.before disk
    apply liftTerminal
    rw [atPhase.scanned]
    simp only
    rw [MutationIngressCut.borrowLeaf fits]
    rcases location with rfl | stopped | rfl
    · exact .boundary .here
    · exact .during .here stopped
    · exact .boundary (.step .here)
  · have observed : (observedCell sites last p.ref).read.run (NativeWrite.guardWorld p.ref p.wal p.callback) =
        .ok (.updating p.wal) p.issue := atPhase.borrowed
    rw [observed] at later
    change ((worker sites last change p.wal) >>= fun _ => pure ()).cuts p.issue d at later
    rw [Observed.resultCuts] at later
    exact .inside fits (.instruction later)

private theorem ordinaryGate_ok (p : Prefix path root start) (change : Change) (reached : Reached p image)
    (fits : image.view.tail + 1 < UInt64.size) :
    ordinaryGate p.ref change p.session image.view (NativeWrite.guardWorld p.ref p.wal p.callback) =
      match MutationExitCut.output p change with
      | .ok _ t => .ok {p.session with mem := insert p.session.mem change} t | .error e t => .error e t := by
  unfold ordinaryGate MutationIngressCut.gate Cell.borrowWal Native.phaseCell MutationIngressCut.append
  simp only [fits,↓reduceIte,Bind.bind,instMonadEIO._aux_13,EST.bind,reached.borrowed,Phase.wal]
  cases ran : WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue <;>
    simp [MutationExitCut.output,ran,Pure.pure,instMonadEIO._aux_5,EST.pure]

/-- Classify a cut of the composed public schedule without assuming which
worker or cleanup branch was reached. -/
private theorem classifyAt (p : Prefix path root start) (change : Change) (sites : Sites) (atPhase : Reached p image)
    (raw : (program sites d p.ref p.lock change).cut p.callback last) : Covered p change image sites last d := by
  rcases Program.classifyIf _ _ _ _ raw with early | late
  · exact .before early.2 (liftPrelude _ _ early.1)
  rw [atPhase.scanned] at late
  change (gate sites last p.ref change p.session image.view).cuts (NativeWrite.guardWorld p.ref p.wal p.callback) d ∨
    (post sites d p.ref p.lock p.session _).cut _ last at late
  by_cases fits : image.view.tail + 1 < UInt64.size
  · rcases late with work | reported
    · exact gateCut p sites change atPhase fits work
    · obtain ⟨disk,cut⟩ := reported
      apply Covered.afterReturn fits disk
      change Cut _ (afterStore _ _ _ (restored ((ordinaryGate _ _ _ _).toBaseIO _).val _)) _ _ at cut
      unfold EIO.toBaseIO at cut
      simp only [ordinaryGate_ok p change atPhase fits] at cut
      unfold MutationExitCut.remaining
      cases done : MutationExitCut.output p change <;>
        simp only [done,restored,afterStore,MutationExitCut.accepted,returnedWorld] at cut ⊢ <;> exact cut
  · have failed : ordinaryGate p.ref change p.session image.view (NativeWrite.guardWorld p.ref p.wal p.callback) =
        .error (IO.userError "absolute WAL position exhausted") (NativeWrite.guardWorld p.ref p.wal p.callback) := by
      simp only [ordinaryGate,MutationIngressCut.gate,fits,↓reduceIte]; rfl
    rcases late with impossible | stopped
    · simp only [gate,MutationIngressCut.gate,fits,↓reduceIte,Observed.bindCuts] at impossible
      exact impossible.elim False.elim False.elim
    · obtain ⟨disk,cut⟩ := stopped
      apply Covered.rejected fits disk
      change Cut _ (afterStore _ _ _ (restored ((ordinaryGate _ _ _ _).toBaseIO _).val _)) _ _ at cut
      simp only [EIO.toBaseIO,failed,restored,afterStore] at cut
      exact cut

open NativeMutationScope (uncertainEvents AppendPrimitives)
open MutationExitCut (Recovery Frame Frames)
open WalRecoverySlice.Segmented.Native.AppendCut (CutRuntime FrameRuntime)

abbrev Outcome (physical : W → NativeRead.Footprint inode) (heap : PhaseMemory) (path root : System.FilePath)
    (image : Selected) (life : NativeRead.Lifetime) (before : List Event) (change : Change) (after : W) :=
  Recovery physical heap path root image life none (uncertainEvents before change) after ∨
  Recovery physical heap path root image life (some (.append (encode change))) (uncertainEvents before change) after ∨
  Recovery physical heap path root (image.append (encode change)) life none (uncertainEvents before change) after

/-- Any raw observation of the reached public callback selects either the
unmodified history, the one pending request, or the definitely extended
history. Each alternative supplies the two public reopens from the same
reboot, with the newly reached physical state threaded through the reads. -/
theorem interrupted {physical : W → NativeRead.Footprint inode} (p : Prefix path root start) (change : Change)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (prior : Execution.Run before none image)
    (scans : ∀ hist w, NativeRead.SessionAt physical root p.lock p.ref p.wal p.session image hist w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (appendIO : AppendPrimitives runtime change) (linux : System.Platform.isWindows = false)
    (outerStop : LeafStop) (innerStop : Stop) (last : W) (d : Disk)
    (ingress : Frames (Frame physical root image.tables) outerStop (MutationIngressCut.prelude p.ref change) p.callback)
    (denied : ¬ image.view.tail + 1 < UInt64.size →
      Frames (Frame physical root image.tables) outerStop (suffix p.ref p.lock p.session false)
        (NativeWrite.guardWorld p.ref p.wal p.callback))
    (inner : image.view.tail + 1 < UInt64.size → ∀ store s, (canonical p).phase = .ready store s →
      CutRuntime (fun w => (physical w).disk) store s (tagAt (BoundaryOr (fun w => (physical w).disk) innerStop) last))
    (framing : image.view.tail + 1 < UInt64.size → ∀ store s, (canonical p).phase = .ready store s →
      FrameRuntime (fun w => (physical w).disk) store s (InterruptedMutation.Protected physical root image))
    (leaving : image.view.tail + 1 < UInt64.size →
      Frames (Frame physical root image.tables) outerStop (MutationExitCut.remaining p change)
        (returnedWorld (MutationExitCut.output p change)))
    (raw : (program ⟨outerStop,innerStop,fun w => (physical w).disk⟩ d p.ref p.lock change).cut p.callback last)
    (boot : NativeAppendCut.Restarted physical root image.tables last d mode after) :
    (program ⟨outerStop,innerStop,fun w => (physical w).disk⟩ d p.ref p.lock change).run p.callback =
        Native.withOpen path (fun h => Native.mutation h change) start ∧
      Outcome physical heap path root image life before change after := by
  refine ⟨erases p _ d change,?_⟩
  obtain ⟨_,hist,online⟩ := p.online entry files heap (runtime _ _) prior
  have atPhase := reached p online (runtime _ _) (scans hist)
  cases classifyAt p change _ atPhase raw with
  | before disk atCut =>
    exact .inl (MutationIngressCut.beforeAppend p change entry files heap (runtime _ _) prior atCut ingress (disk ▸ boot)).2
  | rejected full disk atCut =>
    exact .inl (MutationExitCut.rejected p entry files heap (runtime _ _) prior change scans full atCut (denied full) (disk ▸ boot)).2
  | inside fits hit =>
    have retry := (canonical p).retry entry files heap runtime prior change scans fits appendIO linux (inner fits)
      (framing fits) hit boot
    exact .inr (.inl ⟨retry,retry.readTwice⟩)
  | afterReturn fits disk atCut =>
    have recovered := (MutationExitCut.afterReturn p entry files heap runtime prior change scans fits appendIO linux
      atCut (leaving fits) (disk ▸ boot)).2
    cases accepted : MutationExitCut.accepted (MutationExitCut.output p change) with
    | false => exact .inr (.inl (by simpa only [accepted,MutationExitCut.pending,MutationExitCut.selected,Bool.false_eq_true,↓reduceIte] using recovered))
    | true => exact .inr (.inr (by simpa only [accepted,MutationExitCut.pending,MutationExitCut.selected,↓reduceIte] using recovered))

end ExperimentalL0.MutationAllCuts
