import Alvoki.Experiments.L0.NativeRecoverAt

namespace ExperimentalL0.NativeWrite
open Lifecycle NativeScope
open WalRecoverySlice.Segmented (Contract.View)

private abbrev F := ExceptT String IO

private theorem checked_bind (a : F α) (f : α → F β) :
    Native.checked (a >>= f) = (Native.checked a >>= fun x => Native.checked (f x)) := by
  funext w
  unfold Native.checked
  rw [ExceptT.run_bind]
  cases ran : a.run w with
  | error e t => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
  | ok v t => cases v <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran,
      Pure.pure, instMonadEIO._aux_5, EST.pure] <;> rfl

private theorem checked_lift (a : IO α) : Native.checked (liftM a : F α) = a := by
  funext w
  have lifted : (liftM a : F α).run = (do return (Except.ok (← a) : Except String α) : IO _) := rfl
  cases ran : a w <;> simp [Native.checked, lifted, Bind.bind, instMonadEIO._aux_13, EST.bind, ran,
    Pure.pure, instMonadEIO._aux_5, EST.pure]

private theorem checked_pure (x : α) : Native.checked (pure x : F α) = pure x := rfl
private theorem checked_throw (e : String) :
    Native.checked (throw e : F α) = throw (IO.userError e) := rfl

private abbrev borrow (ref : Ref) (f : Wal → IO α) : IO α := do
  let some wal := (← (ref.get : IO (Phase Wal))).wal | throw (IO.userError "L0 cannot use the WAL in this phase")
  f wal

private theorem checked_borrow (ref : Ref) (f : Wal → IO α) :
    Native.checked ((Native.componentCell ref).borrowWal "L0 cannot use the WAL in this phase"
      (fun h => liftM (f h))) = borrow ref f := by
  unfold Cell.borrowWal Native.componentCell borrow
  rw [checked_bind, checked_lift]
  apply congrArg (Bind.bind (ref.get : IO (Phase Wal)))
  funext p
  cases p.wal <;> simp [checked_lift, checked_throw]

/-- The public write scans and appends through two independent reads of
the owned phase reference. The rejected position never enters append. -/
theorem write_atRoot (root : System.FilePath) (ref : Ref) (s : Session) (change : Change) :
    Native.checked (write (Native.callbackComponents root ref) s change) =
      (do
        let view ← borrow ref WalRecoverySlice.Segmented.Native.scan
        unless view.tail + 1 < UInt64.size do throw (IO.userError "absolute WAL position exhausted")
        borrow ref (fun h => do let _ ← WalRecoverySlice.Segmented.Native.append h (encode change); pure ())
        return {s with mem := insert s.mem change} : IO Session) := by
  unfold write Native.callbackComponents Cell.components Native.storageCallbacks
  rw [checked_bind, checked_borrow]
  apply congrArg (Bind.bind _)
  funext view
  split <;> simp only [checked_bind, checked_borrow, checked_pure, checked_throw]

open NativeRead (Footprint Owned SessionAt Online Frame)
open WalRecoverySlice.Segmented.Native (PhaseMemory scanWorld)

/-- The outcome of publication or error cleanup for the already-issued
public mutation. On error the inner close still runs at its reached world. -/
def afterWrite (ref : Ref) (written : EST.Out IO.Error IO.RealWorld Session) :
    EST.Out IO.Error IO.RealWorld Unit :=
  let closed := (Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close
  let failed := fun e w => EST.Out.error e (closed.toBaseIO w).state
  match written with
  | .error e t => failed e t
  | .ok next t =>
    match (Native.phaseCell ref).publish (IO.userError "L0 requires reopen") next t with
    | .ok () u => .ok () u
    | .error e u => failed e u

/-- A successful WAL append leaves the L0 reference in its reserved
updating phase. Publication reads that reference and installs the new
session before the public operation can report success. -/
theorem afterWrite_publish {physical : W → Footprint inode}
    (held : NativeRecoverAt.Held physical root lock ref image (.updating wal) w)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image) (next : Session) :
    ∃ t u, NativeRead.Frame physical root wal image.tables w t ∧
      NativeRead.FrameTo physical root wal image.tables t u (.online wal next) ∧
      NativeRecoverAt.Held physical root lock ref image (.online wal next) u ∧
      afterWrite ref (.ok next w) = .ok () u := by
  obtain ⟨t, read, keep⟩ := phase.refRead wal w held.owned (by rw [held.phaseEq]; rfl)
  have updated := held.frame keep
  obtain ⟨u, swap, reached⟩ := phase.swap t updated.owned wal (.online wal next)
  refine ⟨t, u, keep, reached, reached.held updated, ?_⟩
  have observed : (ref.get : IO (Phase Wal)) w = .ok (.updating wal) t := held.phaseEq ▸ read
  unfold afterWrite
  simp [Cell.publish, Native.phaseCell, Bind.bind, instMonadEIO._aux_13, EST.bind,
    observed, Phase.publish, swap]
  rfl

private theorem mutation_started (binding : Native.Handle.AtRoot handle root ref) (change : Change)
    (read : (ref.get : IO (Phase Wal)) start = .ok (.online wal s) entered)
    (swapped : (ref.swap (.updating wal) : IO (Phase Wal)) entered = .ok previous hidden) :
    Native.mutation handle change start =
      afterWrite ref (Native.checked (write (Native.callbackComponents root ref) s change) hidden) := by
  rw [Native.mutation_atRoot binding,
    Cell.update_online_io (Native.phaseCell ref) _ _ _ read swapped]
  let op := Native.checked (write (Native.callbackComponents root ref) s change)
  cases ran : op hidden with
  | error e t =>
    simp [op] at ran
    simp [afterWrite, Bind.bind, instMonadEIO._aux_13, EST.bind, EIO.toBaseIO, ran]
  | ok v t =>
    cases pub : (Native.phaseCell ref).publish (IO.userError "L0 requires reopen") v t <;>
      simp [op] at ran <;>
      simp [afterWrite, Bind.bind, instMonadEIO._aux_13, EST.bind, EIO.toBaseIO, ran, pub]

private theorem borrow_run (f : Wal → IO α)
    (read : (ref.get : IO (Phase Wal)) w = .ok (.updating wal) t) :
    borrow ref f w = f wal t := by
  simp [borrow, Bind.bind, instMonadEIO._aux_13, EST.bind, read, Phase.wal]

/-- The position guard keeps its pre-append disk. Otherwise the public
operation calls append once, using precisely the registration and world
that survived both phase borrows and the cached scan. -/
theorem dispatch {physical : W → Footprint inode}
    (online : Online physical root lock ref wal s image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (heap : PhaseMemory) (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (scan : ∀ w, SessionAt physical root lock ref wal s image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w)
    (change : Change) :
    if image.view.tail + 1 < UInt64.size then
      ∃ issued, SessionAt physical root lock ref wal s image history issued (.updating wal) ∧
        Native.mutation handle change start = afterWrite ref
          (match WalRecoverySlice.Segmented.Native.append wal (encode change) issued with
           | .ok _ t => .ok {s with mem := insert s.mem change} t
           | .error e t => .error e t)
    else
      ∃ rejected, SessionAt physical root lock ref wal s image history rejected (.updating wal) ∧
        Native.mutation handle change start = afterWrite ref (.error (IO.userError "absolute WAL position exhausted") rejected) := by
  have readAt {w stage} (entry : SessionAt physical root lock ref wal s image history w stage)
      (ownsWal : stage.wal = some wal) :
      ∃ t, (ref.get : IO (Phase Wal)) w = .ok stage t ∧
        SessionAt physical root lock ref wal s image history t stage := by
    obtain ⟨t, ran, frame⟩ := phase.refRead wal w entry.owned (entry.phase.symm ▸ ownsWal)
    exact ⟨t, entry.phase ▸ ran, entry.phase ▸ entry.advance frame⟩
  obtain ⟨entered, read, online'⟩ := readAt online rfl
  obtain ⟨hidden, swapped, step⟩ := phase.swap entered online'.owned wal (.updating wal)
  have updating := online'.advance step
  have run := mutation_started binding change read swapped
  rw [write_atRoot] at run
  obtain ⟨scanStart, borrowScan, scanning⟩ := readAt updating rfl
  obtain ⟨reg, slot, _, _, view⟩ := scanning.child
  have regReady := (cached _ scanning.owned wal reg).mp slot
  have ran := (WalRecoverySlice.Segmented.Native.scan_ready_world heap regReady.ready).1
  have scanned := borrow_run _ borrowScan |>.trans (view ▸ ran)
  have scannedFrame := WalRecoverySlice.Segmented.Native.scanWorld_frame (scan _ scanning) Frame.refl
  have afterScan := scanning.phase ▸ scanning.advance scannedFrame
  split
  · rename_i fits
    obtain ⟨issued, borrowAppend, ready⟩ := readAt afterScan rfl
    refine ⟨issued, ready, run.trans ?_⟩
    apply congrArg (afterWrite ref)
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, scanned, fits]
    simp only [borrow, Bind.bind, instMonadEIO._aux_13, EST.bind, borrowAppend, Phase.wal]
    cases WalRecoverySlice.Segmented.Native.append wal (encode change) issued <;> rfl
  · rename_i full
    refine ⟨_, afterScan, run.trans ?_⟩
    apply congrArg (afterWrite ref)
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, scanned, full]
    rfl

end ExperimentalL0.NativeWrite
