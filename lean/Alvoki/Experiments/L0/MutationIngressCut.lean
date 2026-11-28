import Alvoki.Experiments.L0.ReserveScanSource
import Alvoki.Experiments.L0.MutationExitCut

namespace ExperimentalL0.MutationIngressCut
open NativeScope Lifecycle
open MutationExitCut (Tail PathM pathInstructions)
open ReserveScanCut (Program Destination View)
open InterruptedMutation (Prefix)
open NativeMutationScope (Retry uncertainEvents)

/-- The guard consumes the returned scan and borrows the WAL a second time.
The append starts only after this second reference read returns. -/
def gate [Monad m] [MonadExceptOf IO.Error m] (cell : Cell m Wal) (issue : Wal → m Unit)
    (change : Change) (session : Session) (view : View) : m Session := do
  unless view.tail + 1 < UInt64.size do throw (IO.userError "absolute WAL position exhausted")
  cell.borrowWal (IO.userError "L0 cannot use the WAL in this phase") issue
  return {session with mem := insert session.mem change}

def append (change : Change) (h : Wal) : IO Unit := do
  let _ ← WalRecoverySlice.Segmented.Native.append h (encode change)
  pure ()

/-- Replacing the append boundary by the real append yields the complete
public mutation, with its original guard, error handling and result. -/
theorem source (bound : Native.Handle.AtRoot h root ref) (change : Change) :
    (ReserveScanCut.program ref (fun _ => true)).resume
      (ReserveScanCut.applyTail pure (gate (Native.phaseCell ref) (append change) change) ref) =
        Native.mutation h change := by
  rw [ReserveScanCut.resume, Native.mutation_atRoot bound]
  congr 1
  funext session
  rw [NativeWrite.write_atRoot]
  have borrow : (Native.phaseCell ref).borrowWal (IO.userError "L0 cannot use the WAL in this phase") (append change) =
      NativeWrite.borrow ref (append change) := by
    unfold Cell.borrowWal NativeWrite.borrow
    apply congrArg (Bind.bind (ref.get : IO (Phase Wal)))
    funext phase
    cases phase.wal <;> rfl
  simp only [ReserveScanCut.operation, ite_true]
  apply congrArg (Bind.bind (NativeWrite.borrow ref WalRecoverySlice.Segmented.Native.scan))
  funext view
  by_cases fits : view.tail + 1 < UInt64.size <;> simp only [gate, fits, ↓reduceIte, borrow] <;> rfl

/-- Retain every call in the shared reservation/scan source and continue
each reached result with the corresponding guard and append borrow. -/
def continueAt (k : Destination → Tail) : Program → Tail
  | .reached d => k d
  | .call a rest => .call a fun v => continueAt k (rest v)

def untilAppend (r : Ref) (change : Change) : Destination → Tail
  | .scanned s (.ok view) => gate (pathInstructions.cell r)
      (fun _ => fun _ _ => .done) change s view (fun _ => .done) (fun _ => .done)
  | _ => .done

noncomputable def prelude (r : Ref) (change : Change) :=
  continueAt (untilAppend r change) (ReserveScanCut.program r fun _ => true)

theorem borrowLeaf (fits : view.tail + 1 < UInt64.size) :
    untilAppend r change (.scanned s (.ok view)) = .call r.get (fun _ => .done) := by
  unfold untilAppend gate
  simp only [fits, ↓reduceIte]
  change Tail.call r.get _ = Tail.call r.get _
  apply congrArg (Tail.call r.get)
  funext stage
  cases seen : stage.wal <;> simp [seen] <;> rfl

theorem rejected (full : ¬ view.tail + 1 < UInt64.size) :
    untilAppend r change (.scanned s (.ok view)) = .done := by
  simp only [untilAppend, gate, full, ↓reduceIte]
  rfl

/-- No reached prefix of the reservation, scan or guard has written this
mutation. Local frames and the reboot at its last call preserve the known
history, including power loss and interruptions inside each primitive. -/
theorem beforeAppend (p : Prefix path root start) (change : Change)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start)
    (heap : WithOpenReads.Heap) (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap)
    (trace : Execution.Run before none image) (cutAt : MutationExitCut.Cut stop (prelude p.ref change) p.callback cut)
    (frames : MutationExitCut.Frames (MutationExitCut.Frame physical root image.tables) stop (prelude p.ref change) p.callback)
    (restart : NativeAppendCut.Restarted physical root image.tables cut (physical cut).disk mode after) :
    (∃ h : Native.Handle, h.AtRoot root p.ref ∧
      (ReserveScanCut.program p.ref (fun _ => true)).resume
        (ReserveScanCut.applyTail pure (gate (Native.phaseCell p.ref) (append change) change) p.ref) =
        Native.mutation h change ∧
      Native.withOpen path (fun h => Native.mutation h change) start = finish (ε := IO.Error) (Native.mutation h change)
        (finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close) p.lock.unlock) p.callback) ∧
    MutationExitCut.Recovery physical heap path root image life none (uncertainEvents before change) after := by
  obtain ⟨run,_,online⟩ := p.online entry files heap ops trace
  obtain ⟨h,bound,scope⟩ := p.withOpen (fun h => Native.mutation h change)
  obtain ⟨_,_,_,installed,view⟩ := online.child
  have saved := (cutAt.frame frames).files online.manifest online.catalog
    (installed.installed.offline (request := none) (.inl view)) restart
  have retry := Retry.rejected (change := change) run saved
  exact ⟨⟨h,bound,source bound change,scope⟩,retry,retry.readTwice⟩

end ExperimentalL0.MutationIngressCut
