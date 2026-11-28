import Alvoki.Experiments.L0.NativeFlush
import Alvoki.Experiments.L0.MutationExitCut

namespace ExperimentalL0.ReserveScanCut
open NativeScope (W Ref Wal)
open Lifecycle (Phase)
open MutationExitCut (Tail)
abbrev View := WalRecoverySlice.Segmented.Contract.View

/-- A leaf resumes the native updating action with its actual scan result.
Phase errors before and after reservation have different cleanup. -/
inductive Destination where
  | invalid
  | skipped (s : Session)
  | scanned (s : Session) (report : Except IO.Error View)

inductive Program where
  | reached (d : Destination)
  | call {α : Type} (op : BaseIO α) (k : α → Program)

def Program.path : Program → Tail
  | .reached _ => .done
  | .call op k => .call op (fun x => (k x).path)

def Program.resume (k : Destination → IO Unit) : Program → IO Unit
  | .reached d => k d
  | .call op rest => fun w => let x := op w; (rest x.val).resume k x.state

def reported : WalRecoverySlice.Segmented.Native.Phase WalRecoverySlice.Segmented.Native.Store → Except IO.Error View
  | .ready _ s => .ok s.view
  | .poisoned _ => .error (IO.userError "segmented WAL requires reopen")
  | .closed => .error (IO.userError "segmented WAL closed")

noncomputable def scanning (wal : Wal) (s : Session) : Program :=
  let cell := wal.parts.choose
  let mutex := wal.parts.choose_spec.choose
  .call mutex.lock fun _ => .call cell.get fun ph => .call mutex.unlock fun _ => .reached (.scanned s (reported ph))

/-- Only the observed phase read selects a reservation. The optional WAL borrow
identifies the private phase reference and mutex for the three scan calls. -/
noncomputable def program (ref : Ref) (wantScan : Session → Bool) : Program :=
  .call ref.get fun ph => match ph.beginUpdate with
  | none => .reached .invalid
  | some (next, s) => .call (ref.swap next) fun _ =>
    if wantScan s then .call ref.get fun read => match read.wal with
      | none => .reached (.scanned s (.error (IO.userError "L0 cannot use the WAL in this phase")))
      | some wal => scanning wal s
    else .reached (.skipped s)

noncomputable def reserveScan (ref : Ref) (wantScan : Session → Bool) : Tail :=
  (program ref wantScan).path

theorem scanning_state (wal : Wal) (s : Session) (w : W) :
    ((scanning wal s).path.run w).state = WalRecoverySlice.Segmented.Native.scanWorld wal w := by
  let cell := wal.parts.choose
  let mutex := wal.parts.choose_spec.choose
  have parts : wal.Parts cell mutex := wal.parts.choose_spec.choose_spec
  unfold WalRecoverySlice.Segmented.Native.scanWorld
  rw [parts.1, parts.2]
  rfl

private theorem atCall (op : BaseIO α) (k : α → Tail) (w : W) :
    (Tail.call op k).run w = (k (op w).val).run (op w).state := by rw [Tail.run]; rfl

/-- The path only requires observations from already completed calls. For the
full returning execution, reservation and the optional WAL borrow fix the
world of the following guard or store without running it. -/
theorem state (wantScan : Session → Bool)
    (read : (ref.get : IO (Phase Wal)) start = .ok (.online wal s) ((ref.get : BaseIO _) start).state)
    (borrow : wantScan s = true → (ref.get : IO (Phase Wal)) (NativeFlush.hidden ref wal start) =
      .ok (.updating wal) ((ref.get : BaseIO _) (NativeFlush.hidden ref wal start)).state) :
    ((reserveScan ref wantScan).run start).state =
      if wantScan s then NativeWrite.guardWorld ref wal start else NativeFlush.hidden ref wal start := by
  rw [NativeScope.read_io] at read
  have phase := (EST.Out.ok.inj read).1
  unfold reserveScan program
  simp only [Program.path, atCall, phase, Phase.beginUpdate]
  cases scan : wantScan s with
  | false => rfl
  | true =>
    have actual := borrow scan
    rw [NativeScope.read_io] at actual
    have visible := (EST.Out.ok.inj actual).1
    simp only [ite_true, Program.path, atCall]
    change ((match ((ref.get : BaseIO _) (NativeFlush.hidden ref wal start)).val.wal with
      | none => Program.reached (.scanned s (.error _)) | some h => scanning h s).path.run _).state = _
    rw [visible]
    exact scanning_state wal s _

end ExperimentalL0.ReserveScanCut
