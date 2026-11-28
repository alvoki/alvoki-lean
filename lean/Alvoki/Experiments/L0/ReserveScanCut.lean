import Alvoki.Experiments.L0.NativeFlush
import Alvoki.Experiments.L0.MutationExitCut

namespace ExperimentalL0.ReserveScanCut
open NativeScope (W Ref Wal)
open Lifecycle (Phase)
open MutationExitCut (Tail)
/-- The WAL scan takes the actual private mutex, reads its phase and releases
the mutex in the finally block, including on a phase error. -/
noncomputable def walScan (wal : Wal) : Tail :=
  let cell := wal.parts.choose
  let mutex := wal.parts.choose_spec.choose
  .call mutex.lock fun _ => .call cell.get fun _ => .call mutex.unlock fun _ => .done

/-- Only the observed phase read selects a reservation; only the real nonempty
memtable starts a scan, on the WAL obtained by the later borrow. -/
noncomputable def reserveScan (ref : Ref) (wantScan : Session → Bool) : Tail :=
  .call ref.get fun ph => match ph.beginUpdate with
  | none => .done
  | some (next, s) => .call (ref.swap next) fun _ =>
    if wantScan s then .call ref.get fun read => match read.wal with
      | none => .done
      | some wal => walScan wal
    else .done

theorem walScan_state (wal : Wal) (w : W) :
    ((walScan wal).run w).state = WalRecoverySlice.Segmented.Native.scanWorld wal w := by
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
  unfold reserveScan
  simp only [atCall, phase, Phase.beginUpdate]
  cases scan : wantScan s with
  | false => rfl
  | true =>
    have actual := borrow scan
    rw [NativeScope.read_io] at actual
    have visible := (EST.Out.ok.inj actual).1
    simp only [ite_true, atCall]
    change ((match ((ref.get : BaseIO _) (NativeFlush.hidden ref wal start)).val.wal with
      | none => Tail.done | some h => walScan h).run _).state = _
    rw [visible]
    exact walScan_state wal _

end ExperimentalL0.ReserveScanCut
