import Alvoki.Experiments.L0.ReserveScanCut

namespace ExperimentalL0.ReserveScanCut
open NativeScope (W Ref Wal)
open Lifecycle (Phase)
def applyTail (skip : Session → IO Session) (step : Session → View → IO Session)
    (ref : Ref) : Destination → IO Unit
  | .invalid => throw (IO.userError "L0 requires reopen")
  | .skipped s => fun w => NativeWrite.afterWrite ref (skip s w)
  | .scanned _ (.error e) => fun w => NativeWrite.afterWrite ref (.error e w)
  | .scanned s (.ok view) => fun w => NativeWrite.afterWrite ref (step s view w)

def operation (ref : Ref) (wantScan : Session → Bool) (skip : Session → IO Session)
    (step : Session → View → IO Session) (s : Session) : IO Session :=
  if wantScan s then (do let v ← NativeWrite.borrow ref WalRecoverySlice.Segmented.Native.scan; step s v) else skip s

private theorem scan_resume (s : Session) (h : Wal) (w : W) (f : Destination → IO Unit) :
    (scanning h s).resume f w = match WalRecoverySlice.Segmented.Native.scan h w with
    | .ok v t => f (.scanned s (.ok v)) t
    | .error e t => f (.scanned s (.error e)) t := by
  rw [WalRecoverySlice.Segmented.Native.scan_parts h h.parts.choose_spec.choose_spec]
  simp only [scanning, Program.resume]
  cases (((h.parts.choose.get : BaseIO _) (h.parts.choose_spec.choose.lock w).state).val) <;> rfl

/-- This erases all observed calls to the complete native Cell.update, including
its results, skipped scans, rejected borrows/scan reports and cleanup. -/
theorem resume (ref : Ref) (wantScan : Session → Bool) (skip : Session → IO Session)
    (step : Session → View → IO Session) :
    (program ref wantScan).resume (applyTail skip step ref) =
      (Native.phaseCell ref).update (IO.userError "L0 requires reopen")
        (operation ref wantScan skip step) WalRecoverySlice.Segmented.Native.close := by
  funext w
  simp only [program, Program.resume]
  let a := (ref.get : BaseIO _) w
  have read : (ref.get : IO (Phase Wal)) w = .ok a.val a.state := NativeScope.read_io ref w
  rw [← show a = (ref.get : BaseIO _) w from rfl]
  cases ph : a.val with
  | opening | recovering _ | updating _ | offline =>
    simp only [ph] at read ⊢
    simp only [Phase.beginUpdate, Program.resume, applyTail, Lifecycle.Cell.update, Native.phaseCell,
      Bind.bind, instMonadEIO._aux_13, EST.bind, read]
  | online wal s =>
    have swapped := NativeScope.swap_io ref (.updating wal) a.state
    rw [ph] at read
    rw [NativeWrite.update_started ref _ read swapped]
    simp only [Phase.beginUpdate, Program.resume, operation]
    let b := (ref.swap (.updating wal) : BaseIO _) a.state
    cases wanted : wantScan s with
    | false => rfl
    | true =>
      simp only [ite_true, Program.resume]
      let c := (ref.get : BaseIO _) b.state
      have ran : (ref.get : IO (Phase Wal)) b.state = .ok c.val c.state := NativeScope.read_io ref b.state
      change Program.resume _ (match c.val.wal with | none => _ | some _ => _) c.state =
        NativeWrite.afterWrite ref ((NativeWrite.borrow ref WalRecoverySlice.Segmented.Native.scan >>= step s) b.state)
      simp only [NativeWrite.borrow, Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
      cases c.val.wal with
      | none => rfl
      | some h =>
        rw [scan_resume]
        simp only
        cases WalRecoverySlice.Segmented.Native.scan h c.state <;> rfl

def flushRemainder (root : System.FilePath) (s : Session) (view : View) : IO Session := do
  unless view.tail < UInt64.size do throw (IO.userError "absolute WAL position exhausted")
  let id ← NativeFlush.createTable root s.mem.toList
  let proposal : L0Manifest.Version := ⟨id :: s.version.tables, view.tail.toUInt64⟩
  NativeFlush.publish root proposal
  return ⟨proposal, ∅⟩

/-- Replacing the terminal stubs by the remaining table/manifest action gives the
entire concrete public flush, including both its result and the returned world. -/
theorem flush (binding : Native.Handle.AtRoot h root ref) :
    (program ref fun s => !s.mem.isEmpty).resume (applyTail pure (flushRemainder root) ref) = Native.flush h := by
  rw [resume, Native.flush_atRoot binding]
  congr 1
  funext s
  rw [NativeFlush.atRoot]
  have scan : Native.checked (Native.callbackComponents root ref).scan =
      NativeWrite.borrow ref WalRecoverySlice.Segmented.Native.scan := by
    unfold Native.callbackComponents Lifecycle.Cell.components Native.storageCallbacks
    apply NativeWrite.checked_borrow
  cases h : s.mem.isEmpty <;> simp [operation, h, scan, flushRemainder]

end ExperimentalL0.ReserveScanCut
