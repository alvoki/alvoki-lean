import Alvoki.Experiments.L0.ReserveScanSource

namespace ExperimentalL0
open NativeScope (W Ref Wal)

/-- Ordinary execution with unreturned interruption observations. Bind starts its
continuation only on an actual successful return, at its actual reached world. -/
structure ObservedIO (α : Type) where
  run : IO α
  cut : W → W → Prop

instance : Monad ObservedIO where
  pure x := ⟨pure x, fun w t => t = w⟩
  bind a f := ⟨a.run >>= fun x => (f x).run, fun w t =>
    a.cut w t ∨ ∃ x u, a.run w = .ok x u ∧ (f x).cut u t⟩

/-- An error also invokes the result handler when handling store returns and
finalizers. A stop inside the first action never invokes that handler. -/
def ObservedIO.thenResult (a : ObservedIO α) (k : Except IO.Error α → ObservedIO β) : ObservedIO β :=
  ⟨fun w => let r := a.run.toBaseIO w; (k r.val).run r.state,
    fun w t => a.cut w t ∨ (k (a.run.toBaseIO w).val).cut (a.run.toBaseIO w).state t⟩

namespace ReserveScanCut

def Program.eval : Program → BaseIO Destination
  | .reached d => pure d
  | .call op k => fun w => let r := op w; (k r.val).eval r.state

private def primitive (valid : W → Prop) (stop : MutationExitCut.LeafStop) (op : BaseIO α) : ObservedIO α :=
  ⟨fun w => .ok (op w).val (op w).state, fun w t => (t = w ∨ stop op w t ∨ t = (op w).state) ∧ valid t⟩

def Program.observeIf (p : Program) (valid : W → Prop) (stop : MutationExitCut.LeafStop)
    (k : Destination → ObservedIO Unit) : ObservedIO Unit :=
  match p with
  | .reached d => k d
  | .call op next => (primitive valid stop op) >>= fun x => (next x).observeIf valid stop k

theorem Program.observeIf_run (p : Program) (valid : W → Prop) (stop : MutationExitCut.LeafStop)
    (k : Destination → ObservedIO Unit) : (p.observeIf valid stop k).run = p.resume (fun d => (k d).run) := by
  induction p with
  | reached => rfl
  | call op next ih =>
    funext w
    change ((next (op w).val).observeIf valid stop k).run (op w).state = _
    rw [ih]
    rfl

private theorem cutStep (op : BaseIO α) (k : α → MutationExitCut.Tail)
    (rest : MutationExitCut.Cut stop (k (op w).val) (op w).state t) :
    MutationExitCut.Cut stop (.call op k) w t := by
  cases rest with
  | boundary path => exact .boundary (.step path)
  | during path cut => exact .during (.step path) cut

/-- No decomposition of the observer's cut is assumed. Recursing on the actual
returned operands classifies every intermediate primitive or hands the remaining
cut to the reached terminal continuation. -/
theorem Program.classifyIf (p : Program) (valid : W → Prop) (stop : MutationExitCut.LeafStop)
    (k : Destination → ObservedIO Unit) (raw : (p.observeIf valid stop k).cut w t) :
    (MutationExitCut.Cut stop p.path w t ∧ valid t) ∨ (k (p.eval w).val).cut (p.eval w).state t := by
  induction p generalizing w with
  | reached d => exact .inr raw
  | call op next ih =>
    change ((_ ∨ stop op w t ∨ _) ∧ valid t) ∨ ∃ x u, EST.Out.ok (ε := IO.Error) (op w).val (op w).state = .ok x u ∧ _ at raw
    rcases raw with ⟨(rfl | during | rfl), fact⟩ | ⟨_, _, ran, later⟩
    · exact .inl ⟨.boundary .here, fact⟩
    · exact .inl ⟨.during .here during, fact⟩
    · exact .inl ⟨.boundary (.step .here), fact⟩
    · cases ran
      exact (ih _ later).imp_left fun h => ⟨cutStep op _ h.1, h.2⟩

abbrev Program.observe (p : Program) := p.observeIf (fun _ => True)

theorem Program.observe_run (p : Program) (stop : MutationExitCut.LeafStop) (k : Destination → ObservedIO Unit) :
    (p.observe stop k).run = p.resume (fun d => (k d).run) := p.observeIf_run _ stop k

theorem Program.classify (p : Program) (stop : MutationExitCut.LeafStop) (k : Destination → ObservedIO Unit)
    (raw : (p.observe stop k).cut w t) :
    MutationExitCut.Cut stop p.path w t ∨ (k (p.eval w).val).cut (p.eval w).state t :=
  (p.classifyIf _ stop k raw).imp_left And.left

theorem Program.resume_eval (p : Program) (k : Destination → IO Unit) (w : W) :
    p.resume k w = k (p.eval w).val (p.eval w).state := by
  induction p generalizing w with
  | reached => rfl
  | call op next ih => exact ih (op w).val (op w).state

private theorem scanEval (wal : Wal) (s : Session) (w : W) :
    (scanning wal s).eval w =
      let r := (WalRecoverySlice.Segmented.Native.scan wal).toBaseIO w
      ⟨.scanned s r.val, r.state⟩ := by
  simp only [EIO.toBaseIO, WalRecoverySlice.Segmented.Native.scan_parts wal wal.parts.choose_spec.choose_spec,
    scanning, Program.eval]
  cases ((wal.parts.choose.get : BaseIO _) (wal.parts.choose_spec.choose.lock w).state).val <;> rfl

theorem destination (wantScan : Session → Bool)
    (read : (ref.get : IO (Lifecycle.Phase Wal)) start = .ok (.online wal s) ((ref.get : BaseIO _) start).state)
    (borrow : wantScan s = true → (ref.get : IO (Lifecycle.Phase Wal)) (NativeFlush.hidden ref wal start) =
      .ok (.updating wal) ((ref.get : BaseIO _) (NativeFlush.hidden ref wal start)).state)
    (scan : wantScan s = true → NativeWrite.borrow ref WalRecoverySlice.Segmented.Native.scan
      (NativeFlush.hidden ref wal start) = .ok view (NativeWrite.guardWorld ref wal start)) :
    ((program ref wantScan).eval start) = if wantScan s then
      ⟨.scanned s (.ok view), NativeWrite.guardWorld ref wal start⟩
      else ⟨.skipped s, NativeFlush.hidden ref wal start⟩ := by
  rw [NativeScope.read_io] at read
  simp only [program, Program.eval, (EST.Out.ok.inj read).1, Lifecycle.Phase.beginUpdate]
  cases b : wantScan s with
  | false => rfl
  | true =>
    have bran := borrow b
    have ran := scan b
    rw [NativeWrite.borrow_run _ bran] at ran
    rw [NativeScope.read_io] at bran
    simp only [ite_true, Program.eval]
    change (match ((ref.get : BaseIO _) (NativeFlush.hidden ref wal start)).val.wal with
      | none => Program.reached (.scanned s (.error _)) | some h => scanning h s).eval _ = _
    rw [(EST.Out.ok.inj bran).1]
    change (scanning wal s).eval _ = _
    rw [scanEval]
    unfold NativeFlush.hidden at ran
    simp only [EIO.toBaseIO, ran]

end ReserveScanCut
end ExperimentalL0
