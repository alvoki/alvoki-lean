import Alvoki.Experiments.WAL.Proofs.ConcreteAppend

namespace WalRecoverySlice.SingleFile.ConcreteAppendCut
open ConcreteRecovery ConcreteAppend Persistence

/-- The actual syscall reached within one append instruction. In the
marker path, the writer rewinds this particular marker before writing.
A stopped flush is reached only after its own write returned. -/
inductive Site (files : AppendFiles IO.FS.Handle) : Op → W → IO Unit → W → Prop where
  | data : Site files (.append bytes) w (files.writer.write ⟨bytes.toArray⟩) w
  | dataFlush : files.writer.write ⟨bytes.toArray⟩ w = .ok () t →
      Site files (.append bytes) w files.writer.flush t
  | dataSync : Site files .syncData w (Internal.syncHandle files.writer) w
  | rewind : files.markers = some (a,b) → h = (if slot == 0 then a else b) →
      Site files (.writeMarker slot bytes) w h.rewind w
  | marker : files.markers = some (a,b) → h = (if slot == 0 then a else b) →
      h.rewind w = .ok () t → Site files (.writeMarker slot bytes) w (h.write ⟨bytes.toArray⟩) t
  | markerFlush : files.markers = some (a,b) → h = (if slot == 0 then a else b) →
      h.rewind w = .ok () t → h.write ⟨bytes.toArray⟩ t = .ok () u →
      Site files (.writeMarker slot bytes) w h.flush u
  | markerSync : files.markers = some (a,b) → h = (if slot == 0 then a else b) →
      Site files (.syncMarker slot) w (Internal.syncHandle h) w

/-- The source alone determines the prefix. There is no persistence report
in the witness and the interrupted instruction has no return-value premise. -/
inductive Issued (actual : Ops F) (entry : Program α) (start : W) : Program α → W → Type where
  | start : Issued actual entry start entry start
  | next {op : Op} {cont : op.Result → Program α} {value : op.Result} :
    Issued actual entry start (.call op cont) w →
    (op.eval actual).run w = .ok (.ok value) t → Issued actual entry start (cont value) t

theorem Issued.resume {start : W} (path : Issued actual entry start rest w) :
    (entry.eval actual).run start = (rest.eval actual).run w := by
  induction path with
  | start => rfl
  | next _ ran ih =>
    rw [ih, Program.eval]
    rw [ExceptT.run_bind]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]

/-- At each issued prefix the actual public child append has already
poisoned its phase. The residual worker retains its normal completion
and error paths; the cut makes no assumption about either outcome. -/
theorem Issued.append {start : W} (bound : h.Assembled p cell mutex)
    (active : (readAt cell mutex start).val = .active fd files cursor history)
    (path : Issued (nativeOps files) (appendBatch programOps p cursor batch)
      (poisonAt cell fd mutex start) rest w) :
    SingleFile.append h batch start =
      match (rest.eval (nativeOps files)).run w with
      | .error e t => .error e (mutex.unlock t).state
      | .ok (.error err) t => .error (IO.userError err) (mutex.unlock t).state
      | .ok (.ok result) t => .ok () (mutex.unlock (installAt cell fd files result (history ++ [batch]) t)).state := by
  have ran := path.resume
  rw [eval_append (nativeOps files) p cursor batch (fun _ _ => rfl)] at ran
  rw [append_active_run bound start active, ← ran]
  rfl

private theorem Prefix.modelRun (path : Prefix actual model entry start initial rest w current) :
    (entry.eval model).run initial = (rest.eval model).run current := by
  induction path with
  | initial => rfl
  | next _ _ ran ih =>
    rw [ih, Program.eval]
    rw [ExceptT.run_bind]
    simp only [Bind.bind, EStateM.bind, ran]

/-- Pair only the primitive calls which returned strictly before the cut.
The local report for the interrupted operation is allowed to differ from
the report it would have made if it had returned. -/
inductive Reports {actual : Ops F} (model : Ops M) {entry : Program α} {start : W} (initial : Image) :
    {rest : Program α} → {w : W} → Issued actual entry start rest w → Image → Prop where
  | initial : Reports model initial .start initial
  | next {op : Op} {cont : op.Result → Program α} {x : op.Result}
      {prior : Issued actual entry start (.call op cont) w}
      {ran : (op.eval actual).run w = .ok (.ok x) t} :
    Reports model initial prior i → (op.eval model).run i = .ok (.ok x) u →
    Reports model initial (prior.next ran) u

/-- Apply the primitive reports only to calls which strictly preceded
this cut. The concrete world-to-file projection produces each successive
model image without a trace-matching premise on the append. -/
def Issued.Earlier {actual : Ops F} {entry : Program α} {origin : W}
    {rest : Program α} {w : W} (path : Issued actual entry origin rest w)
    (P : (op : Op) → op.Result → W → W → Prop) : Prop :=
  match path with
  | .start => True
  | @Issued.next _ _ _ _ before after op _ value earlier _ =>
      earlier.Earlier P ∧ P op value before after

theorem Reports.of_earlier {actual : Ops F} {entry : Program α} {origin : W}
    {rest : Program α} {w : W} (path : Issued actual entry origin rest w)
    (model : Ops M) (file : W → Image)
    (returns : path.Earlier (fun op value a b => (op.eval model).run (file a) = .ok (.ok value) (file b))) :
    Reports model (file origin) path (file w) := by
  induction path with
  | start => exact .initial
  | next earlier ran ih => exact .next (ih returns.1) returns.2

private theorem Reports.paired {initial : Image} {path : Issued actual entry start rest w}
    (reports : Reports model initial path i) : Prefix actual model entry start initial rest w i := by
  induction reports with
  | initial => exact .initial
  | next _ sent ih => exact ih.next ‹_› sent

/-- PR #26's crash producer consumes the report of the one syscall
actually interrupted. The interrupted result is a model abort only; the
real write/rewind/flush/fsync need never return. -/
theorem interrupted {p : Policy} {batch : Bytes} {files : AppendFiles IO.FS.Handle}
    (report : AppendReports p (historyCursor history) batch)
    (path : Issued (nativeOps files) (appendBatch programOps p (historyCursor history) batch) start (.call op k) w)
    (prior : Reports (modeledOps report) initial path atOp)
    (site : Site files op w action issued) (stop : IO Unit → W → Image → Prop)
    (stopped : stop action issued cut)
    (primitive : Site files op w action issued → ∀ after, stop action issued after → (op.eval (modeledOps report)).run atOp = .error () after)
    (entry : Ready p initial history) (clean : initial.powerLoss = initial)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length < 255) (size : batch.length ≤ 32) :
    Dirty p history (some batch) cut ∧ (p = .logOnly → cut.MarkersSettled) := by
  have atLeaf := primitive site cut stopped
  have ran := Prefix.modelRun prior.paired
  rw [eval_append (modeledOps report) p (historyCursor history) batch (fun _ _ => rfl)] at ran
  unfold Program.eval at ran
  rw [ExceptT.run_bind] at ran
  simp only [Bind.bind, EStateM.bind, atLeaf] at ran
  have result := appendPrimitive_refines report.effects report.writebacks p initial history batch report.torn
    entry clean bounded fits size
  change Dirty p history (some batch) (reached ((appendBatch (modeledOps report) p (historyCursor history) batch).run initial)) ∧ _ at result
  rw [ran] at result
  exact ⟨result.1, result.2.1⟩

end WalRecoverySlice.SingleFile.ConcreteAppendCut
