import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.L0.NativeBridge

namespace ExperimentalL0.NativeBridge

/-- A runtime observation semantics for reached IO actions. Its bind rule
matches the continuation for the actual result, and its error rules stop
the schedule. The premises on component actions are separate from these
monadic rules. -/
structure Reports (σ : Type) where
  relates : {α : Type} → ExceptT String IO α → StorageM σ α → Prop
  observed : {α : Type} → ExceptT String IO α → σ → EStateM.Result String σ α → Prop
  adequate : ∀ {α} {io : ExceptT String IO α} {model s result},
    relates io model → observed io s result → model s = result
  pure : ∀ {α} (x : α), relates (pure x) (pure x)
  bind : ∀ {α β} {a : ExceptT String IO α} {b : StorageM σ α}
    {f : α → ExceptT String IO β} {g : α → StorageM σ β},
    relates a b → (∀ value, relates (f value) (g value)) → relates (a >>= f) (b >>= g)
  throw : ∀ {α : Type} (error : String), relates (throw (α := α) error) (throw error)

structure CallbackReports (r : Reports σ) (io : Components (ExceptT String IO))
    (model : Components (StorageM σ)) : Prop where
  scan : r.relates io.scan model.scan
  append : ∀ batch, r.relates (io.append batch) (model.append batch)
  walOpen : r.relates io.reopenWal model.reopenWal
  manifestOpen : r.relates io.manifest.reopen model.manifest.reopen
  publish : ∀ version, r.relates (io.manifest.publish version) (model.manifest.publish version)
  create : ∀ rows, r.relates (io.tables.create rows) (model.tables.create rows)
  check : ∀ id, r.relates (io.tables.check id) (model.tables.check id)
  lookup : ∀ id key, r.relates (io.tables.lookup id key) (model.tables.lookup id key)

variable {r : Reports σ} {io : Components (ExceptT String IO)} {model : Components (StorageM σ)}

private theorem CallbackReports.checkTables (h : CallbackReports r io model) (ids : List UInt64) :
    r.relates (checkTables io.tables ids) (checkTables model.tables ids) := by
  induction ids with
  | nil => exact r.pure ()
  | cons name ids ih => exact r.bind (h.check name) (fun _ => ih)

private theorem CallbackReports.lookupTables (h : CallbackReports r io model)
    (key : UInt64) (ids : List UInt64) :
    r.relates (lookupTables io.tables key ids) (lookupTables model.tables key ids) := by
  induction ids with
  | nil => exact r.pure none
  | cons name ids ih =>
    refine r.bind (h.lookup name key) (fun result => ?_)
    cases result with
    | none => exact ih
    | some value => exact r.pure (some value)

theorem CallbackReports.write (h : CallbackReports r io model) (session : Session) (change : Change) :
    r.relates (ExperimentalL0.write io session change) (ExperimentalL0.write model session change) := by
  unfold ExperimentalL0.write
  apply r.bind h.scan
  intro view
  by_cases fits : view.tail + 1 < UInt64.size
  · simp only [ite_eq_left fits]
    exact r.bind (h.append (encode change)) (fun _ => r.pure _)
  · simp only [ite_eq_right fits]
    exact r.bind (r.throw _) (fun _ => r.bind (h.append _) (fun _ => r.pure _))

theorem CallbackReports.flush (h : CallbackReports r io model) (session : Session) :
    r.relates (ExperimentalL0.flush io session) (ExperimentalL0.flush model session) := by
  unfold ExperimentalL0.flush
  split
  · exact r.pure _
  · apply r.bind h.scan
    intro view
    by_cases fits : view.tail < UInt64.size
    · simp only [ite_eq_left fits]
      exact r.bind (h.create _) (fun _ => r.bind (h.publish _) (fun _ => r.pure _))
    · simp only [ite_eq_right fits]
      exact r.bind (r.throw _) (fun _ =>
        r.bind (h.create _) (fun _ => r.bind (h.publish _) (fun _ => r.pure _)))

theorem CallbackReports.recover (h : CallbackReports r io model) :
    r.relates (ExperimentalL0.recover io) (ExperimentalL0.recover model) := by
  unfold ExperimentalL0.recover
  apply r.bind h.manifestOpen
  intro version
  apply r.bind h.walOpen
  intro view
  by_cases valid : view.base ≤ version.flushedThrough.toNat ∧ version.flushedThrough.toNat ≤ view.tail
  · cases decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode <;>
      simp only [ite_eq_left valid, decoded]
    · exact r.throw _
    · exact r.bind (h.checkTables _) (fun _ => r.pure _)
  · simp only [ite_eq_right valid]
    apply r.bind (r.throw _)
    intro (_ : Unit)
    cases (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode
    · exact r.throw _
    · exact r.bind (h.checkTables _) (fun _ => r.pure _)

theorem CallbackReports.get (h : CallbackReports r io model) (session : Session) (key : UInt64) :
    r.relates (ExperimentalL0.get io session key) (ExperimentalL0.get model session key) := by
  unfold ExperimentalL0.get
  split
  · exact r.pure _
  · exact r.bind (h.lookupTables _ _) (fun _ => r.pure _)

/-- Specialize the four schedule proofs to the concrete callback record
constructed by `Native.withOpen`. The remaining observation premises are
stated at the individual callback, rather than the LSM operation. -/
theorem native_schedules
    (reports : CallbackReports r (Native.callbackComponents root phase) model) :
    r.relates (recover (Native.callbackComponents root phase)) (recover model) ∧
    (∀ session change, r.relates (write (Native.callbackComponents root phase) session change)
      (write model session change)) ∧
    (∀ session, r.relates (flush (Native.callbackComponents root phase) session) (flush model session)) ∧
    (∀ session key, r.relates (get (Native.callbackComponents root phase) session key)
      (get model session key)) :=
  ⟨reports.recover, reports.write, reports.flush, reports.get⟩

/-- Each attempt may have its own phase cell. Evidence is required only
for the callback record of the attempt that makes this observation. -/
def NativeObserved (r : Reports σ) (model : Components (StorageM σ))
    (call : {m : Type → Type} → [Monad m] → [MonadExceptOf String m] → Components m → m α)
    (s : σ) (result : EStateM.Result String σ α) : Prop :=
  ∃ root phase, CallbackReports r (Native.callbackComponents root phase) model ∧
    r.observed (call (Native.callbackComponents root phase)) s result

private theorem observedWrite (h : NativeObserved r model (fun ops => write ops session change) s result) :
    write model session change s = result := by
  obtain ⟨_, _, callbacks, observed⟩ := h
  exact r.adequate (callbacks.write session change) observed

private theorem observedFlush (h : NativeObserved r model (fun ops => flush ops session) s result) :
    flush model session s = result := by
  obtain ⟨_, _, callbacks, observed⟩ := h
  exact r.adequate (callbacks.flush session) observed

private theorem observedGet (h : NativeObserved r model (fun ops => get ops session key) s result) :
    get model session key s = result := by
  obtain ⟨_, _, callbacks, observed⟩ := h
  exact r.adequate (callbacks.get session key) observed

private theorem observedRecover (h : NativeObserved r model (fun ops => recover ops) s result) :
    recover model s = result := by
  obtain ⟨_, _, callbacks, observed⟩ := h
  exact r.adequate callbacks.recover observed

/-- Observed calls admitted by the wrapper's serialized phase discipline.
A failed read contributes no logical observation. Cleanup and stops frame
the durable selections. Uncertain results end the current session. -/
inductive NativeRun (r : Reports σ) (model : Components (StorageM σ)) (selected : σ → Selected) :
    List Event → Option Session → σ → Prop where
  | initial : Nonempty (Durable (selected s) []) → NativeRun r model selected [] none s
  | written : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => write ops session change) s (.ok next after) →
      NativeRun r model selected (events ++ [.written change]) (some next) after
  | writeUncertain : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => write ops session change) s result →
      NativeRun r model selected (events ++ [.writeUncertain change]) none (reached result)
  | got : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => get ops session key) s (.ok value after) →
      NativeRun r model selected (events ++ [.got key value]) (some session) after
  | readFailed : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => get ops session key) s (.error error after) →
      NativeRun r model selected events (some session) after
  | flushed : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => flush ops session) s (.ok next after) →
      NativeRun r model selected (events ++ [.flushed]) (some next) after
  | flushUncertain : NativeRun r model selected events (some session) s →
      NativeObserved r model (fun ops => flush ops session) s result →
      NativeRun r model selected (events ++ [.flushUncertain]) none (reached result)
  | reopened : NativeRun r model selected events none s →
      NativeObserved r model (fun ops => recover ops) s (.ok session after) →
      NativeRun r model selected (events ++ [.reopened]) (some session) after
  | openFailed : NativeRun r model selected events none s →
      NativeObserved r model (fun ops => recover ops) s (.error error after) →
      NativeRun r model selected (events ++ [.openFailed]) none after
  | stopped : NativeRun r model selected events session s → selected after = selected s →
      NativeRun r model selected (events ++ [.stop]) none after

theorem NativeRun.projects (run : NativeRun r model selected events session s) :
    ObservedRun model selected events session s := by
  induction run with
  | initial durable => exact .initial durable
  | written _ observed ih => exact .written ih (observedWrite observed)
  | writeUncertain _ observed ih => exact .writeUncertain ih (observedWrite observed)
  | got _ observed ih => exact .got ih (observedGet observed)
  | readFailed _ observed ih => exact .readFailed ih (observedGet observed)
  | flushed _ observed ih => exact .flushed ih (observedFlush observed)
  | flushUncertain _ observed ih => exact .flushUncertain ih (observedFlush observed)
  | reopened _ observed ih => exact .reopened ih (observedRecover observed)
  | openFailed _ observed ih => exact .openFailed ih (observedRecover observed)
  | stopped _ frame ih => exact .stopped ih frame

theorem NativeRun.refines (run : NativeRun r model selected events session s)
    (evidence : CallbackEvidence model selected fileBytes) :
    ∃ state, Client.Allows events state ∧ Execution.Represents session (selected s) state :=
  run.projects.refines evidence

end ExperimentalL0.NativeBridge
