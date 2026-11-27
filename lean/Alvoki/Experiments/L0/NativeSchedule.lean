import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.L0.NativeBridge

namespace ExperimentalL0.NativeBridge

/-- A runtime observation semantics for reached IO actions. Its bind rule
matches the continuation for the actual result, and its error rules stop
the schedule. The premises on component actions are separate from these
monadic rules. -/
structure Reports (σ : Type) where
  relates : {α : Type} → ExceptT String IO α → StorageM σ α → Prop
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

end ExperimentalL0.NativeBridge
