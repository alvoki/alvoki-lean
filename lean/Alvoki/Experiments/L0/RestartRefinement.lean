import Alvoki.Experiments.L0.DurableCatalog
import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0

/-- Before manifest publication, the old selection is still a recovery
candidate. A reached prefix can leave an orphan without changing the history
or the physical bindings the old manifest needs. -/
theorem retainRecoverySelection {selected : σ → Selected} {ns : TableNamespace σ}
    (prior : Durable (selected before) history)
    (catalog : ns.Represents before (selected before).tables)
    (same : selected after = selected before)
    (keeps : ns.Keeps before after (selected before).tables) :
    Nonempty (Durable (selected after) history) ∧
      ns.Represents after (selected after).tables := by
  rw [same]
  exact ⟨⟨prior⟩, catalog.frame keeps⟩

private theorem checksKeepCatalog {ops : Tables (StorageM σ)} {ns : TableNamespace σ}
    (keeps : ∀ s id, match ops.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after tables) (ids : List UInt64) (s : σ) :
    match checkTables ops ids s with
    | .ok _ after | .error _ after => ns.Keeps s after tables := by
  induction ids generalizing s with
  | nil => exact fun _ _ _ _ _ name content => ⟨name, content⟩
  | cons id ids ih =>
    have first := keeps s id
    cases checked : ops.check id s with
    | error error after =>
      simpa [checkTables, Bind.bind, EStateM.bind, checked] using first
    | ok result middle =>
      rw [checked] at first
      have rest := ih middle
      cases ran : checkTables ops ids middle <;>
        rw [ran] at rest <;>
        simpa [checkTables, Bind.bind, EStateM.bind, checked, ran] using first.trans rest

/-- Every path through public recover preserves the durable table namespace
when each reached manifest, WAL and scoped check call frames it. -/
theorem recoverKeepsCatalog {ops : Components (StorageM σ)} {ns : TableNamespace σ}
    (manifest : ∀ s, match ops.manifest.reopen s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (wal : ∀ s, match ops.reopenWal s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (check : ∀ s id, match ops.tables.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after tables) (s : σ) :
    match recover ops s with
    | .ok _ after | .error _ after => ns.Keeps s after tables := by
  have opened := manifest s
  cases manifestRan : ops.manifest.reopen s with
  | error error after =>
    simpa [recover, Bind.bind, EStateM.bind, manifestRan] using opened
  | ok version middle =>
    rw [manifestRan] at opened
    have recovered := wal middle
    cases walRan : ops.reopenWal middle with
    | error error after =>
      rw [walRan] at recovered
      simpa [recover, Bind.bind, EStateM.bind, manifestRan, walRan] using opened.trans recovered
    | ok view checked =>
      rw [walRan] at recovered
      have header := opened.trans recovered
      by_cases bounds : view.base ≤ version.flushedThrough.toNat ∧
          version.flushedThrough.toNat ≤ view.tail
      · cases decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode with
        | none =>
          simp only [recover, Bind.bind, EStateM.bind, manifestRan, walRan, bounds, decoded]
          exact header
        | some rows =>
          have all := checksKeepCatalog check version.tables checked
          cases tableRan : checkTables ops.tables version.tables checked <;>
            rw [tableRan] at all <;>
            simpa [recover, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
              manifestRan, walRan, bounds, decoded, tableRan] using header.trans all
      · simp only [recover, Bind.bind, EStateM.bind, manifestRan, walRan, bounds, ite_false]
        exact header

/-- Supply the reached catalog on either public recovery outcome. -/
theorem recoverCatalog
    {ops : Components (StorageM σ)} {selected : σ → Selected} {ns : TableNamespace σ}
    (laws : RecoveryEffects ops selected) (d : Durable (selected s) history)
    (prior : ns.Represents s (selected s).tables)
    (manifest : ∀ state, match ops.manifest.reopen state with
      | .ok _ after | .error _ after => ns.Keeps state after (selected s).tables)
    (wal : ∀ state, match ops.reopenWal state with
      | .ok _ after | .error _ after => ns.Keeps state after (selected s).tables)
    (check : ∀ state id, match ops.tables.check id state with
      | .ok _ after | .error _ after => ns.Keeps state after (selected s).tables) :
    match recover ops s with
    | .ok _ after | .error _ after => ns.Represents after (selected after).tables := by
  have physical := recoverKeepsCatalog manifest wal check s
  have logical := recover_refines laws s d
  cases ran : recover ops s with
  | ok session after =>
    rw [ran] at physical logical
    change ns.Represents after (selected after).tables
    exact logical.1.symm ▸ prior.frame physical
  | error error after =>
    rw [ran] at physical logical
    change ns.Represents after (selected after).tables
    exact logical.symm ▸ prior.frame physical

end ExperimentalL0
