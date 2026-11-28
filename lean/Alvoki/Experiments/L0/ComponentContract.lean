import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0
open WalRecoverySlice.Segmented

/-- Durable selections visible to the LSM. The adapter may carry private
state, including open descriptors and recovery progress. -/
structure Selected where
  view : Contract.View
  version : L0Manifest.Version
  tables : Catalog

def Selected.append (s : Selected) (batch : Contract.Batch) : Selected :=
  {s with view := s.view.append batch}

def Selected.publish (s : Selected) (version : L0Manifest.Version) : Selected :=
  {s with version}

abbrev StorageM (σ : Type) := EStateM String σ

/-- Recovery reads one WAL view, one manifest, and the manifest's tables. -/
structure RecoveryEffects (ops : Components (StorageM σ)) (selected : σ → Selected) : Prop where
  reopenWal : ∀ s, match ops.reopenWal s with
    | .ok view after => view = (selected s).view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  reopenManifest : ∀ s, match ops.manifest.reopen s with
    | .ok version after => version = (selected s).version ∧ selected after = selected s
    | .error _ after => selected after = selected s
  check : ∀ s id, match ops.tables.check id s with
    | .ok _ after | .error _ after => selected after = selected s

/-- Flush scans the WAL, creates a table, and publishes the new manifest. -/
structure FlushEffects (ops : Components (StorageM σ)) (selected : σ → Selected) : Prop where
  scan : ∀ s, match ops.scan s with
    | .ok view after => view = (selected s).view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  create : ∀ s rows, Rows.Ordered rows →
    match ops.tables.create rows s with
    | .ok id after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Created (selected after).tables id rows
    | .error _ after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Preserves (selected after).tables
  publish : ∀ s version, version.Valid → match ops.manifest.publish version s with
    | .ok _ after => selected after = (selected s).publish version
    | .error _ after => selected after = selected s ∨ selected after = (selected s).publish version

/-- The component model also interprets successful and uncertain appends. -/
structure ComponentEffects (ops : Components (StorageM σ)) (selected : σ → Selected)
    : Prop extends RecoveryEffects ops selected, FlushEffects ops selected where
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => selected after = (selected s).append batch
    | .error _ after => selected after = selected s ∨ selected after = (selected s).append batch

/-- Reads add the table lookup law. Recovery and mutation do not require it. -/
structure ComponentLaws (ops : Components (StorageM σ)) (selected : σ → Selected)
    : Prop extends ComponentEffects ops selected where
  lookup : ∀ s id key rows, (selected s).tables id = some rows →
    match ops.tables.lookup id key s with
    | .ok result after => result = lookupRows rows key ∧ selected after = selected s
    | .error _ after => selected after = selected s

end ExperimentalL0
