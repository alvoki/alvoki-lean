import Alvoki.Experiments.L0.ComponentProofs
import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0.Model

private theorem check_bound (faults : Faults) (image : Image) (ids : List UInt64)
    (bound : ids.mapM (fun id => image.catalog[id.toNat]?) = some runs) :
    checkTables (components faults).tables ids image = .ok () image := by
  induction ids generalizing runs with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.mapM_cons] at bound
    cases hit : image.catalog[id.toNat]? with
    | none => simp [hit] at bound
    | some rows =>
      have inside : id.toNat < image.catalog.length := List.getElem?_eq_some_iff.mp hit |>.choose
      cases found : ids.mapM (fun id => image.catalog[id.toNat]?) with
      | none => simp [hit, found] at bound
      | some rest =>
        have tail := ih found
        simp [checkTables, components, tableOps, inside, Bind.bind, EStateM.bind]
        exact tail

theorem recover_healthy (image : Image) (faults : Faults) (d : Durable image.selected history)
    (manifestReady : faults.openManifest = true) (walReady : faults.openWal = true) :
    recover (components faults) image = .ok ⟨image.version, replay d.pending⟩ image := by
  have check := check_bound faults image image.version.tables d.bindings
  simp [recover, components, manifestReady, walReady, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, show image.view.base ≤ image.version.flushedThrough.toNat ∧
      image.version.flushedThrough.toNat ≤ image.view.tail from d.bounds,
    show (image.view.batches.drop (image.version.flushedThrough.toNat - image.view.base)).mapM decode =
      some d.pending from d.replay_pending,
    show checkTables (tableOps faults.create) image.version.tables image = .ok () image from check]

end ExperimentalL0.Model
