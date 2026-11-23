import Lean

open Lean Elab Command

/-- Reject transitive dependencies outside the repository's proof policy. -/
elab "#check_axioms " id:ident : command => withRef id do
  let constants ← liftCoreM <| realizeGlobalConstWithInfos id
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for name in constants do
    let unexpected := (← collectAxioms name).filter (fun axiomName => axiomName ∉ allowed)
    unless unexpected.isEmpty do
      throwError m!"unexpected axiom dependencies for '{name}': {unexpected.toList}"
