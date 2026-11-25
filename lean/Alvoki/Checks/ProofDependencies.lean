import Lean

open Lean

/-- Report named declaration references from compiled Lean modules.
Type and body references are direct. The axiom list is transitive.
Review executable outcome coverage and assumptions separately. -/
private def dependencyRow (env : Environment) (info : ConstantInfo) : IO Json := do
  let typeRefs := (info.type.getUsedConstants.map toString).qsort (· < ·)
  let bodyRefs := (info.value? (allowOpaque := true)).map fun body =>
    (body.getUsedConstants.map toString).qsort (· < ·)
  let module := (env.getModuleIdxFor? info.name).bind (env.header.moduleNames[·]?)
  let axioms ← (collectAxioms info.name : CoreM (Array Name)).toIO'
    { fileName := "ProofDependencies", fileMap := default } { env := env }
  return Json.mkObj [
    ("name", toJson info.name.toString),
    ("module", toJson (module.map toString)),
    ("type_refs", toJson typeRefs),
    ("body_status", toJson (if bodyRefs.isSome then "available" else "unavailable")),
    ("body_refs", toJson bodyRefs),
    ("transitive_axioms", toJson ((axioms.map toString).qsort (· < ·)))]

def main (args : List String) : IO Unit := do
  let moduleName :: declaration :: remaining := args
    | throw (IO.userError "usage: lake env lean --run Alvoki/Checks/ProofDependencies.lean MODULE DECLARATION [DECLARATION ...]")
  -- Imported environment extensions include Lean's recorded axiom summaries.
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := moduleName.toName }] {} (loadExts := true)
  let env := env.setExporting false
  let declarations ← (declaration :: remaining).mapM fun name => do
    let some info := env.find? name.toName
      | throw (IO.userError s!"unknown compiled declaration '{name}' in the import closure of '{moduleName}'")
    dependencyRow env info
  IO.println (Json.mkObj [("import", toJson moduleName), ("declarations", toJson declarations)]).pretty
