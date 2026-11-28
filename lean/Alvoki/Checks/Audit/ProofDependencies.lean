import Lean

open Lean

private def bodyReferences (info : ConstantInfo) : Option (Array Name) :=
  (info.value? (allowOpaque := true)).map Expr.getUsedConstants

/-- Report named declaration references from compiled Lean modules.
Type and body references are direct. The axiom list is transitive.
Review executable outcome coverage and assumptions separately. -/
private def dependencyRow (env : Environment) (info : ConstantInfo) : IO Json := do
  let typeRefs := (info.type.getUsedConstants.map toString).qsort (· < ·)
  let bodyRefs := (bodyReferences info).map fun refs =>
    (refs.map toString).qsort (· < ·)
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

/-- Follow available body references, including references through helper proofs. -/
private def bodyPath (env : Environment) (consumer producer : Name) : Option (List Name) := Id.run do
  let mut pending : Array (Name × List Name) := #[(consumer, [])]
  let mut seen : NameSet := ({} : NameSet).insert consumer
  let mut index := 0
  while h : index < pending.size do
    let (name, parents) := pending[index]
    index := index + 1
    let path := name :: parents
    if name == producer then return some path.reverse
    if let some refs := (env.find? name).bind bodyReferences then
      for ref in refs do
        unless seen.contains ref do
          seen := seen.insert ref
          pending := pending.push (ref, path)
  return none

private def declaration (env : Environment) (moduleName name : String) : IO ConstantInfo := do
  let some info := env.find? name.toName
    | throw (IO.userError s!"unknown compiled declaration '{name}' in the import closure of '{moduleName}'")
  return info

private def usage : IO.Error :=
  IO.userError ("usage: lake env lean --run Alvoki/Checks/Audit/ProofDependencies.lean MODULE " ++
    "(DECLARATION [DECLARATION ...] | --body-path CONSUMER PRODUCER)")

def main (args : List String) : IO Unit := do
  let moduleName :: query := args | throw usage
  -- Imported environment extensions include Lean's recorded axiom summaries.
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := moduleName.toName }] {} (loadExts := true)
  let env := env.setExporting false
  let result ← match query with
    | ["--body-path", consumer, producer] => do
      let consumer ← declaration env moduleName consumer
      let producer ← declaration env moduleName producer
      let path := bodyPath env consumer.name producer.name
      pure [("consumer", toJson consumer.name.toString), ("producer", toJson producer.name.toString),
        ("scope", toJson "available_declaration_bodies"),
        ("body_path", toJson (path.map (List.map Name.toString)))]
    | "--body-path" :: _ | [] => throw usage
    | names => do
      let declarations ← names.mapM fun name => do
        dependencyRow env (← declaration env moduleName name)
      pure [("declarations", toJson declarations)]
  IO.println (Json.mkObj (("import", toJson moduleName) :: result)).pretty
