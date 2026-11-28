# Proof audits

[The axiom policy](AxiomPolicy.lean) enforces the repository's allowed
transitive axioms for the declarations named by the
[component checks](../../../../scripts/reproduce.sh). Use Lean's
`#print axioms NAME` for an ad hoc query. Coverage starts at the declarations
selected by each check. For example, the Manifest round-trip proof uses
`word_encodeWords`. The SSTable check names `splitByte_joinBytes` directly
to cover the inverse byte-lane direction.

## Trace a consumer to a producer

Run the [dependency probe](ProofDependencies.lean) from `lean/` after building
the module to inspect. Passing declaration names prints their direct type
and body references and transitive axioms. Pass `--body-path` with two names
to find a shortest chain of references in available declaration bodies.

```sh
lake build Alvoki.Checks.Tests.SSTableProducer
lake env lean --run Alvoki/Checks/Audit/ProofDependencies.lean \
  Alvoki.Checks.Tests.SSTableProducer --body-path \
  SSTableProducerCheck.checkedLookup \
  ImmutableSSTable.Unified.Image.openCheckedWith_represents_at
```

The path goes through `buildFileWith_open_represents`. To check which
parts of the writer's postcondition this proof consumes, read its source
or use `set_option pp.proofs true in #print` on the theorem. The proof uses
the returned row count, the writer's `Image`, the inode binding and the
durable bytes. The initial empty binding, flushed flag and model-builder
equality are skipped by this consumer. Other consumers can still rely
on those fields.
[SSTable writer-reader proof](../../Experiments/SSTable/Proofs/UnifiedNativeEndToEnd.lean)

A null path means no chain was found in the available bodies. Definitions
can be reduced during elaboration and some bodies may be unavailable.
For example, `uncertainResult` has no body path to `buildFileWith_syncError`.
The fixture proves its concrete outcome by reduction. Use the returned
references to locate a proof step, then review the reached state, premises
and failure continuations against the component contract.
[SSTable producer fixture](../Tests/SSTableProducer.lean)

## Check the review scope

- For a suspected superseded declaration, search current and active
  branches, then remove it in a scratch candidate and rebuild and check
  the affected consumers. The result describes the checked roots.
- To inspect direct imports, run `lake env lean --src-deps PATH.lean`.
  For transitive imports, inspect Lean's environment. For example, this
  probe checks the SSTable native entry point against the local proof
  modules, including those imported indirectly.

```lean
import Alvoki.Experiments.SSTable.UnifiedNative
import Lean

open Lean Elab Command
run_cmd do
  for name in (← getEnv).allImportedModuleNames do
    if Name.isPrefixOf `Alvoki.Experiments.SSTable.Proofs name ||
        name == `Alvoki.Kernel.BlockContracts then
      throwError "proof module in native import closure: {name}"
```
