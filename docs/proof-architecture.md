# Proof design

Alvoki now develops storage components independently. Keep a component's public contract, executable producer, proof, native adapter, and open assumptions close enough that a caller can see where each guarantee comes from. The component guides link these pieces:

- [Segmented WAL](../lean/Alvoki/Experiments/WAL/Segmented/README.md)
- [Durable blob](../lean/Alvoki/Experiments/DurableBlob/README.md)
- [Manifest](../lean/Alvoki/Experiments/Manifest/README.md)
- [Immutable SSTable](../lean/Alvoki/Experiments/SSTable/README.md)

## A useful proof path

1. State the observable behavior at the caller boundary, including errors and uncertain outcomes.
2. Write down the admitted filesystem effects and the ownership, descriptor, and durability assumptions supplied by the environment.
3. State the final theorem that the caller needs on the executable path and [audit its premises](#premise-audit). Work backward from the conclusion. Add each local lemma to close an identified gap, and compose it into that theorem so the remaining premises are visible.
4. Challenge the contract with a disallowed behavior and a required counterexample. For a WAL, lose an append reply at the durability boundary, reopen twice, and check that a healthy open can succeed.
5. Keep the producer of a guarantee explicit. A model theorem, a native fixture, and native refinement are different kinds of evidence.

Prefer shared schedules down to meaningful filesystem primitives. Keep recovery state on failed and interrupted paths so a retry can consume the reached state. When proofs grow sharply, test whether the boundary or representation asks callers to recover distinctions they cannot observe. Do not replace an open premise with an assumption that its desired conclusion already holds. See [WAL counterexamples and fault assumptions](design/wal-recovery.md) and the [current handoff](progress.md).

## Premise audit

For each consuming theorem, name the executable producer of each premise and
justify any external assumptions. Follow the exact state or handle across
each outcome. When a later operation depends on a resource's identity or
authority, make the handoff explicit in the executable dataflow. For example,
DurableBlob passes the writer returned by staging directly to file sync.
Hidden mutable state can require an extra proof that the later consumer
retrieves the same resource. [DurableBlob protocol](../lean/Alvoki/Experiments/DurableBlob/Protocol.lean)

Where applicable, check retry after a rejected operation and after an
uncertain outcome. On a reported error, run cleanup from the state reached
and handle only resources actually acquired and still owned. Preserve the
primary error where the contract calls for it, even if cleanup fails. When
cleanup starts after handle construction, check whether acquisition can fail
after obtaining a descriptor or creating a name, and who owns cleanup in
that case. A process interruption can prevent cleanup from running. Check
recovery from the state reached at interruption.

A premise stays open until its producer establishes it. Audit premises
alongside transitive axioms and apply the
[joint candidate acceptance check](../AGENTS.md#agent-work-and-review).

## Compose consumer requirements with producer guarantees

Design a component boundary from both ends. Work backward from the public
consumer theorem to list the exact premises, invariants, and witnesses its
proof needs. Then work forward from the producer: inventory the properties
its execution and proofs already establish, and retain those that help current
or plausible consumers without costly reconstruction. Meet at a composition
contract whose guarantees are actually consumed.

Keep three layers distinct:

- **Public behavior** states stable, representation-independent outcomes a
  caller may rely on.
- **Composition interfaces** pass reusable proved facts or ghost witnesses
  across boundaries without adding runtime data. Preserve reached state on
  errors, resource identity and ownership, durability, frame conditions, and
  authority to continue when a consumer needs them.
- **Private invariants** support implementation proofs but stay private unless
  a concrete composition need justifies exposing a stable consequence.

Pass established facts directly to the next proof. The SSTable reader uses
the writer's proved `Image`. DurableBlob carries the exact staged writer
through to its sync, preserving the inode binding. A WAL ready session carries
the installed active child that supplies append authority, rather than making
the consumer reconstruct which child was opened. In the open L0 PR #5,
`flushPublicationChoices` establishes invariants for both manifest choices
over the same catalog and WAL. The publication branches consume those facts
in the flush proof under the component contracts. Native end-to-end
composition remains open.
[SSTable composition](../lean/Alvoki/Experiments/SSTable/Proofs/UnifiedNativeEndToEnd.lean)
· [L0 flush proof](https://github.com/alvoki/alvoki-lean/blob/5bb259a0838c0b02025615ebce452c2582e7648c/lean/Alvoki/Experiments/L0/Refinement.lean#L242-L306)

Reuse local effect contracts and monadic composition rules that preserve
the reached state on success and failure. Prefer existing Lean
infrastructure. Try `Std.WP` and `vcgen` where they can replace existing
proof work. Before extracting a shared abstraction, use a second concrete
consumer to replace an existing proof, then compare what must change for a
schedule edit, a new interpreter, and a changed primitive contract.
[DurableBlob evaluation](https://github.com/alvoki/alvoki-lean/blob/a8b663695b064efc30cf43d4d3467d658255979e/lean/Alvoki/Experiments/DurableBlob/WPEvaluation.md)

## Lean techniques that still apply

| Technique | How to use it |
|---|---|
| Prove a binary-search partition | Establish monotonicity, then prove the lower-bound loop returns a cut with every earlier key below the query and every later in-range key at or above it. Connect the machine-index loop to that logical cut. See [`BlockContracts`](../lean/Alvoki/Kernel/BlockContracts.lean) and [`SSTable.Search`](../lean/Alvoki/Experiments/SSTable/Proofs/Search.lean). |
| Prove exact serialization | Compare lengths and bytes, not only a checksum. Round-trip and byte-equality lemmas then cover headers, ordering, and payloads together. See [`ByteWords`](../lean/Alvoki/Codec/ByteWords.lean), [manifest proofs](../lean/Alvoki/Experiments/Manifest/Proofs.lean), and [SSTable metadata proofs](../lean/Alvoki/Experiments/SSTable/Proofs/UnifiedMetadata.lean). |
| Carry reached state through failures | Model returned errors and interruptions separately. Preserve the state after each reached operation so a later open or retry consumes that state, instead of replaying from the initial state. See [`CrashModel`](../lean/Alvoki/Experiments/WAL/CrashModel.lean) and [segmented execution](../lean/Alvoki/Experiments/WAL/Segmented/Proofs/Execution.lean). |
| Separate safety from progress | Safety covers every admitted outcome. Healthy-open or eventual-maintenance theorems may add explicit assumptions that required I/O succeeds and resources remain available. Never let a progress premise silently narrow the safety theorem. |

For loop proofs, keep the logical specification in `Nat`; convert to `USize` only at a boundary where an extent proof establishes the conversion and every update remains in range. Prefer an invariant for the actual executable loop, and inspect the generated code before attributing a performance change to a proof-oriented source edit.
