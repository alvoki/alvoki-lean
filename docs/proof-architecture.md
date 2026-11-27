# Proof design

Alvoki now develops storage components independently. Keep a component's public contract, executable producer, proof, native adapter, and open assumptions close enough that a caller can see where each guarantee comes from. The component guides link these pieces:

- [Segmented WAL](../lean/Alvoki/Experiments/WAL/Segmented/README.md)
- [Durable blob](../lean/Alvoki/Experiments/DurableBlob/README.md)
- [Manifest](../lean/Alvoki/Experiments/Manifest/README.md)
- [Immutable SSTable](../lean/Alvoki/Experiments/SSTable/README.md)

## A useful proof path

1. State the observable behavior at the caller boundary, including errors and uncertain outcomes.
2. Write down the admitted filesystem effects and the ownership, descriptor, and durability assumptions supplied by the environment.
3. Prove one path through the executable schedule and [audit its premises](#premise-audit).
4. Challenge the contract with a disallowed behavior and a required counterexample. For a WAL, lose an append reply at the durability boundary, reopen twice, and check that a healthy open can succeed.
5. Keep the producer of a guarantee explicit. A model theorem, a native fixture, and native refinement are different kinds of evidence.

Prefer shared schedules down to meaningful filesystem primitives. Keep recovery state on failed and interrupted paths so a retry can consume the reached state. When proofs grow sharply, test whether the boundary or representation asks callers to recover distinctions they cannot observe. Do not replace an open premise with an assumption that its desired conclusion already holds. See [WAL counterexamples and fault assumptions](design/wal-recovery.md) and the [current handoff](progress.md).

## Premise audit

For each consuming theorem, name the executable producer of each premise and
justify any external assumptions. Follow the exact state or handle across
each outcome. Where applicable, check retry after a rejected operation and
after an uncertain outcome. When cleanup starts after handle construction, check whether
acquisition can fail after obtaining a descriptor or creating a name, and
who owns cleanup in that case. A premise stays open until its producer
establishes it. Audit premises alongside transitive axioms and apply the
[joint candidate acceptance check](../AGENTS.md#agent-work-and-review).

## Lean techniques that still apply

| Technique | How to use it |
|---|---|
| Prove a binary-search partition | Establish monotonicity, then prove the lower-bound loop returns a cut with every earlier key below the query and every later in-range key at or above it. Connect the machine-index loop to that logical cut. See [`BlockContracts`](../lean/Alvoki/Kernel/BlockContracts.lean) and [`SSTable.Search`](../lean/Alvoki/Experiments/SSTable/Proofs/Search.lean). |
| Prove exact serialization | Compare lengths and bytes, not only a checksum. Round-trip and byte-equality lemmas then cover headers, ordering, and payloads together. See [`ByteWords`](../lean/Alvoki/Codec/ByteWords.lean), [manifest proofs](../lean/Alvoki/Experiments/Manifest/Proofs.lean), and [SSTable metadata proofs](../lean/Alvoki/Experiments/SSTable/Proofs/UnifiedMetadata.lean). |
| Carry reached state through failures | Model returned errors and interruptions separately. Preserve the state after each reached operation so a later open or retry consumes that state, instead of replaying from the initial state. See [`CrashModel`](../lean/Alvoki/Experiments/WAL/CrashModel.lean) and [segmented execution](../lean/Alvoki/Experiments/WAL/Segmented/Proofs/Execution.lean). |
| Separate safety from progress | Safety covers every admitted outcome. Healthy-open or eventual-maintenance theorems may add explicit assumptions that required I/O succeeds and resources remain available. Never let a progress premise silently narrow the safety theorem. |

For loop proofs, keep the logical specification in `Nat`; convert to `USize` only at a boundary where an extent proof establishes the conversion and every update remains in range. Prefer an invariant for the actual executable loop, and inspect the generated code before attributing a performance change to a proof-oriented source edit.
