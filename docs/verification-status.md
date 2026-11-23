# Verification status

| Property | Lean 4 | Verus |
|---|---|---|
| Lower-bound partition and termination | Kernel-checked for the executable `lowerBound` with a monotone predicate | Verified for the corresponding binary search over a sorted `&[u64]` |
| Point lookup | Kernel-checked soundness for the packed lookup, and lower-bound completeness under strict logical key order | Verified found index and absence for a sorted key slice |
| Range membership and key order | Kernel-checked exact index interval membership under sorted keys and pairwise key ordering under strict order | Verified exact bounds membership for a sorted key slice |
| Little-endian codec | Kernel-checked round trip through eight appended bytes at an arbitrary prefix offset for `pushWordFast` and `word`. Also proved `wordFast = word`. | Outside the verified key-slice core |
| Full parser, block codec, and materialized range fold | Differential tests cover the current implementations. The block-level refinement and fold proofs remain open. | The corresponding packed Rust implementation is tested. The verified core operates on logical keys. |

The Lean search proofs use an invariant over the left and right regions outside the active window. The range theorem combines two lower-bound partitions. The codec proof reduces each output bit to the unique byte lane that contains it and uses byte-array push indexing to connect that result to the optimized encoder. The axiom audit reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` where used. An earlier bit-vector tactic yielded a native checking dependency, which the checked bit-lane proof removed.

Verus proves the analogous loop invariant with quantified sequence properties. It needs explicit instantiation of sortedness after changing either bound and an explicit trigger on range membership. The verified source is a separate executable core, so its results do not establish correctness for the Rust packed parser or search integration.

`lake env leanchecker Proofs` successfully rechecked the built Lean module. The separately packaged `lean4lean Proofs` failed with an incompatible olean header. The proofs concern Lean or Verus source semantics and use their normal trusted bases. Native execution also relies on the respective compilers, runtimes, and standard libraries. Kernel or Verus checks do not establish correctness of the VM, OS, file I/O, or generated machine code.

## Optimized reader and search

`lean/OptProofs.lean` proves that the tail-recursive machine-index search agrees with the original natural-number lower bound after index conversion. It derives the same partition guarantee for monotone logical keys. `wordMachine_eq` proves the optimized reader is equal to the original byte reader when the eight-byte extent is in bounds and the array size fits in a machine word. Each proof-carrying byte load and indexed store uses an explicit bound, and Lean checks the progress of the machine-index loops.

The optimized parser, view offsets, range fold, and encoders are tested against both external layouts or the version 1 output fixture where applicable. Connecting parser acceptance and offset arithmetic to the logical sortedness assumptions remains open. `scripts/optimize.sh` builds and rechecks the new theorems using `leanchecker`; the axiom audit lists only standard Lean axioms.

## Packed output and merge

| Component | Kernel-checked source guarantee | Remaining boundary |
|---|---|---|
| [Stock byte builder](../lean/ScopedBytes.lean) | Appending an in-bounds slice preserves the prefix, appends the exact source bytes in order, and gives the specified length. Batch append agrees with concatenating the supplied slices. Combining adjacent source extents preserves their byte sequence. | Native execution relies on the stock compiler and runtime, including `ByteArray.copySlice`. Capacity and exclusivity are runtime concerns. |
| [Streaming and prepared replay](stock-builder.md#byte-contract) | Streaming output refines the header and payload of the supplied trace. Prepared output has the specified header, slice bytes and payload length for the supplied plan. | The trace checker establishes move and cursor validity. The benchmark oracle supplies the right-biased choices. Planner and coalescer equivalence remain open. |
| [Online merge and direct scan](fused-merge.md#verification-and-reproduction) | Lean checks loop termination and the explicit bounds required by proof-carrying accesses. The fused emitter uses the stock builder's proved byte operations. | Exact merge fixtures and checksum comparisons cover the tested implementations. Full refinement to the sorted union and direct fold remains open. |
| [Fixed-width copy](fixed-copy.md) and [scoped runtime](scoped-builder.md) prototypes | The source-level byte contract provides a reference for the experiment. | The alternate native implementations depend on the pinned generated-code ABI and their runtime contracts. Differential fixtures check their outputs. Runtime refinement remains open. |

`scripts/stock-builder.sh` checks the stock builder and replay proofs with the bundled `leanchecker` and audits their axiom dependencies. The stock proof audit reported only the standard Lean axioms. [Builder proof audit](../lean/ScopedBytesProofs.lean) · [Review findings](repository-review.md)
