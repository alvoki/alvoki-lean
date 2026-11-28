# Streaming sorted-run merge

`SortedRun.next` consumes two immutable runs of generic rows in strict key
order. The caller supplies a key projection, the two pull functions, their
initial cursors and storage for the frontier. The newer run has priority on
ties. The merge emits the winning row intact, including any value the caller
uses as a tombstone. The merge holds at most one buffered row per input. It
reads only missing heads and remembers EOF. The input and output files and
their lifetimes belong to the caller. [Executable merge](Merge.lean)

## Producer contract

A successful pull returns either the first row and a cursor for the exact
tail, or EOF for an empty suffix. The cursor type is opaque to the merge.
The slot belongs exclusively to the producer. Its reads and writes
respectively return and replace the current frontier without failing.
The key relation must be a strict total order for the semantic guarantees.
A typed caller uses an encoding that preserves that order for the SSTable
builder. A failed required read or decode terminates the operation and
retains the effects of that call and all earlier successful work. In
particular, if the older fill fails, the completed newer fill remains
buffered. The effect interpreter checks the actual callback schedule.

- `next_exact` identifies the emitted head and the exact new suffix of
  each input, including consumption of both heads on a tie. On every
  emitted row the sum of the two suffix lengths strictly decreases. EOF
  requires both original suffixes to be empty.
- `merge_ordered`, `Ordered.unique_keys` and `merge_keys` give strict
  ordering and exactly one row per key in the union. `merge_lookup`
  selects the complete newer row when a key occurs in both runs.
- `next_effect` gives the state and error returned for either failing
  pull and identifies the actual successful state update.

The finite reference merge and cursor suffixes used in the proofs are
ghost data. They are absent from the runtime producer. [Proofs](Proofs.lean)

## SSTable composition

`buildMergedWith` passes the actual callback to the existing streaming
writer. It accepts both the byte table and typed table pull interfaces.
`buildMergedFileSynced` uses the checked byte tables, an IO ref for the
frontier and the existing exclusive-create and original-descriptor sync
operations. The runtime still uses the existing indexed `Table.next`.
[Adapter](SSTable.lean)

`buildMergedWith_refines` establishes the exact image of the consumed rows
and an actual successful builder EOF with both input suffixes empty.
`checkedInputs_merge_checkedOutput` starts with the checked SSTable
opens of two immutable images and concludes that a checked reopen of the
synced output inode represents the full merged rows. The proof uses the
healthy reader observations and local exclusive-create, append, flush and
sync effects. A caller must supply descriptor identity for reopen and the
usual external native primitive guarantees. The writer proof admits an
observation of the writer fields alongside the input cursors. The old
writer and reader theorem interfaces are preserved. Name durability and
manifest installation are separate responsibilities.
[Composition proofs](SSTableProofs.lean) · [Writer proofs](../SSTable/Proofs/NativeWrite.lean)

The native fallible chain starts from the caller's actual checked opens.
`CheckedInput.ofOpen` transfers the acquired descriptor and valid immutable
image to the cursor proof using the local size and guarded pread contracts.
The framed reader proof, reused from PR #5 and extended to iteration,
gives the exact row or logical EOF on success. Read and decode failures
preserve the input and writer observations in the reached world.

`buildMergedFileSynced` allocates a fresh private IO ref initialized with
both starting cursors. Input actions and writer primitives receive no
reference to it. The local get and set contracts specify the exact value
of that reference and frame all caller-owned state. `nativeNext_refines`
uses them at the actual get and set calls. A failed newer fill leaves
the frontier unchanged. A failed older fill keeps exactly the stored
newer head. The effect transport keeps the original `IO.Error` and reached
world and commutes with the actual streaming writer and its cleanup.
`buildMergedFileSynced_success` supplies the exact synced image, witnessed
EOF and exhausted inputs. The output image can be fed to the same
checked-open theorem when the caller acquires the synced inode.

`buildMergedFileSynced_inputError` accepts the actual prefix of successful
pulls and accepts ending at a required failing input. It derives the
reported native error, proves that cleanup runs on the read's reached
world, and preserves the primary error even when removal fails. This branch
executes no EOF, image finalization or sync. Input acquisition, lifetime
and directory publication remain caller responsibilities. The external
primitive premises cover private reference allocation and access, the
held immutable input descriptors, and effects on the owned output.
[Fallible reader](../SSTable/Proofs/UnifiedReadSafety.lean) ·
[Native refinement](NativeRefinement.lean) · [Slot proof](Refinement.lean)

The native fixtures inject a required positional-read error and a typed
decode error after one emitted row. The effect check also injects a
second cleanup error and checks the exact final state and primary error.
The capacity case builds two valid inputs whose combined root exceeds
the format limit.
[Effect check](../../Checks/Tests/SortedRunEffects.lean) ·
[Native fixtures](../../Checks/Tests/SortedRunNative.lean)

The same pull contract allows a row or block cursor. A later k-way merge
can hold one head per run, select a minimum key and consume all heads with
that key while keeping the highest-priority row. The suffix measure is the
sum over the active runs. Two-way producers can also be composed over
groups that already respect the total recency order. There is no k-way
scheduling or iterator change in the current component.

Run `bash scripts/check-sorted-run.sh` from the repository root. It
checks the kernel and axiom policy, runs the native fixtures and checks
the logical L0 mutation view against the [PR #31 materialized oracle].
The L0 consumer is outside the component import graph.
[L0 check](../../../../tests/sorted-run/L0Consumer.lean)

[PR #31 materialized oracle]: https://github.com/alvoki/alvoki-lean/blob/f69b65229056fbde6a8de4cceefe637fcdf7b2d5/tests/compaction/CompactionProof.lean

The [negative check runner](../../../../scripts/check-sorted-run-mutations.sh)
compiles three independent mutations in an isolated checkout of the
candidate. It expects the proof checks to reject the older row winning
a tie, EOF with one input still populated, and the writer masking a
required input error.
