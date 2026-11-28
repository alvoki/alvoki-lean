# ALVSST06 writer refinement

Every successful execution of the recursive streaming builder in the exact
append and supplier interpretation produces `Image` for the supplier it
consumed. The implementation in [Builder.lean](../../lean/Alvoki/Experiments/SSTable/Recursive/Builder.lean)
is the schedule the theorem executes. The metadata invariant is proof-only.

The pending list starts at the lowest level. At each level its upper tail
covers an earlier row prefix and the current page covers a contiguous
suffix. Every pending child records its exact encoded byte slice, decoded
row interval and last key. Appending preserves earlier slices. Writing
a page closes one recursive node, then promotes its exact reference.
Finalization drains the pending list into a root and binds the footer to
the root ending at the footer offset. On an empty supplier the footer
describes an empty image. The supplier invariant relates the pending data
array to exact positions in its consumed prefix. The loop proves it reaches
EOF. [Page and tree invariants](../../lean/Alvoki/Experiments/SSTable/Recursive/WriterPages.lean)
· [Streaming producer theorem](../../lean/Alvoki/Experiments/SSTable/Recursive/WriterProofs.lean)

The native proof shares the executable exclusive-create, append, flush and
sync schedule and the audited ALVSST05 primitive contracts. It derives the
exact empty initial file from successful create, projects each successful
supplier and append step to the exact model, and checks that flush and sync
act on the returned descriptor. The native theorem returns the selected
inode and its exact durable bytes. Healthy open of that inode gives the
byte and typed table contracts for lookup, seek and arbitrary row cursors.
On a fallible read, the lookup consumes the writer's durable image through
the local descriptor-binding and positional-read contracts. Successful
lookups return the corresponding value, and both outcomes preserve the
specified frame. The footer-fault theorem also identifies the exact returned
error and reached state. Directory publication uses a separate barrier.
[Native composition and local contracts](../../lean/Alvoki/Experiments/SSTable/Recursive/NativeWriteProofs.lean)

The three-row checked fixture now derives its image from the general
native writer theorem. It still exercises two index levels and compares
the actual writer output with explicit expected bytes. The native
executable checks exercise CRC32C, genuine files, and malformed input.
[Kernel fixture](../../lean/Alvoki/Checks/Tests/RecursiveSSTableProducer.lean)

## Negative controls

In a detached worktree, change only the corresponding expression in
`Recursive/Builder.lean` and build
`Alvoki.Experiments.SSTable.Recursive.WriterProofs`. The unmutated
builder passes. Each mutant below is rejected by the general proof.

| Mutation | Rejected in |
| --- | --- |
| Store an empty fence in `writePage` | The promoted child fence witness |
| Store `offset + 1` in the same reference | The exact child extent |
| Add one to the promoted row count | The promoted row-range equality |
| Keep the upper pending pages without feeding them the promoted reference | The recursive promotion step |

## Review boundaries

The success theorem checks the depth and byte limits along every successful
run. The separate height proof establishes a minimum of two to the power of
the rank rows per regularly promoted reference. Finalization may carry one
short rightmost reference and keeps the higher pending pages regular. The
whole-builder proof follows supplier reads, data flushes and finalization
to exclude height exhaustion.
[Promotion and finalization height](../../lean/Alvoki/Experiments/SSTable/Recursive/WriterHeight.lean)

The healthy-progress theorem assumes valid layout and targets, strictly
ordered rows whose individual data and fence packets fit the format, and
the following conservative bound on the original supplier count:

```text
(rows + 1) × (maxRowSize + maxHeight × maxIndexSize)
  + maxIndexSize × (1 + … + maxHeight)
  + footerPacketSize
  ≤ maxFileSize
```

Each accepted row and the terminal data flush get room for one data packet
and one promoted packet per index level. Finalization reserves room for each
remaining level, its possible promotions, and the footer. This bound also
provides a spare rank for finalization. It is a sufficient capacity bound
from the input count. The writer keeps its existing single supplier pass and
does not compute the bound or materialize the input.

With the local healthy exclusive-create, supplier, append, flush and sync
contracts, the actual native schedule reaches EOF and produces the exact
synced inode and byte image. The failure theorems cover exclusive create and
errors returned by the streaming writer or sync. Create returns its actual
error and reached state directly. A streaming or sync error starts removal in
the reached state and returns the primary error with the state left by
removal, including if removal itself fails.
[Whole-builder progress](../../lean/Alvoki/Experiments/SSTable/Recursive/WriterHealthy.lean)
· [Native failure schedule](../../lean/Alvoki/Experiments/SSTable/Recursive/WriterEffectsProgress.lean)

The recursive index writer
and reader retain their existing runtime and wire behavior. The ALVSST05
producer and the L0 consumer continue to use their existing format and
interfaces.

The Bloom placement research and the index target benchmark are independent
review checkpoints. The stateful block iterator remains a separate milestone.
