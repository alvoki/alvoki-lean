# Future WAL design options

Finish the current sequential L0 baseline before choosing a new WAL.
The options below change the storage and recovery boundary. They do not
describe a production protocol. [Current milestone](../progress.md)
· [Linux writeback experiment](linux-writeback/README.md)

## Segment layout and publication

Preallocate each successor under an unpublished name and establish its
initial extent, generation and empty state. Sync the required file metadata
and contents, then sync its containing directory before a durable selector
can reference it. A fixed-extent append can then avoid extending the file or
publishing a name in the steady-state append path. Preallocation guarantees
only what the selected filesystem primitive supplies. Unwritten extents,
allocation errors, and the conversion of an extent on first use still need
an explicit interpretation.

Use aligned physical blocks containing multiple framed logical records,
with an explicit end marker or length, generation, sequence and integrity
check. A logical tail can advance without truncating preallocated storage.
Specify each block's ownership and failure locality so a fresh write cannot
damage an acknowledged prefix. Alignment alone gives no torn-write
atomicity. A torn or short write needs an admitted physical outcome and a
corresponding scanner rule. [Linux DIO alignment](https://man7.org/linux/man-pages/man2/statx.2.html)
· [ext4 atomic writes](https://docs.kernel.org/filesystems/ext4/atomic_writes.html)

## Two direct-write options

| Candidate | Durable completion rule | Expected costs and benefits |
| --- | --- | --- |
| Direct I/O with explicit group sync | All writes in the group complete with the intended lengths, then its file barrier succeeds. | Multiple writes can share one barrier. The scheduler must prevent early acknowledgement and cover failures before, during and after that barrier. |
| Direct I/O with `O_DSYNC` and an aligned group write | The entire group write completes with its intended length and the data-integrity guarantee. | One write can carry the group's barrier. Fragmenting a group may add waits, and a reported short completion needs recovery handling. |

The measured data-block fault was reported by direct `pwrite`, and the
failed overwrite did not leave new bytes visible as a clean cache page.
Buffered `O_DSYNC` reported the error on the write, yet still left that
cache state. A direct path that excludes fallback and overlapping
buffered I/O can omit that specific page-cache failure from its data-write
model. The device's persistence contract, metadata effects, namespace
durability, and possible partial or torn effects still require premises.
A direct write completion without a durability flag is insufficient to
advance the durable frontier. [Linux `open(2)`](https://man7.org/linux/man-pages/man2/open.2.html)
· [Linux `write(2)`](https://man7.org/linux/man-pages/man2/write.2.html)

Reduced allocation and directory work, amortized barriers, and pipelined
I/O are performance hypotheses. The overwrite experiment measured error
semantics. It measured neither throughput nor latency. An implementation
needs an explicit buffer-lifetime and alignment contract, evidence that
its filesystem issues direct I/O, and validation of its completions and
failure continuations.

## Frontier, uncertain groups and handoff

Maintain an invariant that the durable frontier denotes a contiguous,
validated prefix of logical records. An acknowledgement covers only
records at or below that frontier. Out-of-order completions cannot
advance it past a gap. A group barrier may complete before its reply is
lost. After an uncertain group, recovery may choose an allowed prefix of
the issued records extending the last acknowledged frontier. It must
preserve all previously acknowledged records, reject gaps and
substitutions under the admitted integrity model, and settle the chosen
prefix before returning it. A second successful reopen must return the
same prefix with no intervening write. If a group is exposed as a single
atomic client operation, the allowed prefixes must instead respect that
atomic boundary.

With async I/O, carry the exact file description and aligned buffer through
submission and completion. Before releasing or transferring ownership,
drain the in-flight writes or establish that cancellation is complete and
which effects occurred. A stopped process can leave I/O in flight. The
next owner needs quiescence before inspecting or reusing the segment.
Descriptor lifetime, lock ownership and directory barriers remain part
of the proof boundary. [TigerBeetle Linux storage and locking](https://github.com/tigerbeetle/tigerbeetle/blob/0aeb306561365e21b97775c729bfc439f6c16d72/src/stdx/io/linux.zig#L1563)

Compare the two schedules under the same workload and fault model after
the current baseline. Establish the producer-to-consumer contract with a
healthy group and a failure continuation that reopens the exact reached
state twice. Device loss of acknowledged data requires fail-stop or a
redundant repair source under either option.
