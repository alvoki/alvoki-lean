# Single-file WAL proofs

Start with the [batch-level client contract](../Contract.lean). It defines the
histories a writer may observe. [`Run.refines`](Execution.lean) checks that every
modeled trace of the [single-file WAL](../README.md) obeys it.
`Run.healthy_open` establishes that recovery can return once the faults stop.
The [policy comparison](Policy.lean) shows when equal-length substitution escapes both modes, which suffix each mode
adopts and how an intact marker detects a missing published suffix.

An open writer holds a settled history. An abandoned writer can leave two
possible histories, distinguished by the last outstanding batch.
[Append](DirtyAppend.lean) and the [torn-write proof](TornAppend.lean) establish this recovery invariant.
Independent writeback of a file preserves it, and
[recovery](DirtyRetry.lean) preserves it at every interruption point.
A successful open gives the next writer a settled history again.

For a background writeback, the important physical question is whether it happens before
or after a truncate. The [append proof](AppendWriteback.lean) absorbs writeback into the
corresponding data or marker barrier. The [reopen proof](ReopenWriteback.lean) moves
writebacks to either side of the existing recovery proof while preserving its exact result
and file images. [Trace composition](ScheduledExecution.lean) then reuses the client contract.

The result is conditional on the modeled crash outcomes and experimental
limits. The [design's proof summary](../../../../../docs/design/wal-recovery.md#what-the-single-file-proof-establishes)
states those assumptions and what remains outside the theorem. Run
`bash scripts/check-wal-recovery-slice.sh` from the repository root for the
slice's kernel and axiom checks, simulations and Linux fixtures.

## Public native recovery

Linux IO and the local model run the same `openExistingWith` schedule.
[`SingleFile.openLocations`](NativeOpen.lean) checks the path and mode of
each lock, policy, data, marker, and directory open issued by the shared
dispatcher. The local model interprets each role at that reached binding. The policy barrier uses the description that
supplied the policy bytes. The data barrier uses the read/write description
that was read and, if necessary, truncated. Explicit-length `ftruncate`
removes the previous prefix read. The pre-opened append stream keeps its
own barriers.

[`SingleFile.openExisting_refines`](NativeOpen.lean) composes acquisition,
scheduled recovery, policy and directory barriers, and installation. It
returns the selected history and canonical cursor with both namespace
barriers settled. An ordinary failure releases the lock and preserves the
retry invariant at the reached image, including if recovery already
changed that image. A process stop drops the lock without changing the
reached child bytes. The shared open schedule constructs the ready phase with that exact
cursor and history after both barriers. The shared storage schedule passes
that phase unchanged to the native reference allocator. The proof observes
that stored phase, and the runtime supplies reference semantics under the mutex. `scanWith` returns its history and `closeWith` clears
the phase before releasing the lock, including on unlock error.
[`Child.Recoverable.nativeOpen`](../Segmented/Proofs/SegmentRecovery.lean)
derives the current child contracts and scan result from the complete open
model, with acquisition and cleanup included.

| Boundary | External primitive premises |
| --- | --- |
| Directory and file descriptions | The owner supplies an existing admitted directory and policy, stable names and distinct regular inodes, except that the two segment opens reach the same inode. The directory's parent binding is durable. Open resolves the requested binding or errors. Open may create the dedicated lock file. C stream construction and disabling buffering preserve the bound file description. |
| Lock and handle lifetime | Lock acquisition is exclusive for cooperating owners. The lock remains held across the body until explicit unlock or the last drop of its private description, including a failed unlock or process exit. The runtime releases local references on failure and serializes shared phase reads and writes under the mutex. Ref and mutex allocation and ordinary process-resource handling follow the Lean runtime semantics. |
| Reads, repair and barriers | Reads from the start return the exact visible bytes or an error. Truncate uses the requested nonnegative prefix length on the supplied read/write description. On Linux x86-64 the reachable lengths fit signed `off_t`. Sync binds to the supplied description and settles the relevant bytes or directory entries. A truncate or barrier can report an error before or after its effect. |
| Background persistence | The existing scheduled model admits independent whole-file writeback before each reached worker primitive. Writebacks during acquisition and after the worker commute with the metadata-only steps and are represented at those boundaries. The established byte-level fault and crash assumptions still apply. |

The focused check kernel-checks the worker and public proofs, audits their
dependencies and runs the native fixtures. The added fixture exercises
truncation to zero, append on the pre-opened append description, and two
subsequent successful reopens, for both policies. A test-only linker
wrapper also fails directory fsync after the repair, checks that the public
open failed and left the truncate in place, and verifies lock reacquisition
and the recovered history on retry. The fixtures sample
behavior of Linux and its runtime. The proof establishes the contract
relative to the primitive assumptions in the table.

## Public native append

The ready phase stores the writer and marker pair acquired by open, in the
order fixed by the shared dispatcher. The recovery reader can drop after
installation. The append schedule constructs its callbacks from those
stored descriptions. It poisons the shared phase before issuing writes
and reinstalls the same bindings with the advanced cursor and history
only after all required barriers. Scan and append reject a poisoned
phase. Close clears it before releasing the same lock.

[`SingleFile.append_refines`](NativeAppend.lean) uses the existing
scheduled writeback, dirty append and torn append proofs at the reached
writer and marker slot. An ACK establishes the extended durable history.
An error or interruption leaves at most the submitted batch pending.
A lost reply can leave that batch fully durable. Oversized or exhausted
submissions poison the handle before any write and leave the image alone.
[`Child.Recoverable.nativeAppendAfterOpen`](../Segmented/Proofs/SegmentRecovery.lean)
composes the public open and append interpretations on the same stored
phase, yielding the existing child installation and recovery facts.

The native premise is local to each issued operation. On the unbuffered
append description, a successful write and flush appends the frame at the
actual end. A marker rewind followed by write and flush starts at offset
zero on the selected slot, or returns a primitive error with its reached
bytes. A rewind error issues no write. Writebacks before a write, including
between rewind and write, change only the corresponding durable image.
File sync acts on the supplied writing description and may report an
error before or after persistence. The admitted partial writes, tears,
and crash choices remain those of the existing WAL model. Ref and mutex
semantics preserve the shared phase under aliases. A normal error keeps
the lock in the poisoned phase, and a process stop releases its private
descriptions by last drop. The test-only wrapper checks the reached marker inode and reports an error
after its successful native fsync and checks that two reopens recover the
same confirmed history plus the pending batch.

Native bootstrap, segmented root recovery, CONTROL publication, and
native rotation retain separate refinement obligations.
