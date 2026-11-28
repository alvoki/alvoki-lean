# Reviewing the native L0 refinement

**Independent audit correction.** The required PhaseMemory has no inhabitant. The native theorems that assume it are vacuous, including the healthy examples described below. The [counterexample, design and validation gates](l0-phase-memory-audit.md) supersede the earlier native acceptance assessment.

PR #5 has one integrated executable candidate. The starting points for
review are the [flush scope](../../lean/Alvoki/Experiments/L0/NativeFlushPublic.lean),
the [interrupted flush](../../lean/Alvoki/Experiments/L0/NativeFlushObserver.lean)
and the [same-handle mutation sequence](../../lean/Alvoki/Experiments/L0/MutationSequenceRoot.lean).
The [client contract](../../lean/Alvoki/Experiments/L0/Client.lean) and
[`Execution.Run.refines`](../../lean/Alvoki/Experiments/L0/Execution.lean)
also apply when the reply is lost.

The [acceptance boundary](l0-native-acceptance.md) distinguishes the public
safety theorems, conditional progress and the runtime assumptions. The
[implementation retrospective](l0-native-retrospective.md) records what
changed the proof design and where its cost still grows.

## Review units in dependency order

| Unit | Producer and external boundary | Consumer on this branch |
| --- | --- | --- |
| Single-file WAL | [ConcreteRecovery](../../lean/Alvoki/Experiments/WAL/Proofs/ConcreteRecovery.lean), ConcreteOpen, ConcreteAppend and ConcreteCreate relate file roles, cursor, descriptor and selected marker to bytes. POSIX reads, writes, sync, namespace queries and exclusive handle ownership are local inputs. | The segmented acquisition, append-in-place and successor workers reuse the same single-file proofs. |
| Segmented WAL | [RuntimeStoreOpen](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/RuntimeStoreOpen.lean) and RuntimeChild return the actual registration. [AppendRuntime](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/AppendRuntime.lean) returns authority on success, or the exact uncertain request and owned slot on error. CONTROL, slot transfer and child preparation stay inside the component. | Both the first and second public mutations use these producers. The second consumes the registration and child memory left by the first. Close and retry use the same WAL acquisition laws as the original read scope. |
| WAL interruption | [PublicAppendCut](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/PublicAppendCut.lean), the child, close, prepare and CONTROL coverage modules connect native issued operations to the WAL disk model. Successful previous calls determine the next operand. | [InterruptedWorker](../../lean/Alvoki/Experiments/L0/InterruptedWorker.lean) obtains a permitted pending append from the observed execution. It needs local primitive disk effects, caller-file frames and reboot selection. |
| Runtime ownership and scope | [NativeScope](../../lean/Alvoki/Experiments/L0/NativeScope.lean), [NativeReadRelease](../../lean/Alvoki/Experiments/L0/NativeReadRelease.lean) and [MutationExitCut](../../lean/Alvoki/Experiments/L0/MutationExitCut.lean) implement ordered bind, primary-error precedence, phase ownership, and cleanup. Runtime assumptions concern the named references and acquired descriptors. | Read, mutation and flush share grant, release, and close. A reported unlock error still leads to last-reference disposal under the local runtime contract. Failed fdopen before Lean 4.36 constructs the handle remains outside that contract. |
| SSTable IO and allocation | [BuilderRelation](../../lean/Alvoki/Experiments/SSTable/Proofs/BuilderRelation.lean) carries the generic streaming induction. [NativeTableWriter](../../lean/Alvoki/Experiments/L0/NativeTableWriter.lean) binds the actual row supplier, exclusive writer and synced bytes. [NativeTableCreate](../../lean/Alvoki/Experiments/L0/NativeTableCreate.lean) combines allocation and directory fsync. | The table producer hands the live and durable inode and its checked image to manifest publication. The L0 codec, table layout, directory naming and freshness test specialize this unit. The original pure builder and public table reader continue to consume the same image predicate. |
| Manifest publication | [NativeManifestPublish](../../lean/Alvoki/Experiments/L0/NativeManifestPublish.lean) and [ManifestPublishSchedule](../../lean/Alvoki/Experiments/L0/ManifestPublishSchedule.lean) bind staged bytes, the specific writer, rename, and directory handle. Typed version validity is the manifest-specific input. | Flush consumes the old manifest before rename, the admitted old/new bindings after rename and the settled new binding after the directory barrier. These modules contain no memtable or WAL replay proof. |
| L0 composition | [NativeFlushCatalog](../../lean/Alvoki/Experiments/L0/NativeFlushCatalog.lean) carries the initialized live and durable catalog through recovery and scan. [NativeFlushStore](../../lean/Alvoki/Experiments/L0/NativeFlushStore.lean) consumes the reached rows and calls the two filesystem producers. [NativeFlushRestart](../../lean/Alvoki/Experiments/L0/NativeFlushRestart.lean) interprets the chosen watermark, table order, replay suffix and resulting map. | Every reached selection supplies the existing [WithOpenReads](../../lean/Alvoki/Experiments/L0/WithOpenReads.lean) scope. Recovery can fail before a callback, a read can report an error, or close can fail after the reads. |

The first three units are WAL review candidates. The streaming induction
and raw publication schedule can each be reviewed with their existing
component proofs. Keep the L0-specific physical directory mapping, replay
watermark and client traces together. These boundaries describe the
current graph and require no branch extraction.

## Interruption granularity

The initial root and the successful callback grant identify the public
operation being interrupted. Before callback invocation there is no
client append or flush to acknowledge. Public open and recovery errors
have their own outcomes. Within the operation a prefix can end at an
ordinary boundary, during the currently issued primitive, or after the
complete return. A bind starts its continuation only on its actual
successful result. Error handlers and finalizers start on the world
left by the preceding error.

An FFI primitive such as checked directory enumeration may be stopped
while its native implementation is running. Its in-flight contract
specifies the possible protected-file effects throughout that call.
Lean-level loops over returned entries and the WAL's read-to-EOF loop
expose each iteration. In particular the second and later 1,024-byte
reads have their own issued operands. Pure code between two observable
effects uses the same physical world as their common boundary.

For flush, `NativeFlushObserver.erase` relates the observer to the
actual public IO result and world. Its reverse theorem `classify` takes
a raw cut at that callback and recovers its position in reservation,
storage or finalization. `interrupted` passes that position to the
survivor proof and then to the public read. For append,
[`MutationAllCuts.interrupted`](../../lean/Alvoki/Experiments/L0/MutationAllCuts.lean)
starts with one raw cut and passes the precise pending or settled history
through two public reopens. This includes a guard rejection and the
second phase borrow before append.

## What changes at a flush cut

| Last completed effect | Physical recovery input |
| --- | --- |
| Reservation, scan, allocation, streaming, or table-directory sync | The old manifest still selects the old database. Newly created files can remain as unreachable orphans. Allocation consults the actual namespace and skips occupied names. |
| Staged manifest file synced | The new table is available under its durable name. The active manifest is still old. |
| Rename took effect, parent sync pending or reported an error | Process exit retains the current active manifest. Power loss can select an allowed directory survivor. If it selects the new manifest, its table bytes and name were made durable earlier. |
| Manifest directory sync succeeded | Only the new manifest survives. Publication of the in-memory session, delivery of the client reply, and finalization may still be interrupted. |

A failed or interrupted syscall uses the primitive's admitted physical
effects. A reported error can follow an effective rename or directory
barrier. At reboot the [physical selection rule](../../lean/Alvoki/Experiments/L0/NativeFlushBoot.lean)
reads live entries on process exit and durable entries after power loss.
It puts no restriction on unreferenced orphan names. The Linux fixtures
exercise error returns and abrupt process exits while the kernel is
running. Persistent media and loss of kernel state are modeled by the
filesystem laws. [Filesystem assumptions](filesystem-assumptions.md)

## Proof cost

The flush-specific obligations are equality to the installed sorted
memtable, freshness in the presence of orphans, durability of the file
before publishing its name, and agreement of the selected watermark
with replay. Existing WAL acquisition, phase scopes, catalog lookup,
client trace rules, and the public read pipeline are reused. The generic
builder induction serves both the old writer proof and the native
streaming writer. The same executable create/publish bind supplies both
typed IO and the interruption proof. The same primitive reader
induction underlies the fallible read and healthy read with advancing
worlds. A temporary second rename in the actual DurableBlob publisher
made the native manifest correspondence proof fail at compile time.
Restoring the executable restored the proof.

The scan, table create and manifest calls preserve different fields.
Table preparation may add a file while framing the manifest, and the
publisher changes the manifest while framing the original file. They
share the bind and scope rules but keep these two contracts separate.
A conditional healthy execution also needs positive syscall reports.
The capacity-one recovery witness reuses the same segmented worker as
the empty example and the same public read pipeline as the safety proof.
The CONTROL bytes read on the reopened disk identify the selected child.
The ordinary acquisition and validation frames carry its recoverability
to the policy read where the child opener consumes it. The caller supplies
the healthy primitive reports for this WAL.
For a recovered nonempty memtable and a key present in its sorted rows,
[`NativeFlush.healthyRead`](../../lean/Alvoki/Experiments/L0/HealthyFlushRead.lean)
also forces the next public get to succeed under the healthy reports.
The returned descriptor selects the very inode and bytes that were synced
before rename. Capacity one and an unrotated selected WAL bound this
positive example. The safety and interruption theorems apply across
admitted WAL shapes.

The former whole-callback bridge required a separate writer execution
and an installation map from that run to the purported physical state.
Deleting the unused bridge and its product-world consumers removed
1,358 lines of Lean while retaining the component-level model proofs.
The new path still incurs the cost of checking every primitive in the
WAL rotation and cleanup schedules. Grouping those proofs with their
executable producers gives reviewers a way to check that cost separately
from L0 history reasoning.
