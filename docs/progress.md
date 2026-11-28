# Current handoff

The segmented WAL milestone was reviewed and merged in PR #26 at
`a375c871879e51558be60661d86f73b9cbaa904c`. PR #5 includes the
tested integration handoff `791940352e0068a9e303236c8b50b22d638fa139`.
Its [L0 producer checks](../lean/Alvoki/Experiments/L0/WalProducerHandoff.lean)
recover the registered active child and append authority, pass a reported
append through close on the reached disk, and pin the recovered choice
across two opens. The operations in these checks run on the WAL proof
model. [WAL guide](../lean/Alvoki/Experiments/WAL/Segmented/README.md)

PR #5 connects the native L0 read scope to the client trace. The concrete
[public scope theorem](../lean/Alvoki/Experiments/L0/WithOpenReads.lean)
follows root acquisition, manifest and WAL recovery, phase publication,
each public read and cleanup on their reached IO worlds. It starts with
an initialized root, a represented table catalog, the selected manifest
bytes and a WAL recoverable at a known view. The [recovery proof](../lean/Alvoki/Experiments/L0/NativeRecoverAt.lean)
obtains the session by replay, and publication supplies the online state
used by the first read. Caught read errors leave the next read on the same
owned session. A successful read contributes a client event. The cleanup
proof retains the actual root-unlock response even when an earlier error
determines the public reply. The failed-`fdopen` limitation on Lean 4.36
is recorded in the [filesystem contract](design/filesystem-assumptions.md).

[HealthyReads.withOpen](../lean/Alvoki/Experiments/L0/HealthyReads.lean)
derives two successful public misses and cleanup on an initialized empty
root from healthy primitive reports. On a populated root the Linux fixture
injects a one-shot table size error after descriptor acquisition. It reads
successfully on the same handle, counts descriptors across close and
reads again after reopen. The [L0 guide](../lean/Alvoki/Experiments/L0/README.md)
describes the remaining consumers of the earlier model bridge.

[NativeMutationScope.mutationThenReadTwice](../lean/Alvoki/Experiments/L0/NativeMutation.lean)
connects public put and delete, acknowledgement loss, error cleanup and two
reopens on the reached worlds. It derives the write authority from the
child installed by the public opener. The first recovery with a pending
request pins its choice at WAL acquisition. The next open consumes that
choice even if the earlier read or cleanup returned an error. The L0 guide
records the division between reusable WAL producers and public L0 proofs.
[Worker interruptions](../lean/Alvoki/Experiments/L0/InterruptedWorker.lean)
and [cleanup interruptions](../lean/Alvoki/Experiments/L0/MutationExitCut.lean)
derive the retry input for process exit and power loss from the issued
operation and the surviving files. The [progress check](../lean/Alvoki/Experiments/L0/HealthyMutation.lean)
derives success on a healthy initialized root and follows the same
committed write when the final unlock reports an error. Milestone 3 follows table creation, directory sync and manifest
publication through the admissible interruption prefixes into survivor
selection and a recovered read. Both deliver their observations to
`Client.Step`, `Client.Allows` and `Execution.Run.refines`. PR #30 at
`876256a6005d0845519b15aada3b224275dbf3db` remains the reviewed
research reference.
