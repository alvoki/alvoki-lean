# WAL recovery policies and deterministic simulation

**Design proposal.** Start with a single writer, one durably named segment and whole batches. The current engine publishes an absolute WAL byte boundary using a staged marker, grouped file sync, rename and directory sync. Its callback-based schedule is a useful starting point. The two policies below would require a versioned on-disk format and their own source-level proofs. [Current commit path](../../lean/Alvoki/Storage/Disk/WAL/WalSegmentCommit.lean) · [Current filesystem contract](../proofs/filesystem.md)

## What the caller buys

| Persistent database policy | ACK boundary | Successful recovery |
|---|---|---|
| Log only | Append the complete batch, flush any userspace buffering and successfully data-sync the segment. | Recover a contiguous sequence of complete submitted batches starting at the required checkpoint position. Every ACK survives under the crash assumptions below. A complete uncertain tail may survive. |
| Durable commit boundary | Make the batch data durable, then durably publish the boundary covering it before ACK. | Replay through the selected boundary. Missing bytes, a gap or detectable corruption inside it must produce an error. Discard any later unpublished suffix before reusing the segment. |

Record the format and policy durably at creation. An existing database opens under its recorded policy. A missing required marker is an error. New formats need an explicit migration or a fresh database. The boundary identifies the segment generation, byte end and last sequence. Its publication must survive a crash as one old or new valid choice and a completed barrier must preserve the newer choice. Loss or coherent rollback of both the marker and the data is beyond this detector. A marker can become durable before the caller receives the ACK.

**Assumptions to prove against.** The writer owns the directory and establishes the segment name durably. A successful data-sync preserves the bytes and the metadata needed to retrieve them. A subsequent append or tail repair preserves previously synchronized prefix bytes, including when two batches share a filesystem block. Process death may leave dirty data visible. Power loss selects an allowed joint image of file contents and directory entries. A read error provides no evidence that the tail is empty.

Use bounded, checked batch headers (generation, sequence and length) and a validity check over the header and payload. Define exactly which torn writes or corruptions the encoding detects. A CRC alone cannot prove authenticity against arbitrary replacement bytes or checksum collisions. An old valid batch in a recycled file is another reason to check generation and sequence. Before claiming the log-only theorem, prove that every accepted tail under the admitted fault model decodes to a complete submitted batch, or explicitly narrow that model.

## First vertical slice

1. Append A and return its ACK. Start B, then interrupt the append or its sync. Stop issuing writes on that session after an ambiguous outcome.
2. Open the actual resulting image. In log-only mode an admissible torn final B, even at full declared file length, can be discarded. A valid B can be retained. A gap in required earlier history or an I/O read error fails open. In boundary mode inspect the selected marker first. If it covers B, damaged B must fail open. If it ends at A, discard the suffix.
3. Stabilize the recovered end before exposing the recovered history as durable, including after process death with dirty bytes. Append and acknowledge C. Crash again. A second successful open must preserve A, C, and the decision about B that the first successful open exposed. Recovery interrupted during repair must itself be retryable.

After this slice, rotate only between batches and settle the successor name before acknowledging writes to it. Collect whole closed segments only after a durable checkpoint releases them. Defer recycling until a fresh generation and every stale-tail outcome can be distinguished. Keep proofs of these operations local to the shared recovery invariant.

## One algorithm, two ways to run it

Keep framing, bounded decoding and the choice of replay end pure. Keep the order of append, sync, marker publication and repair in a single executable Lean function parameterized by the few operations it actually calls. A function of the shape `appendBatch [Monad m] (ops : WalOps m) ... : m Ack` can execute these calls in order and branch on their results. The type and signature here are illustrative. Start with ordinary function arguments if the slice only needs append and sync. Existing `commitBytesAt` and `Publication.run` already express schedules this way. [Publication interpreter](../../lean/Alvoki/Storage/Publication/DiskPublication.lean)

- **Native interpreter.** Supply Lean IO and checked native primitives. Preserve actual descriptors, flushes, return values and failures, including effects that occurred before an error.
- **Simulation interpreter.** Supply operations on a small model with volatile bytes, durable bytes, visible/durable names and a fault script. For example, `EStateM SimError SimState` carries the reached state on both success and failure. A scripted stop abandons the running call without invoking its ordinary error cleanup. Model exit or reboot explicitly and run the same real open schedule again on its successor state. Keep the driver's record of submissions and observed ACKs outside the simulated process.
- **Independent test oracle.** Check the public observations against allowed histories from those submissions and ACKs. Never use the production scanner to compute the expected answer. For a small script, enumerate the reached primitive cuts and allowed persistence outcomes. Later, generate longer scripts deterministically and save failing scripts with their seed and minimized sequence.

A discriminating fixture places A and B in one block and persists B's full length with only part of its payload. Enumerate this outcome only while the required data barrier for B has yet to succeed. Separately inject detectable damage *after* B's ACK to exercise the stronger policy with an intact marker. Also try a process exit with valid B visible only in cache, an error before and after an effective sync, and a read EIO. Assert the subsequent open result, repair effects and second-reboot history. A deliberately broken implementation that acknowledges before sync should fail under an allowed power-loss cut.

## Evidence and cost

Lean proofs should quantify over all admitted outcomes and establish the ACK, recovery and detection contracts per policy. Simulation executes representative and bounded-exhaustive scripts quickly, challenges the fault model and produces short regressions while the contracts change. Linux fault and process-death tests independently exercise native callback ordering, actual reads and error propagation. Neither a simulator nor a process kill establishes a device's power-loss behavior. [Native fixtures](../../lean/Alvoki/Checks/Tests/DiskTableChecks.lean) · [Process-death tests](../../scripts/check-disk-process-death.py)

Measure performance empirically. Compare the two policies on the same device, filesystem, workload and durability settings. Record batch size, group size, segment size, ACK latency percentiles, throughput and syncs per acknowledged group. Report rotation separately and compare recycling on/off once it exists. Recycling saves work per rotation while a durable commit boundary adds ordered work per group. Published results should identify the workload where either cost matters. [Benchmark methodology](../performance/benchmarks.md)
