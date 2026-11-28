# WAL recovery assumptions and counterexamples

The WAL models preserve several correctness obligations that continue to matter to the component work. A crash contract must describe the joint file and namespace state that can survive, including an error after a sync has taken effect. A successful first open must establish a history that a second open with no intervening operation returns again. Healthy recovery must be possible once faults stop. These are proof obligations, not consequences of a checksum or of a successful model run.

## Counterexamples the contract must admit

<a id="what-the-single-file-proof-establishes"></a>

- **Uncertain append.** After A is acknowledged and B's append or sync reply is lost, a surviving complete B may be retained; a damaged final B may be discarded only when the selected durability boundary does not cover it. Recovery must never lose A.
- **Missing published data.** If a durable marker covers B but the corresponding bytes are missing or detectably corrupt, open must report an error. If the marker ends at A, an unpublished suffix can be discarded.
- **Valid substitution.** A different checksum-valid record with the expected sequence and length can pass ordinary framing checks. The abstract client history must reject a recovered write that was never submitted. A checksum is not authentication.
- **Interrupted repair.** If dirty tail bytes are written back before recovery truncates them, then recovery stops before syncing that truncate, a power loss can reveal the tail again. Retry must account for both the reached state and the sync outcome.
- **Lost sync response.** A reported file or directory sync error does not establish that the operation had no effect. Keep both possible outcomes and feed the observed filesystem choice into retry and reopen.

The single-file proofs model append residues, writeback and the policy-dependent treatment of an uncertain suffix. Their important boundary is explicit: valid arbitrary substitution is outside the filesystem crash model and must be caught by the client-history contract. See [policy counterexamples](../../lean/Alvoki/Experiments/WAL/Proofs/Policy.lean), [physical write outcomes](../../lean/Alvoki/Experiments/WAL/CrashModel.lean), and [writeback proofs](../../lean/Alvoki/Experiments/WAL/Writeback.lean).

## Filesystem premises

The executable schedule needs explicit premises for exclusive stable directory ownership, durable naming at initialization, exact reads or reported read errors, prefix preservation across append and repair, and the effects of successful file and directory sync. Process exit may leave cached bytes visible; power loss selects an admitted durable image of both file contents and directory entries. A native fixture can exercise selected Linux outcomes but cannot establish device power-loss behavior. See [filesystem assumptions](filesystem-assumptions.md) and the [DurableBlob guide](../../lean/Alvoki/Experiments/DurableBlob/README.md).

## Proof and verification paths

Keep framing, replay choice and the observable history contract explicit. Derive each filesystem premise from the operation and handle actually reached. Preserve failed and interrupted state so subsequent open attempts consume the real continuation. The segmented model and proofs compose rotation and release around the single-file recovery reasoning; see its [guide](../../lean/Alvoki/Experiments/WAL/Segmented/README.md).

Run `bash scripts/check-wal-recovery-slice.sh` for the single-file proofs, torn-write and retry regressions, and native partial-write fixture. Run `bash scripts/check-segmented-wal.sh` for the segmented model, kernel, axiom, and native fixtures. The full retained suite is `bash scripts/reproduce.sh`.

See the [runtime-state and streaming recovery proposal](wal-runtime-state.md)
for the field inventory, producer migration and review gates.
