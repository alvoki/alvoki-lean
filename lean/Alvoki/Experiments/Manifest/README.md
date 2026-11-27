# L0 manifest

The manifest publishes a full version: unique opaque UInt64 table IDs in
newest-first order, and an inclusive absolute UInt64 WAL batch position
`flushedThrough`. Zero denotes the initial boundary. The initial version is
an empty list at zero. The caller supplies an initialized blob containing
that version. [Typed API](Basic.lean)

Use `backend IO.userError (DurableBlob.native directory)` with the Linux
adapter, or supply another backend with the [durable blob contract](../DurableBlob/README.md).
A publish with duplicate IDs fails before calling the backend. Reopen
propagates backend errors and rejects structurally invalid data. Publication
and reopen otherwise inherit whole-version selection and durable recovery.
The codec round trip and `recover_version` preserve the exact order and
position of either permitted version. The format is a magic word, the
position, then the IDs, all unsigned little-endian 64-bit words. Structurally
valid corruption is outside the crash model. [Manifest proofs](Proofs.lean)

## Using it from an LSM

1. Build new immutable tables under fresh IDs and make their contents and
   names durable before publishing a version that references them. The LSM
   establishes the relationship between table contents and the committed
   WAL prefix, and keeps all tables referenced by either possible version
   available until the choice is durable.
2. Publish the ordered version with a nondecreasing position through the
   last fully represented batch. WAL positions are natural numbers. Check
   that the position is below `2^64` before storing it as a UInt64, and pass
   `flushedThrough.toNat` to the WAL. If publication is uncertain, reopen before
   publishing again or releasing any additional WAL positions. On
   successful publication or recovery, the selected version permits
   `discardThrough` up to its position.
3. Recover the selected tables and replay only retained WAL batches after
   that position. For a recovered WAL view with base `b` and tail `t`, the
   LSM maintains `b ≤ flushedThrough.toNat ≤ t`. Drop
   `flushedThrough.toNat - b` batches from the retained list before replay.
   The position does not change when earlier batches are discarded.
   [Segmented WAL observations](../WAL/Segmented/Contract.lean) ·
   [Immutable table guarantees](../SSTable/README.md)

The LSM owns table lifetimes, the monotonicity and meaning of the position,
and the ordering of WAL release. This component leaves bootstrap, file
collection, compaction, further levels and engine integration to later work.

Run `bash scripts/check-experimental-manifest.sh` from the repository root
to kernel-check the modules, audit the public theorems and run a Linux
fixture through the typed API and native adapter.
