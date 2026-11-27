# Single-file WAL experiment

This directory explores recovery policies for a **single-segment experimental
WAL**. It is separate from the engine's supported
[segmented WAL](../../Storage/Disk/WAL/README.md); its formats and guarantees
must not be assumed to describe `DiskTable`.

Start with the [design and executable walkthrough](../../../../docs/design/wal-recovery.md#run-the-one-segment-experiment).
[SingleFile](SingleFile.lean) provides the experimental directory API;
[Contract](Contract.lean) defines permitted observations in batches,
[Recovery](Recovery.lean) contains framing and recovery decisions, and
[CrashModel](CrashModel.lean) defines the modeled persistence outcomes.
[Proofs](Proofs/README.md) explains the verified slice and its limits. The
design links its deterministic simulation and Linux fixtures.

The [segmented experiment](Segmented/README.md) composes these single-file guarantees across rotation, prefix release and repeated recovery.
