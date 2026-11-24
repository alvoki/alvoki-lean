# Current handoff

The Linux adapter uses one WAL, a durable commit marker and strict v2 checkpoint manifests over immutable v3 runs. It supports sequential writes, snapshots, compaction, checkpoints, recovery and opt-in collection of obsolete run generations. [Active storage protocol](architecture.md#sequential-storage)

Under the documented I/O contracts, the strict v2 proof follows exact locked reads after repeated failures and returns the table and generation selected by the recovered checkpoint and marker. An interrupted checkpoint preserves the acknowledged WAL. An uncertain write may add its one submitted frame. Live lock and descriptor lifetimes and primitive effect reports still need to be connected to the complete native trace. [Verification status](verification-status.md) · [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

The separate segmented WAL worker validates the strict checkpoint, selects marker-covered bytes and repairs the last required segment. From one complete lock-held inventory and exact reads at the selected paths, Lean derives the retry plan and the same selected WAL bytes, table and generation after a modeled interruption. The remaining handoff connects these read reports to the effectful retry, then connects bootstrap, append, marker publication and rotation to the production adapter. [Segmented retry proof](../lean/Alvoki/Storage/Disk/WalSegmentRetryReads.lean) · [Remaining recovery and collection work](proof-roadmap.md#garbage-collection-contract)

The repository review identified the remaining native integration and cleanup work. The replay benchmark now writes the strict commit marker before adding any torn tail. The sequential checks run both benchmark modes on a small fixture. The stock and sequential check commands enforce the same proof audit. [Review follow-ups](roadmap.md#repository-review-follow-ups)

Run `bash scripts/reproduce.sh` for the baseline and `bash scripts/check-sequential.sh` for the disk fixtures, kernel checks and enforced axiom policy, with the pinned toolchains from the README. [Local commands](../README.md#reproduce-on-linux-x86-64)
