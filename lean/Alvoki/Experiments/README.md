# Experimental kernels

These modules contain independent storage components with local contracts and verification. They are not a complete database engine or a stable public API.

Start: [WAL recovery notes](../../../docs/design/wal-recovery.md#counterexamples-the-contract-must-admit) · [Immutable SSTable](SSTable/README.md).

Storage components: [Durable blob replacement](DurableBlob/README.md) · [L0 manifest](Manifest/README.md) · [Sorted-run merge](SortedRun/README.md).
[L0 composition experiment](L0/README.md) connects the storage contracts in a modeled execution.

Checks: [Component benchmark guide](../../../docs/performance/benchmarks.md).
