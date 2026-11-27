# Table proofs

[CheckedRunLookup.lean](CheckedRunLookup.lean) relates a checked run's lookup to its abstract history. [PackedTableLookup.lean](PackedTableLookup.lean) lifts lookup and snapshot results to the table. [CheckedRunCompaction.lean](CheckedRunCompaction.lean), [PackedTableCompaction.lean](PackedTableCompaction.lean) and [RunRetentionPass.lean](RunRetentionPass.lean) cover compaction and retained versions.

These theorems apply to the operations in [the table implementation](../../Table/README.md); import the relevant proof module explicitly.

From `lean/`, run `lake build Alvoki.Storage.Proofs.Table.PackedTableCompaction` and `lake env leanchecker Alvoki.Storage.Proofs.Table.PackedTableCompaction` for this module. The [getting-started guide](../../../../../docs/getting-started.md) lists the full storage checks.
