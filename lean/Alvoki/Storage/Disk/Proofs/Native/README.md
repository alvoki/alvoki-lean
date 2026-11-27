# Native storage proofs

These modules connect reported native operations and filesystem effects to storage histories. Start with [execution traces](Execution/NativeExecutionTrace.lean) and [fresh opened sessions](Open/NativeFreshOpenedSessions.lean).

The subdirectories cover [checkpoint](Checkpoint/README.md), [execution](Execution/README.md), [open](Open/README.md), [recovery](Recovery/README.md), and [WAL](WAL/README.md). These are proofs about reported operations and explicit filesystem assumptions; see the [native storage invariant map](../../../../../../docs/proofs/native-storage.md).

From `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionTrace` and `lake env leanchecker Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionTrace` for this module. The [getting-started guide](../../../../../../docs/getting-started.md) lists the full storage checks.
