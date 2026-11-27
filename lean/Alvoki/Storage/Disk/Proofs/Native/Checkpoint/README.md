# Native checkpoint proofs

Start with [NativeFreshFinalCheckpoint.lean](NativeFreshFinalCheckpoint.lean) for fresh sessions through an interrupted final checkpoint. Adjacent modules connect other reached operations, failures or continuations to this boundary.

These results use explicit callback and filesystem observations; their scope and remaining assumptions are described in the [native storage invariant map](../../../../../../../docs/proofs/native-storage.md).

From `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeFreshFinalCheckpoint` and `lake env leanchecker Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeFreshFinalCheckpoint` for this module. The [getting-started guide](../../../../../../../docs/getting-started.md) lists the full storage checks.
