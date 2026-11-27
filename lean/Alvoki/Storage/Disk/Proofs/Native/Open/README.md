# Native open proofs

Start with [NativeFreshOpenedSessions.lean](NativeFreshOpenedSessions.lean) for fresh opens and subsequent session histories. Adjacent modules connect other reached operations, failures or continuations to this boundary.

These results use explicit callback and filesystem observations; their scope and remaining assumptions are described in the [native storage invariant map](../../../../../../../docs/proofs/native-storage.md).

From `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Native.Open.NativeFreshOpenedSessions` and `lake env leanchecker Alvoki.Storage.Disk.Proofs.Native.Open.NativeFreshOpenedSessions` for this module. The [getting-started guide](../../../../../../../docs/getting-started.md) lists the full storage checks.
