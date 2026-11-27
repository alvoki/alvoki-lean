# Write proofs

Connects write traces, interrupted effects and retry recovery with client-visible histories.

Start with [ClientWriteTrace](ClientWriteTrace.lean) · [ReturnedWriteRecovery](ReturnedWriteRecovery.lean). ClientWriteTrace is imported by [BatchInterruptionDispatch](../Session/BatchInterruptionDispatch.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Write.ClientWriteTrace`. These theorems use the assumptions stated in their Lean declarations.
