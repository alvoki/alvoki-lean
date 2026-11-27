# Checkpoint reopening proofs

Connects held checkpoint installation with segmented checkpoint recovery.

Start with [HeldInstallation](HeldInstallation.lean). HeldInstallation is imported by [CheckpointLiveHeldReopen](../CheckpointLiveHeldReopen.lean). See the [disk proof guide](../../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Checkpoint.Reopen.HeldInstallation`. These theorems use the assumptions stated in their Lean declarations.
