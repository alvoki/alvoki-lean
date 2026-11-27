# Checkpoint run proofs

Models interruptions and stops during checkpoint run creation and their reopening consequences.

Start with [Interruption](Interruption.lean) · [InterruptionReopen](InterruptionReopen.lean). Interruption is imported by [InterruptionReopen](InterruptionReopen.lean). See the [disk proof guide](../../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Checkpoint.Run.Interruption`. These theorems use the assumptions stated in their Lean declarations.
