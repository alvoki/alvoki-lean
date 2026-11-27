# Checkpoint manifest proofs

Studies the staged manifest and rename prefix during a checkpoint power cut.

Start with [RenamePrefix](RenamePrefix.lean). RenamePrefix is imported by [CheckpointManifestRenameCut](../CheckpointManifestRenameCut.lean). See the [disk proof guide](../../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Checkpoint.Manifest.RenamePrefix`. These theorems use the assumptions stated in their Lean declarations.
