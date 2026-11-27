# Checkpoint proofs

Relates checkpoint publication and interrupted checkpoint steps to recovery and reopening.

Start with [MarkedCheckpointPublication](MarkedCheckpointPublication.lean) · [PriorCheckpointLiveReopen](PriorCheckpointLiveReopen.lean). MarkedCheckpointPublication is imported by [CheckpointHistory](CheckpointHistory.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Checkpoint.MarkedCheckpointPublication`. These theorems use the assumptions stated in their Lean declarations.
