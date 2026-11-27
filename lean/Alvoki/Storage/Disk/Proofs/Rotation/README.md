# WAL rotation proofs

Models segmented WAL rotation and the handoff or reopen after interrupted creation.

Start with [WalSegmentRotation](WalSegmentRotation.lean) · [RotationSessionHandoff](RotationSessionHandoff.lean). WalSegmentRotation is imported by [WalSegmentBootstrapEffects](../Bootstrap/WalSegmentBootstrapEffects.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Rotation.WalSegmentRotation`. These theorems use the assumptions stated in their Lean declarations.
