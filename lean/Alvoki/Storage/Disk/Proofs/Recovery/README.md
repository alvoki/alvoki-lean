# Recovery proofs

Connects observed reopening, rejection and recovery cases to the state installed for subsequent operations.

Start with [CachedOpenRejection](CachedOpenRejection.lean) · [HeldWalInstallation](HeldWalInstallation.lean). CachedOpenRejection is imported by [CachedCheckpointExtentRetry](CachedCheckpointExtentRetry.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Recovery.CachedOpenRejection`. These theorems use the assumptions stated in their Lean declarations.
