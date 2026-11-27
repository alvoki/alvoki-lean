# Collection proofs

Covers WAL and obsolete-run collection, including planner preflight, naming and interrupted effects.

Start with [WalCollectionPreflight](WalCollectionPreflight.lean) · [ObsoleteRunInodeLifetime](ObsoleteRunInodeLifetime.lean). WalCollectionPreflight is imported by [WalCollectionFirstUnlink](WalCollectionFirstUnlink.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Collection.WalCollectionPreflight`. These theorems use the assumptions stated in their Lean declarations.
