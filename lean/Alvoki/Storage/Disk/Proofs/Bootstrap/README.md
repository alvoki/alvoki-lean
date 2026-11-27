# Bootstrap proofs

Studies creation and reopening of the initial WAL keeper and marker, including observed failure and retry cases.

Start with [WalSegmentBootstrapEffects](WalSegmentBootstrapEffects.lean) · [BootstrapMarkerDetachError](BootstrapMarkerDetachError.lean). WalSegmentBootstrapEffects is imported by [SegmentedSessionInstall](../Recovery/SegmentedSessionInstall.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Bootstrap.WalSegmentBootstrapEffects`. These theorems use the assumptions stated in their Lean declarations.
