# Read proofs

Relates client and snapshot read traces to session state and recovery observations.

Start with [ClientReadTrace](ClientReadTrace.lean) · [MixedTraceSnapshotReads](MixedTraceSnapshotReads.lean). ClientReadTrace is imported by [BootstrapClientTrace](../Bootstrap/BootstrapClientTrace.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace`. These theorems use the assumptions stated in their Lean declarations.
