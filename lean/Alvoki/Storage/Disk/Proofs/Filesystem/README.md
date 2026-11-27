# Filesystem observation proofs

Models lock lifetimes, descriptor and handle custody, and observations needed by disk operations.

Start with [DiskLockLifecycle](DiskLockLifecycle.lean) · [SyncHandleCustody](SyncHandleCustody.lean). DiskLockLifecycle is imported by [LockedMarkedRead](../Recovery/LockedMarkedRead.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Filesystem.DiskLockLifecycle`. These theorems use the assumptions stated in their Lean declarations.
