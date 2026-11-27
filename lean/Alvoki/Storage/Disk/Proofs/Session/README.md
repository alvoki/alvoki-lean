# Disk session proofs

Collects admission, recovery and maintenance facts for disk sessions.

Start with [DiskOpenAdmission](DiskOpenAdmission.lean) · [BatchRecoveryPrefix](BatchRecoveryPrefix.lean). DiskOpenAdmission is imported by [BatchAppendReopenAdmission](../Append/BatchAppendReopenAdmission.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission`. These theorems use the assumptions stated in their Lean declarations.
