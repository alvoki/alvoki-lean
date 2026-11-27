# Append proofs

Models segmented WAL appends and the continuation or recovery after interrupted append operations.

Start with [AppendCutContinuation](AppendCutContinuation.lean) · [SegmentedBatchAppendPowerLoss](SegmentedBatchAppendPowerLoss.lean). AppendCutContinuation is imported by [SequentialAudit](../../../../Checks/Audit/SequentialAudit.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Append.AppendCutContinuation`. These theorems use the assumptions stated in their Lean declarations.
