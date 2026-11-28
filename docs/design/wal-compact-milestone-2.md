# Compact WAL and the milestone 2 producer

The reference is PR #5 at
[`e7cc1296`](https://github.com/alvoki/alvoki-lean/commit/e7cc1296625bea88ca002737f64afbfc0f5b3a47).
It was inspected in a pinned detached worktree. The two candidates share
the WAL abstract model from `a375c871`. The compact checkpoint continues
PR #34. The original benchmark harness and cohorts are reviewed
independently in [PR #35](https://github.com/alvoki/alvoki-lean/pull/35).

## Independent Linux prerequisite

A small patch on `main` at `275e348b` was tested in a separate worktree.
It replaces the legacy recovery and policy-stamp reads with checked 1 KiB
chunks. The patch preserves the full read-to-EOF result and the shape of
`RecoveryIO`, the parser, the layout, and the recovery and append schedules.
The shared C adapter checks `ferror` before accepting any byte count and
only accepts a short success with EOF. That matters on the legacy path
because Lean's `readBinToEnd` continues after a nonempty short read, and
Lean 4.36's `Handle.read` can discard the earlier positive short
`fread` result's error.

The native boundary-mode fixture injects a positive short read with
`EIO` after the stream reaches byte 1,024. It checks that failure
preceded truncation and that two later opens see the committed batch.
The existing single-file proofs, axiom checks and native fixtures pass.
The proof laws for `RecoveryIO` still describe the same full byte
sequence or a primitive read failure at the reached disk.
Astra's `ConcreteRecovery.RecoveryOps` and `ConcreteOpen.WorkerSteps`
can use the stronger read primitive with the same full-read contract.
`ConcreteOpen.OpenSteps` will need its policy-stamp read premise
instantiated at the new helper. The bounded prefix/drain argument
remains specific to PR #34. This is a viable standalone prerequisite
with a shared C adapter and a narrow Lean delta. See the
[Lean 4.36 runtime](https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/io.cpp).

## Reuse at the scheduled call sites

| Milestone 2 evidence | Reuse in the compact producer |
| --- | --- |
| `StoreAt`, `AcquireIO`, `acquireStore_io`, and `acquireStore_rootLockAt` | Reuse canonical-root, directory and lock provenance, with the same typed empty child slot. These facts carry no payload list. |
| `Store.readControl_fromFile`, `Store.syncRoot_io`, `CollectionIO.collect`, and `Writebacks` | Reuse the exact CONTROL path, bytes, directory descriptor, reached sync alternatives, and selected-namespace frame. Collection must preserve the compact child custody predicate. |
| `ConcreteRecovery.Op`, `RecoveryOps`, `OpenSteps`, `WorkerSteps`, `ChildAt`, and `ValidationIO` | Reuse primitive descriptions and recovery before installation. Reinterpret the data, marker and stamp read premises at the checked read helper. Use the actual compact continuation to install the phase and consume the validated segment once. |
| `ChildAttempt.openExisting`, `ChildMemory.Owns`, `ChildAuthority` and `RuntimeStoreOpen.OpenIO.Custody` | Project the allocated phase and registration to the compact cell types. Carry history in the relation on the reached disk, and carry cursor, file roles, identity and lock in the actual compact phase. Never allocate a cached legacy phase to establish compact ownership. |
| `ControlIO.publish`, append cut frames, successor preparation, release and restart proofs | Reuse the reached primitive reports, fd and inode relations, and durability cases. Phase-dependent append, rotation, interruption and cleanup consumers require the compact phase and registration projection. |
| `StoreIO.recoverChild_selected`, `openExisting_registered_selected`, and L0 `PendingReadScope.twice` | Keep the composition and the retry invariant. Replace the cached child scan and the materialized sealed window with the fold returned by the selected child scopes. Those consumers bind the new proof to their reached disk and exact installed registration. |

The key seam is the value crossing installation. The existing
`Session.view` and child batch lists can still describe the logical
result in propositions. The compact executable stores a cursor,
descriptor roles, the active child registration, the CONTROL metadata
and the active count. The old `scanActiveModel`,
`ChildUseIO.scan` inside recovery, materialized sealed window, and the
history-bearing `installScopedModel` handoff can retire after their last
consumer moves. The abstract contracts, selected-layout invariants,
and primitive durability proofs remain the shared correctness basis.

## This checkpoint and remaining proof obligations

The shared compact schedule now has a compositional postcondition for
CONTROL selection, one open/fold/close per sealed child, active
selection, collection and exact registration. Reported failures unwind
the reached child and root scopes. Stops carry the reached state to a
distinct custody postcondition. The proof computes the fold over the
selected retained history, even if the active OPEN selects a pending
batch. It calculates the exact base and tail from the selected cursor and
layout. The actual load operation carries those bounds and the folded
value into the outer phase-cell and mutex calls.

The checked CONTROL and root-sync interpretation is connected to the
existing root effect laws. The compact active model uses the shared
`resolve_active` witness, as does Astra's producer. A failed compact
active attempt preserves recoverability in the updated child image and
releases the attempted lock. On success the same model returns the
cursor and installed descriptor roles used to establish ready layout.
The sealed model derives unchanged bytes at all cuts from the existing
settled-segment theorem.

The remaining acceptance work is to instantiate the local reports in
one physical world for the compact executable. Connect
`ChildAttempt`'s descriptor/inode provenance through the compact
child phase and the root's actual `IO.Ref` registration. Thread that
identity and the root lock through collection, outer install and
release. Add the issued-world and process-exit interpretation for
compact recovery's cuts, including stops inside open and cleanup.
The next invocation must consume the actual disk and resources
returned by that cleanup or projected by restart. This closes the gap
between the compact schedule proof and Astra's
`PendingReadScope.twice` style of end-to-end continuation. Healthy
progress should use the same local reports with explicit availability
of each primitive. PR #34 remains a draft while this physical
composition is open.
