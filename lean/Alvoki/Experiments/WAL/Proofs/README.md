# Single-file WAL proofs

These proofs concern the [single-file WAL experiment](../README.md), not the
production segmented WAL. Start with the client result
[`Confirmed.recover`](Client.lean), then follow [append](Append.lean),
[marker](Marker.lean), [scan](Scan.lean), and [persistence](Persistence.lean)
for its supporting boundaries.

The result is conditional on the modeled crash outcomes and experimental
limits. The [design's proof summary](../../../../../docs/design/wal-recovery.md#what-the-single-file-proof-establishes)
states those assumptions and what remains outside the theorem. Run
`bash scripts/check-wal-recovery-slice.sh` from the repository root for the
slice's kernel and axiom checks, simulations and Linux fixtures.
