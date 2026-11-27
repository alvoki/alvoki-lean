# Disk proofs

Proof modules retain the `Alvoki.Storage` namespaces of their declarations. Their paths group related claims and observations:

- [Append](Append), [WAL](WAL), [Write](Write), [Rotation](Rotation) and [Keeper](Keeper) cover the WAL write and recovery paths.
- [Bootstrap](Bootstrap), [Checkpoint](Checkpoint), [Collection](Collection) and [Recovery](Recovery) cover initialization, publication, cleanup and reopening.
- [Read](Read), [Session](Session) and [Filesystem](Filesystem) cover read histories, session models and filesystem observations.
- [Native](Native) groups native execution observations by checkpoint, execution, open, recovery and WAL.

The [proof index](../../../../../docs/proof-index.md) links claims to their consumers and the [roadmap](../../../../../docs/proof-roadmap.md) records open obligations.
