# Disk proofs

Proof modules retain the `Alvoki.Storage` namespaces of their declarations. Their paths group related claims and observations:

- [Append](Append), [WAL](WAL), [Write](Write), [Rotation](Rotation) and [Keeper](Keeper) cover the WAL write and recovery paths.
- [Bootstrap](Bootstrap), [Checkpoint](Checkpoint), [Collection](Collection) and [Recovery](Recovery) cover initialization, publication, cleanup and reopening.
- [Read](Read), [Session](Session) and [Filesystem](Filesystem) cover read histories, session models and filesystem observations.
- [Native](Native) groups native execution observations by checkpoint, execution, open, recovery and WAL.

## Topics and proof boundaries

The directories primarily name a **topic**, not a single level of abstraction.
To understand what a particular theorem covers, follow its statement and the
observations it assumes:

1. A **protocol model** describes allowed states and transitions, independently
   of a particular filesystem execution.
2. An **executable refinement** relates an operation or its result to a model;
   check which actual implementation the statement mentions.
3. A **native effect proof** relates reported calls and filesystem observations
   to the state used by a model, under explicit filesystem assumptions.
4. A **composition** connects established boundaries to a caller-visible
   guarantee. Some compositions still require observations as inputs; full
   production coverage remains an open obligation.

For example, [Recovery](Recovery) includes reopening and installation cases,
while [Native/Recovery](Native/Recovery) follows reported native open and scan
effects. [WAL](WAL) includes segment identity and commit effects, whereas
[Native/WAL](Native/WAL) relates reported native WAL effects to these boundaries.
These are overlapping subjects, not competing implementations or an assurance
that every theorem in a directory occupies the same layer. The
[proof architecture](../../../../../docs/proof-architecture.md) explains how
the layers compose and where the remaining gaps lie.

**Follow an interrupted write.** In `readsAfterInterruptedSecondBatch`, a fresh session has already acknowledged its first batch when the second write stops at the directory sync. Follow the issued callback to see which publication steps have completed. Then follow the chosen crash image to see which bytes recovery can use. Earlier acknowledgements and the whole-or-absent second batch share one history. The theorem takes observations of the filesystem effects and reboot as inputs. [Fresh session](Native/Open/NativeFreshOpenedSessions.lean) · [Issued write stop](Write/NativeRawWriteRootStop.lean) · [Refinement boundaries](../../../../../docs/proofs/native-storage.md#refinement-boundaries)

The [proof index](../../../../../docs/proof-index.md) links claims to their consumers and the [roadmap](../../../../../docs/proof-roadmap.md) records open obligations.
