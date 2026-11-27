# Disk proofs

Proof modules retain the `Alvoki.Storage` namespaces of their declarations. Their paths group related claims and observations:

- [Append](Append), [WAL](WAL), [Write](Write), [Rotation](Rotation) and [Keeper](Keeper) cover the WAL write and recovery paths.
- [Bootstrap](Bootstrap), [Checkpoint](Checkpoint), [Collection](Collection) and [Recovery](Recovery) cover initialization, publication, cleanup and reopening.
- [Read](Read), [Session](Session) and [Filesystem](Filesystem) cover read histories, session models and filesystem observations.
- [Native](Native) groups native execution observations by checkpoint, execution, open, recovery and WAL.

**Follow an interrupted write.** In `readsAfterInterruptedSecondBatch`, a fresh session has already acknowledged its first batch when the second write stops at the directory sync. Follow the issued callback to see which publication steps have completed. Then follow the chosen crash image to see which bytes recovery can use. Earlier acknowledgements and the whole-or-absent second batch share one history. The theorem takes observations of the filesystem effects and reboot as inputs. [Fresh session](Native/Open/NativeFreshOpenedSessions.lean) · [Issued write stop](Write/NativeRawWriteRootStop.lean) · [Refinement boundaries](../../../../../docs/proofs/native-storage.md#refinement-boundaries)

The [proof index](../../../../../docs/proof-index.md) links claims to their consumers and the [roadmap](../../../../../docs/proof-roadmap.md) records open obligations.
