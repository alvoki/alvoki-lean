# Current handoff

Resume at the native write → crash → reopen → next session boundary.
The [invariant map](proofs/native-storage.md#refinement-boundaries) explains
the argument from filesystem effects to client history. The
[completion checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
owns the full list of obligations.

**What composes today.** On the covered aligned checkpoint path, a successful
open installs the literal returned table. Its next supported writes and snapshot
calls extend the incoming client ledger. Failed opens before the file lock,
a refused lock, and partial pruning of later WAL segments have local proofs
that carry protected storage to the heap reached by the public error. Thus a
retry can start after an earlier unlink took effect. The canonical keeper
layout supplies the same byte-prefix and cutoff facts to repair, installation
and work accounting. [Failed repair](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean) · [Keeper facts](../lean/Alvoki/Storage/Disk/WalSegmentBoundedRetry.lean)

**Next obligation.** Derive the retry frame for remaining failed reads and
repairs through their actual cleanup, then feed that frame to the existing
failed-call induction. A successful reopen needs the held scan to cover all
physical later WAL names. This remains a local filesystem enumeration law.
Mixed sessions and interruptions outside the covered paths remain open.

**Verification baseline.** At `a758f0ad`, 779 kernel checks, the axiom audit
and its negative control, native fault tests and reproduction passed. For
commands see [local verification](../README.md#reproduce-on-linux-x86-64).
Earlier delivery notes and their source links remain available in the
[pinned handoff history](https://github.com/alvoki/alvoki-lean/blob/a758f0adf2ee8df0e38eb9b28d84cfdbed866115/docs/progress.md).
