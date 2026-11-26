# Current handoff

Resume at the native write → crash → reopen → next session boundary.
The [invariant map](proofs/native-storage.md#refinement-boundaries) explains
the argument from filesystem effects to client history. The
[completion checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
owns the full list of obligations.

**What composes today.** On the covered aligned checkpoint path, a successful
open installs the literal returned table. Its next supported writes and snapshot
calls extend the incoming client ledger. The supported calls also determine the
heap, cache and ledger at the next observed checkpoint interruption. The
final manifest-directory sync recovery consumes that position. Failed opens before the file lock,
a refused lock, errors during marked checkpoint, marker and WAL preparation, and partial
pruning of later WAL segments each supply a retry frame under local callback
and cleanup laws. Given such a frame for each failed call, one induction
carries the live files, bounded WAL names, durable files and root binding
to the next open. Thus a
retry can start after an earlier unlink took effect. The canonical keeper
layout supplies the same byte-prefix and cutoff facts to repair, installation
and work accounting. [Failed repair](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean) · [Keeper facts](../lean/Alvoki/Storage/Disk/WalSegmentBoundedRetry.lean)

**Next obligation.** Derive the retry frame for the remaining failed guards and mutating repairs from their actual callbacks. Extend coverage to interrupted
calls, whose handles and durable effects can differ from ordinary errors. A successful reopen needs the held scan to cover all
physical later WAL names. This remains a local filesystem enumeration law.
Mixed sessions and interruptions outside the covered paths remain open.

**Verification baseline.** At `4a7ff54c`, 779 kernel checks, the axiom audit
and its negative control, native fault tests and reproduction passed. For
commands see [local verification](../README.md#reproduce-on-linux-x86-64).
