import Alvoki.Storage.Disk.Recovery

namespace Alvoki.Storage

open Alvoki.Sequential (SnapshotTable)

namespace SnapshotWalReplay

/-- Successive abstract replays preserve the order of the complete submission list. -/
theorem append {before middle after : SnapshotTable UInt64} {prefixWrites suffix : List WAL.Write}
    (first : SnapshotWalReplay before prefixWrites middle)
    (second : SnapshotWalReplay middle suffix after) :
    SnapshotWalReplay before (prefixWrites ++ suffix) after := by
  induction first with
  | nil => exact second
  | cons written sequence _ ih => exact .cons written sequence (ih second)

theorem split {before after : SnapshotTable UInt64} {prefixWrites suffix : List WAL.Write}
    (replayed : SnapshotWalReplay before (prefixWrites ++ suffix) after) :
    ∃ middle, SnapshotWalReplay before prefixWrites middle ∧ SnapshotWalReplay middle suffix after := by
  induction prefixWrites generalizing before with
  | nil => exact ⟨before, .nil _, replayed⟩
  | cons _ _ ih =>
    cases replayed with
    | cons written sequence remaining =>
      obtain ⟨middle, first, second⟩ := ih remaining
      exact ⟨middle, .cons written sequence first, second⟩

theorem committed_count {before after : SnapshotTable UInt64} {events : List WAL.Write}
    (played : SnapshotWalReplay before events after) :
    after.committed.toNat = before.committed.toNat + events.length := by
  induction played with
  | nil => simp
  | cons written _ _ ih =>
    rw [ih, (SnapshotTable.write_spec written).1, List.length_cons]
    omega

theorem ordinals {before after : SnapshotTable UInt64} {events : List WAL.Write}
    (played : SnapshotWalReplay before events after) :
    WAL.OrdinalsFrom (before.committed.toNat + 1) events := by
  induction played with
  | nil => trivial
  | cons written sequence _ ih =>
    have count := (SnapshotTable.write_spec written).1
    exact ⟨by rw [← sequence, count], by simpa only [count] using ih⟩

theorem pins {before after : SnapshotTable UInt64} {events : List WAL.Write}
    (played : SnapshotWalReplay before events after) : after.pins = before.pins := by
  induction played with
  | nil => rfl
  | cons written _ _ ih => exact ih.trans (SnapshotTable.write_spec written).2.1

/-- Each event certifies a representable next ordinal. The abstract write
operation can therefore replay the whole consecutive suffix from its starting clock. -/
theorem of_ordinals (before : SnapshotTable UInt64) (events : List WAL.Write)
    (ordered : WAL.OrdinalsFrom (before.committed.toNat + 1) events) :
    ∃ after, SnapshotWalReplay before events after := by
  induction events generalizing before with
  | nil => exact ⟨before, .nil before⟩
  | cons event rest ih =>
    obtain ⟨ordinal, tail⟩ := ordered
    have fits : before.committed.toNat + 1 < UInt64.size := ordinal ▸ event.sequence.toNat_lt_size
    have canWrite := (before.write_iff event.key event.value).mpr fits
    obtain ⟨next, written⟩ := Option.isSome_iff_exists.mp canWrite
    have count := (SnapshotTable.write_spec written).1
    have sequence := UInt64.toNat_inj.mp (count.trans ordinal.symm)
    have restOrdered : WAL.OrdinalsFrom (next.committed.toNat + 1) rest := by rwa [count]
    obtain ⟨after, replayed⟩ := ih next restOrdered
    exact ⟨after, .cons written sequence replayed⟩

/-- A consecutive history starting at one defines the abstract state of a fresh database. -/
theorem fromEmpty (events : List WAL.Write) (ordered : WAL.OrdinalsFrom 1 events) :
    ∃ after, SnapshotWalReplay (SnapshotTable.empty : SnapshotTable UInt64) events after :=
  of_ordinals .empty events ordered

theorem deterministic {before left right : SnapshotTable UInt64} {events : List WAL.Write}
    (first : SnapshotWalReplay before events left) (second : SnapshotWalReplay before events right) :
    left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons written _ _ ih =>
    cases second with
    | cons other _ remaining =>
      cases Option.some.inj (written.symm.trans other)
      exact ih remaining

end SnapshotWalReplay

end Alvoki.Storage
