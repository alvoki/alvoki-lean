import Alvoki.Storage.Disk.CachedRetryInstallation
import Alvoki.Storage.Disk.SessionReadGuards

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)
open WalSegmentRepair

/-- The table returned by the cached marked opener uses the exact selected
checkpoint and retained WAL. Snapshot acquisition and reads use that returned
session's phase and token. The native pointer comparisons are observed. -/
theorem CachedRetryInstalled.guardedSnapshotReads
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history}
    {reported : CachedRetryReadReports directory layout}
    {descriptors slot bindings published liveRefs result}
    (installed : CachedRetryInstalled reported descriptors slot bindings published liveRefs result) :
    ∃ (opened : Reopened) (checkpoint : Option (PackedTable × UInt64)) (reference : SnapshotTable UInt64)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      result = .ok session final ∧ session.directory = directory ∧
      session.descriptor = reported.inventory.descriptor ∧ session.phase = .ready opened.installed ∧
      final.owners.Owns directory session.descriptor ∧
      SelectedIntegrityCheckpoint published.durable before.image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      SnapshotWalReplay .empty history reference ∧
      (∀ snapshot, ¬ (opened.table.pins.floor ≤ snapshot ∧ snapshot ≤ opened.table.committed) →
        session.runAcquireAt snapshot = .ok none session) ∧
      ∀ snapshot, opened.table.pins.floor ≤ snapshot → snapshot ≤ opened.table.committed →
        ∃ (pin : SnapshotPin) (pinned : PackedTable) (after : SegmentedSession),
          session.runAcquireAt snapshot = .ok (some (session.sessionRef, pin)) after ∧
          after.phase = .ready { opened.installed with table := pinned } ∧
          after.sessionRef = session.sessionRef ∧ pin.sequence = snapshot ∧ pin ∈ pinned.pins.active ∧
          (∀ compared : Bool, compared = decide (session.sessionRef = after.sessionRef) →
            (∀ key, readWithHandle (.ready pinned) compared (fun table => table.lookup pin.handle key) =
              .ok (some (reference.table.lookup key snapshot))) ∧
            ∀ start stop, readWithHandle (.ready pinned) compared
                (fun table => table.range pin.handle start stop) =
              .ok (some (reference.table.range start stop snapshot))) ∧
          ∀ issuer ∈ liveRefs, ∀ compared : Bool, compared = decide (issuer = after.sessionRef) →
            ∀ handle : SnapshotHandle,
              (∀ key, readWithHandle (.ready pinned) compared (fun table => table.lookup handle key) =
                .ok none) ∧
              ∀ start stop, readWithHandle (.ready pinned) compared
                  (fun table => table.range handle start stop) = .ok none := by
  obtain ⟨opened, checkpoint, model, session, final, returned, path, descriptor, phase, _, _, _, _, held,
    _, _, fresh, _, _, selected, replay, _, _, _, _, bounds, refined, represented, _⟩ := installed
  have existingReplay := represented
  obtain ⟨reference, replayed, _⟩ := existingReplay
  refine ⟨opened, checkpoint, reference, session, final, returned, path, descriptor, phase, held,
    selected, replay, replayed,
    fun _ unsupported => SegmentedSession.runAcquireAt_unsupported phase unsupported, ?_⟩
  intro snapshot floor committed
  have available : (opened.table.acquireAt snapshot).isSome = true := by
    simpa only [PackedTable.acquireAt, Option.isSome_map] using
      (SnapshotPins.acquire_iff opened.table.pins _ _).mpr ⟨floor, committed⟩
  obtain ⟨⟨pin, pinned⟩, acquired⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨_, pinnedRefined, pinnedRepresents⟩ := represented.acquireAt refined bounds acquired
  have pinSpec := PackedTable.acquireAt_spec acquired
  obtain ⟨lookup, range⟩ := pinnedRepresents.packedPinnedReads pinnedRefined replayed pinSpec.active
  let after := { session with phase := .ready { opened.installed with table := pinned } }
  refine ⟨pin, pinned, after, SegmentedSession.runAcquireAt_ready phase acquired, rfl, rfl,
    pinSpec.sequence, pinSpec.active, ?_, ?_⟩
  · intro compared observed
    have same : compared = true := observed.trans (decide_eq_true rfl)
    rw [same]
    exact ⟨fun key => congrArg Except.ok (pinSpec.sequence ▸ lookup key),
      fun start stop => congrArg Except.ok (pinSpec.sequence ▸ range start stop)⟩
  · intro issuer old compared observed handle
    have foreign : issuer ≠ after.sessionRef := by
      intro same
      exact fresh (same ▸ old)
    exact ⟨fun key => readWithHandle_foreign pinned _ observed foreign,
      fun start stop => readWithHandle_foreign pinned _ observed foreign⟩

end Alvoki.Storage.DiskSession
