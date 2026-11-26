import Alvoki.Storage.Disk.NativeRotationReadyStorage
import Alvoki.Storage.Disk.NativeRotationWalWindow
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap} {current position : NativeOpenedPosition opened}

local notation "old" => current.current.ready.state
local notation "rotated" => position.current.ready.state

/-- A successful nonempty rotation provides the next write entry. Gaps in the
old WAL interval, apart from the successor, determine the interval available
to later calls. A reboot in that interval reuses the ordinary WAL reader. -/
def OpenRotationObservation.ContinuesWal
    {read create sync entry settled reset} (seen : OpenRotationObservation current read create sync entry settled reset)
    (position : NativeOpenedPosition opened) (root : DeviceInode)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop :=
  NativeReadyStorage old (storage current.reached) →
  seen.LocalFrames (fun a b => (storage a).Frames (old).crashPath (storage b)) →
  (seen.view.files position.reached).image.ObservesWalChild root position.current.ready.state.session.directory
    position.current.ready.state.writer.wal.active.first (storage position.reached) (visible position.reached) →
  position.WriteStorageEntry seen.view (seen.writeCache position) (storage position.reached) (visible position.reached) ∧
  ∀ through,
    (∀ start ≤ through, start ≠ (old).writer.wal.active.last →
      (old).writer.wal.SettledNamespaceWindow (old).session.directory start start (storage current.reached)) →
    seen.LocalFrames (fun a b => RotationWalNameFrame (old).session.directory 0 through (old).writer.wal.active.last
      (storage a) (storage b)) →
    position.WalWindowAt storage 0 through ∧
    ∀ {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
      (images : heap → FileImage) {rebooted : heap} (namespaceView : DirectoryReadNamespace) (heldRoot : DeviceInode),
      let view := seen.view.withFileProjection (fun h => ⟨images h, (seen.view.files h).owners⟩)
      ∀ sample : RawWriteRebootEntry position.current.ready.state view storage (fun h => (storage h).files.names) visible position.reached rebooted,
        sample.DurableReset → position.current.ready.state.writer.target.range.through ≤ through → (old).writer.target.pair.manifest = none →
        source.ReadsClientHistoryAtOpen view position.current.ready.state.session.directory
          storage visible rebooted namespaceView heldRoot
          current.current.submissions current.current.ready.reads current.current.history

private theorem OpenRotationObservation.Reached.continuesWal
    {read create sync entry settled reset} {seen : OpenRotationObservation current read create sync entry settled reset}
    {lookup} (returned : seen.Reached lookup position)
    {next : NativeReadPosition current.current.history current.current.submissions}
    (atState : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    (rotation : NativeRotationFrame current.current.ready next)
    (manifest : (rotated).writer.target.pair.manifest = (old).writer.target.pair.manifest)
    {root storage visible}
    (entryAt : NativeReadyStorage old (storage current.reached) →
      seen.LocalFrames (fun a b => (storage a).Frames (old).crashPath (storage b)) →
      (seen.view.files position.reached).image.ObservesWalChild root (rotated).session.directory
        (rotated).writer.wal.active.first (storage position.reached) (visible position.reached) →
      position.WriteStorageEntry seen.view (seen.writeCache position) (storage position.reached) (visible position.reached)) :
    seen.ContinuesWal position root storage visible := by
  intro initial keeps child
  have ready := entryAt initial keeps child
  refine ⟨ready, ?_⟩
  intro through gaps names
  have catalog := returned.walWindow atState rotation storage (fun _ _ => Nat.zero_le _) (fun s _ => gaps s)
    names ready.physical.activeWalPresent
  refine ⟨catalog, ?_⟩
  intro stream source images rebooted namespaceView heldRoot view sample reset within absent
  obtain ⟨valid, history, pending⟩ := position.current.ready.readPrefix.refines
  have opens := @RawWriteRebootEntry.replaysWalBeforeCheckpointAtOpen _ _ _ _ source _ _ _ _ namespaceView heldRoot
    sample valid ready.physical reset (catalog.restrictUpper within).2 (manifest.trans absent)
  have sameHistory : position.current.history = current.current.history := by rw [atState]
  rw [history.trans sameHistory] at opens
  rw [atState] at pending
  change PendingClientReplay current.current.submissions next.reads current.current.history at pending
  rw [rotation.reads] at pending
  intro input returnedAt table
  exact opens.recordsReads pending (input := input) (returnedAt := returnedAt) (table := table)

/-- The exclusive-create route supplies the postcondition at the actual return. -/
theorem NativeOpenedPosition.rotatesCreatedWithWal
    (report : NativeReadyCreatedRotation old) (seen : OpenRotationObservation.Created current report)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :
    ∃ position, seen.Reached report.lookup position ∧ NativeExecutionStep current.current .rotatedWal position.current ∧
      seen.ContinuesWal position report.parent.root storage visible := by
  obtain ⟨next, position, rotation, step, atState, returned⟩ := current.rotatesCreatedOnOpenPhase report seen
  refine ⟨position, returned, step, returned.continuesWal atState rotation.frame ?_ ?_⟩
  · rw [atState]; change next.state.writer.target.pair.manifest = _
    rw [rotation.reached]; rfl
  · exact rotation.writeStorageEntry returned atState

/-- The same continuation also follows the observed reuse of a private empty successor. -/
theorem NativeOpenedPosition.rotatesExistingWithWal
    (report : NativeReadyExistingRotation old) (seen : OpenRotationObservation.Existing current report)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :
    ∃ position, seen.Reached report.opened.lookup position ∧ NativeExecutionStep current.current .rotatedWal position.current ∧
      seen.ContinuesWal position report.opened.root storage visible := by
  obtain ⟨next, position, rotation, step, atState, returned⟩ := current.rotatesExistingOnOpenPhase report seen
  refine ⟨position, returned, step, returned.continuesWal atState rotation.frame ?_ ?_⟩
  · rw [atState]; change next.state.writer.target.pair.manifest = _
    rw [rotation.reached]; rfl
  · exact rotation.writeStorageEntry returned atState

end Alvoki.Storage.DiskSession
