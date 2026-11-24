import Alvoki.Storage.Disk.CachedMarkedRetryInstallation
import Alvoki.Storage.Disk.LockDescriptionLifetime
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Compose an observed successful close of the old writer with the exact
cached installation from the reached post-close state. The marked opener
can supply `installed` directly from `runOpenWithInstallation_markedRetryFromChunks`.
Close changes ownership while preserving the selected file image, which
forces the reopened checkpoint and committed WAL to match the old writer. -/
theorem SegmentedWriterState.RetainedReady.closeThenCachedReopen
    {directory : DiskDirectory} {oldDescriptor nextRef : Nat} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory oldDescriptor)
    {closeUnlock : UnlockReport} {released : LockedFileState FileImage}
    (closed : runCloseWithFiles directory oldDescriptor closeUnlock
      (.ready state.installed, ⟨state.files, state.owners⟩) = .ok () (.closed, released))
    {layout : CanonicalKeeperLayout released.image state.history}
    (reported : CachedRetryReadReports directory layout)
    (descriptors : DescriptorInventory) (slot : DescriptorSlot) (bindings : FilePath → Option Nat)
    (liveRefs : List Nat) {acquired : Except IO.Error Bool} {unlock : UnlockReport}
    {recover : EStateM IO.Error FileImage Reopened}
    (installed : CachedRetryInstalled reported descriptors slot bindings state.published liveRefs
      (runOpenWithInstallation directory slot.description nextRef acquired unlock recover released)) :
    closeUnlock = .success ∧
    released = ⟨state.files, state.owners.set (directory.file .lock) none⟩ ∧
    ∃ (opened : Reopened) (model : Sequential.SnapshotTable UInt64) (session : SegmentedSession)
      (final : LockedFileState FileImage),
      runOpenWithInstallation directory slot.description nextRef acquired unlock recover released = .ok session final ∧
      session.directory = directory ∧ session.descriptor = reported.inventory.descriptor ∧
      session.phase = .ready opened.installed ∧ final.owners.Owns directory session.descriptor ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs ∧
      final.image.directory.active = state.files.directory.active ∧
      final.image.Ready layout.target ∧ EffectTrace layout.target released.image final.image ∧
      SelectedIntegrityCheckpoint state.published.durable released.image.directory.active.manifest state.checkpoint ∧
      recoverSelected (state.checkpoint.getD (.empty, 0)).1 (WAL.encode state.history) = .ok opened.table ∧
      opened.generation = state.installed.generation ∧ opened.walBytes.toNat = state.installed.walBytes ∧
      opened.table.committed.toNat = state.history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
      RepresentsWalHistory state.history model ∧ opened.table.pins.active = [] := by
  have success : closeUnlock = .success := by
    cases closeUnlock with
    | success => rfl
    | failure cause applied =>
      dsimp only [runCloseWithFiles] at closed
      rw [runClose_open (by simp) (.failure cause applied)] at closed
      cases applied <;> contradiction
  have exactClose := runCloseWithFiles_success (before := ⟨state.files, state.owners⟩)
    (show Phase.ready state.installed ≠ .closed by simp) ready.held
  rw [success] at closed
  have release : released = ⟨state.files, state.owners.set (directory.file .lock) none⟩ :=
    congrArg Prod.snd (EStateM.Result.ok.inj (closed.symm.trans exactClose)).2
  have prior : SelectedIntegrityCheckpoint state.published.durable released.image.directory.active.manifest
      state.checkpoint := by
    rw [release]
    change SelectedIntegrityCheckpoint state.published.durable state.files.directory.active.manifest state.checkpoint
    rw [ready.resumed.ready.selected]
    exact ready.resumed.selected
  obtain ⟨opened, checkpoint, model, session, final, returned, path, descriptor, phase, _, _, _, _, held,
    separate, phaseFresh, sessionFresh, repaired, effects, selected, replay, generation, bytes, _, committed,
    bounds, refines, exactHistory, pins⟩ := installed
  have sameCheckpoint := selected.uniqueResult prior
  have exactBytes : opened.walBytes.toNat = state.installed.walBytes := by
    rw [bytes, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  have samePair : final.image.directory.active = state.files.directory.active :=
    repaired.selected.trans (congrArg (fun files => files.image.directory.active) release)
  rw [sameCheckpoint] at replay generation
  exact ⟨success, release, opened, model, session, final, returned, path, descriptor, phase, held, separate,
    phaseFresh, sessionFresh, samePair, repaired, effects, prior, replay,
    generation.trans ready.resumed.generation.symm, exactBytes, committed,
    bounds, refines, exactHistory, pins⟩

end Alvoki.Storage.DiskSession
