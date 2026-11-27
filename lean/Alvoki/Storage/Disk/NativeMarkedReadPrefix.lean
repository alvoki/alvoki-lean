import Alvoki.Storage.Disk.CapturedMarkedInstallation
import Alvoki.Storage.Disk.Proofs.Read.NativeReadyReadPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- Reports for the final healthy held open. The retry prefix supplies the
physical image and selects the checkpoint before these reports are used. -/
structure MarkedReadyOpenObservations (input : FilePath) (directory : DiskDirectory)
    (inventory : DescriptorInventory) (retry : LockedFileState FileImage)
    {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (published : CheckpointPublication.Image) (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  admission : CensusOpenAdmissionReports input directory inventory retry
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout published
  finish : CapturedKeeperFinish callbacks reads vacant selected
  chronology : CapturedMarkedReadCensus reads finish.reader
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

/-- Seed the same ready read prefix after any successful marked repair.
The writer, ownership and replay all come from that one returned open. -/
theorem CapturedKeeperFinish.startsNativeReadPrefix
    (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    (pending : PendingClientReplay log recorded history)
    (bounded : ∀ read ∈ recorded, read.BoundedBy history.length) :
    ∃ state, NativeReadyReadPrefix (finish.run chronology) state history log recorded state ∧
      state.cache = admission.cache ∧ state.census = finish.census ∧ state.owner = admission.owner ∧
      state.directorySlot = admission.cached ∧ state.files.image.directory.active = retry.image.directory.active ∧
      state.writer.published.durable = published.durable ∧ state.writer.checkpoint = checkpoint ∧
      state.session.directory = directory ∧ state.writer.target = layout.target ∧
      state.files.image.kept = retry.image.kept ∧
      state.writer.wal = { wal with directory := state.files.image.directory } ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok state.writer.installed.table ∧
      state.session.phaseRef ∉ calls.liveRefs ∧ state.session.sessionRef ∉ calls.liveRefs := by
  obtain ⟨session, final, returned, pair, ownerLive, directoryLive, installed⟩ :=
    finish.installsFromCensus chronology marker laterValid following accepted ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ordered
  obtain ⟨sameSession, sameFinal, writer, indexed, path, description, phase, files, owners, retainedWal, target,
    exactHistory, _, durable, ready⟩ := appendReady.writerRetained walLayout walValid spans active keeper kept
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  let state : NativeReadyState := ⟨session, writer, finish.census, admission.cache, admission.owner, admission.cached⟩
  have exactFiles : state.files = final := by
    change (⟨writer.files, writer.owners⟩ : LockedFileState FileImage) = final
    rw [files, owners]
  have valid : state.Valid :=
    ⟨phase, description.symm, ownerLive, directoryLive, ⟨admission.reached, rfl⟩, path.symm ▸ description.symm ▸ ready⟩
  have chosen := ready.resumed.selected
  rw [target, durable] at chosen
  have seals : state.files.image.kept = retry.image.kept := by
    change writer.files.kept = retry.image.kept
    rw [ready.sealedFiles, retainedWal]
    exact kept.symm
  obtain ⟨_, _, _, _, sameReturn, samePhase, replaySelection, replay, _⟩ :=
    CachedRetryInstalled.refinesPendingClient installed pending
  have sameSession := (EStateM.Result.ok.inj sameReturn).1
  have sameInstalled := Phase.ready.inj (phase.symm.trans (sameSession.symm ▸ samePhase))
  have exactReplay : recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) =
      .ok state.writer.installed.table := by
    change recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok writer.installed.table
    rw [sameInstalled, ← replaySelection.uniqueResult selected]
    exact replay
  have exactWal : state.writer.wal = { wal with directory := state.files.image.directory } := by
    rw [exactFiles]
    exact retainedWal
  have freshness : session.phaseRef ∉ calls.liveRefs ∧ session.sessionRef ∉ calls.liveRefs := by
    obtain ⟨_, _, _, _, _, indexed, _, _, _, _, _, _, _, _, _, phaseFresh, sessionFresh, _⟩ := installed
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
    exact ⟨phaseFresh, sessionFresh⟩
  exact ⟨state, .installed (exactFiles.symm ▸ returned) valid exactHistory pending bounded,
    rfl, rfl, rfl, rfl, exactFiles.symm ▸ pair, durable, chosen.uniqueResult selected, path, target, seals, exactWal, exactReplay,
    freshness.1, freshness.2⟩

end Alvoki.Storage.DiskSession
