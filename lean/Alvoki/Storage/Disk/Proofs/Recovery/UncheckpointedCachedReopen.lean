import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCleanReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Healthy reads of a marked WAL before the first checkpoint. Optional
file reports concern the marker and manifest. Sealed and keeper payloads
come from the bounded callbacks actually used by the cached worker. -/
structure UncheckpointedCachedReadReports (directory : DiskDirectory) (state : SegmentedWriterState) where
  paths : OpenPathReadReports
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  entries : Array IO.FS.DirEntry
  listing : list directory.path = .ok entries
  unique : (entries.toList.map (·.fileName)).Nodup
  names : ∀ first, renderWalSegmentName first ∈ entries.toList.map (·.fileName) ↔
    first ∈ state.wal.segments.map WalSegment.first
  regular : ∀ first ∈ state.wal.segments.map WalSegment.first, ∃ metadata,
    paths.lstat (directory.file (.walSegment first)) = .ok metadata ∧
      metadata.type = .file ∧ metadata.numLinks = 1
  noCheckpoint : state.wal.directory.active.manifest = none
  manifest : paths.readOptional (directory.file .manifest) = .ok none
  marker : paths.readOptional (directory.file .walBoundary) = .ok state.wal.directory.active.walBoundary
  bounded : CachedWalFileReports directory paths state.wal state.target.range.watermark ByteArray.empty

namespace UncheckpointedCachedReadReports

variable {directory : DiskDirectory} {state : SegmentedWriterState}

/-- The legacy seal report is derived from the observed extent and prefix,
without requiring a separate whole-file read. -/
private def referencePaths (observed : UncheckpointedCachedReadReports directory state) : OpenPathReadReports where
  lstat := observed.paths.lstat
  readBin := fun path =>
    if path = directory.file .manifest ∨ path = directory.file .walBoundary then observed.paths.readBin path
    else do
      let metadata ← observed.paths.lstat path
      observed.bounded.readSeal path metadata.byteSize.toNat

private theorem referenceOptional (observed : UncheckpointedCachedReadReports directory state) {path : FilePath}
    (selected : path = directory.file .manifest ∨ path = directory.file .walBoundary) :
    observed.referencePaths.readOptional path = observed.paths.readOptional path := by
  simp [OpenPathReadReports.readOptional, referencePaths, selected]

private theorem sealPathSeparate (directory : DiskDirectory) (first : Nat) :
    ¬ (directory.file (.walSegment first) = directory.file .manifest ∨
       directory.file (.walSegment first) = directory.file .walBoundary) := by
  rintro (manifest | marker)
  · obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive manifest.symm
    contradiction
  · obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive marker.symm
    contradiction

private def reference (observed : UncheckpointedCachedReadReports directory state)
    {owners : LockOwners} {descriptor : Nat} (held : owners.Owns directory descriptor) :
    HealthyCheckpointCutReports directory owners descriptor state.wal state.wal.directory.active
      state.target.range.watermark state.published.durable where
  list := observed.list
  entries := observed.entries
  listing := observed.listing
  reports := observed.referencePaths
  readPrefix := fun path count => do
    let metadata ← observed.paths.lstat path
    let bytes ← observed.bounded.readKeeper path count metadata.byteSize.toNat
    pure ⟨bytes, metadata.byteSize.toNat⟩
  held := held
  unique := observed.unique
  names := observed.names
  regular := observed.regular
  manifest := (observed.referenceOptional (.inl rfl)).trans (observed.noCheckpoint.symm ▸ observed.manifest)
  marker := (observed.referenceOptional (.inr rfl)).trans observed.marker
  runs := by
    intro _ _ chosen
    simp [observed.noCheckpoint] at chosen
  sealed := by
    intro segment chosen
    have member : segment ∈ state.wal.segments := by
      have readDescriptor : segment ∈ state.wal.readDescriptors state.target.range.watermark :=
        List.dropLast_subset _ chosen
      unfold WalSegmentImage.readDescriptors at readDescriptor
      split at readDescriptor
      · exact (List.mem_filter.mp readDescriptor).1
      · exact List.mem_append_right _ readDescriptor
    obtain ⟨metadata, reported, _, _⟩ := observed.regular segment.first (List.mem_map.mpr ⟨_, member, rfl⟩)
    obtain ⟨size, _, payload⟩ := observed.bounded.sealed segment chosen metadata reported
    simp [referencePaths, sealPathSeparate, reported, size, payload, Bind.bind, Except.bind]
  keeper := by
    have member : state.wal.active.first ∈ state.wal.segments.map WalSegment.first :=
      List.mem_map.mpr ⟨_, List.mem_append_right _ (by simp), rfl⟩
    obtain ⟨metadata, reported, _, _⟩ := observed.regular state.wal.active.first member
    obtain ⟨size, payload⟩ := observed.bounded.keeper metadata reported
    rw [size] at payload
    simp only [reported, Bind.bind, Except.bind, payload, Pure.pure, Except.pure, size]

/-- With an absent manifest, the native cached reads and two reached sync
reports suffice to reopen the same settled WAL after clean close. -/
theorem reopens {oldDescriptor nextDescriptor nextRef : Nat}
    (observed : UncheckpointedCachedReadReports directory state)
    (ready : state.RetainedReady directory oldDescriptor)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (syncDirectory : sync #[directory.path] state.files = .ok () state.files)
    (syncKeeper : sync #[directory.file (.walSegment state.wal.active.first)] state.files = .ok () state.files) :
    let released := SegmentedCleanReopenReport.released directory state
    let recover := reopenMarkedBoundedWithCachedExtents directory
      (fun path => liftExcept (observed.paths.readOptional path))
      (fun path => liftExcept (checkpointRunSizeReport observed.paths path))
      (fun path count => liftExcept (readRunPrefix path count))
      (fun path => liftExcept (observed.list path))
      (fun path => liftExcept (.ok (observed.paths.lstat path) : Except IO.Error _))
      (fun path count => liftExcept (observed.bounded.readSeal path count))
      (fun path count size => liftExcept (observed.bounded.readKeeper path count size))
      removeFile write sync renameFile
    runCloseWithFiles directory oldDescriptor .success (.ready state.installed, ⟨state.files, state.owners⟩) =
      .ok () (.closed, released) ∧
    ∃ (after : SegmentedWriterState) (session : SegmentedSession) (final : LockedFileState FileImage),
      runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock recover released = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners ∧
      final.image = state.files ∧ after.history = state.history ∧ after.checkpoint = none ∧
      recoverSelected .empty (WAL.encode state.history) = .ok after.installed.table ∧
      after.RetainedReady directory nextDescriptor := by
  intro released recover
  have held : (released.owners.set (directory.file .lock) (some nextDescriptor)).Owns directory nextDescriptor := by
    simp [LockOwners.Owns, LockOwners.set]
  let raw := observed.reference held
  let sizes : SizedCheckpointRunReports directory raw.reports state.wal.directory.active.manifest state.published.durable :=
    ⟨readRunPrefix, by intro _ _ chosen; simp [observed.noCheckpoint] at chosen⟩
  let cached : CachedWalFileReports directory raw.reports state.wal state.target.range.watermark ByteArray.empty :=
    ⟨observed.bounded.readSeal, observed.bounded.readKeeper, observed.bounded.sealed, observed.bounded.keeper⟩
  let report : SegmentedCleanReopenReport directory state oldDescriptor nextDescriptor :=
    ⟨nextRef, liveRefs, unlock, raw, removeFile, write, sync, renameFile⟩
  have valid : report.Valid := ⟨fresh, syncDirectory, syncKeeper⟩
  have same : raw.reopenCached sizes cached removeFile write sync renameFile = recover := by
    unfold HealthyBoundedWalReports.reopenCached HealthyBoundedWalReports.reopenCachedWithState
    simp only [recover, reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, raw, reference,
      observed.referenceOptional (.inl rfl), observed.referenceOptional (.inr rfl)]
    rfl
  obtain ⟨after, session, final, endpoint, ran, phase, image, owners⟩ :=
    report.installsRetainedCached valid ready sizes cached
  have run : runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
      (raw.reopenCached sizes cached removeFile write sync renameFile) released = .ok session final := ran
  rw [same] at run
  have absent : state.checkpoint = none := by
    have selected := ready.resumed.selected
    rw [← ready.walPair, observed.noCheckpoint] at selected
    cases checkpoint : state.checkpoint with
    | none => rfl
    | some _ => rw [checkpoint] at selected; cases selected
  obtain ⟨_, _, _, _, _, _, writer⟩ := endpoint.openEffect
  refine ⟨endpoint.closeEffect, after, session, final, run, phase, image, owners, ?_, ?_, ?_, ?_,
    endpoint.preservesRetained valid ready⟩
  · rw [image, writer]
    rfl
  · rw [writer]
    rfl
  · rw [writer]
    exact absent
  · simpa [absent] using endpoint.replay

end UncheckpointedCachedReadReports

end Alvoki.Storage.DiskSession
