import Alvoki.Storage.Disk.CachedMarkedRetryInstallation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Reports at the reached calls before exclusive acquisition. Append-open
can create `LOCK`, which is outside the recovered `FileImage` projection.
The later flock report must still identify the exact opened description
and its canonical lock binding at acquisition. The model uses the file
and owner view reached at acquisition, and checks the flat WAL again
with the separate locked observation. -/
structure OpenAdmissionReports (input : FilePath) (directory : DiskDirectory) (slot : DescriptorSlot) where
  realPath : FilePath → Except IO.Error FilePath
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  openAppend : FilePath → Except IO.Error DescriptorSlot
  resolved : realPath input = .ok directory.path
  flatAbsent : ∃ name message, lookup (directory.file .wal) = .error (.noFileOrDirectory name 2 message)
  lockGuard :
    (∃ name message, lookup (directory.file .lock) = .error (.noFileOrDirectory name 2 message)) ∨
    ∃ metadata, lookup (directory.file .lock) = .ok metadata ∧ metadata.type = .file ∧ metadata.numLinks = 1
  opened : openAppend (directory.file .lock) = .ok slot

/-- The native admission projection reaches acquisition with precisely the
resolved directory and the append-open's returned slot. The effects before
flock preserve the projected data and owner state. -/
theorem OpenAdmissionReports.admits {image result : Type} {input : FilePath} {directory : DiskDirectory}
    {slot : DescriptorSlot} (observed : OpenAdmissionReports input directory slot)
    (acquire : DiskDirectory → DescriptorSlot → EStateM IO.Error image result) (before : image) :
    DiskTable.withOpenAdmission input (fun path => liftExcept (observed.realPath path))
      (fun path => pure (observed.lookup path)) (fun path => liftExcept (observed.openAppend path)) acquire before =
      acquire directory slot before := by
  have checkedPath := DiskDirectory.openWith_reported (before := before) (input := input)
    (fun path => liftExcept (observed.realPath path)) directory (by
      simp [observed.resolved, liftExcept, Pure.pure, EStateM.pure])
  simp only [DiskTable.withOpenAdmission, Bind.bind, EStateM.bind, checkedPath]
  obtain ⟨name, message, absent⟩ := observed.flatAbsent
  rcases observed.lockGuard with ⟨_, _, missing⟩ | ⟨metadata, present, regular, single⟩
  · simp [Bind.bind, EStateM.bind, rejectFlatWalWith,
      optionalMetadataWith, absent, missing, liftExcept, observed.opened, Pure.pure, EStateM.pure]
  · have fileKind : (IO.FS.FileType.file == .file) = true := rfl
    simp [Bind.bind, EStateM.bind, rejectFlatWalWith, optionalMetadataWith, checkPrivateRegularWith, absent,
      present, regular, single, fileKind, liftExcept, observed.opened, Pure.pure, EStateM.pure]

/-- Compose the pre-lock native admission projection with the marked
installer. The chunk reports belong to the actual append-open slot and
reported flock at the resolved directory, and the locked schedule probes
for a flat WAL again. -/
theorem runOpenWithAdmission_markedRetryFromChunks {files : Type} {input : FilePath}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    (admission : OpenAdmissionReports input directory observed.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    CachedRetryInstalled (before := before) observed.reported observed.descriptors observed.slot observed.bindings
      published observed.liveRefs
      (DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
        (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path))
        observed.runAt before) := by
  rw [admission.admits]
  exact runOpenWithInstallation_markedRetryFromChunks observed keeperValid laterValid following accepted ordered

end Alvoki.Storage.DiskSession
