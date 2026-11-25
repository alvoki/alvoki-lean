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

/-- A reported flat WAL binding ends admission at the resolved path, with
no append-open or lock acquisition. The metadata lookup is read-only. -/
theorem _root_.Alvoki.Storage.DiskTable.withOpenAdmission_flatRefused {state handle result : Type}
    {input : FilePath} {directory : DiskDirectory} {before : state}
    (realPath : FilePath → EStateM IO.Error state FilePath)
    (lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (openAppend : FilePath → EStateM IO.Error state handle)
    (acquire : DiskDirectory → handle → EStateM IO.Error state result)
    (resolved : realPath input before = .ok directory.path before)
    {metadata : IO.FS.Metadata} (present : lookup (directory.file .wal) before = .ok (.ok metadata) before) :
    DiskTable.withOpenAdmission input realPath lookup openAppend acquire before =
      .error (IO.userError s!"unsupported flat WAL binding: '{directory.file .wal}'") before := by
  simp [DiskTable.withOpenAdmission, DiskDirectory.openWith_reported realPath directory resolved,
    rejectFlatWalWith, optionalMetadataWith, present, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- An existing non-private lock is rejected before its append-open. -/
theorem _root_.Alvoki.Storage.DiskTable.withOpenAdmission_lockRefused {state handle result : Type}
    {input : FilePath} {directory : DiskDirectory} {before : state}
    (realPath : FilePath → EStateM IO.Error state FilePath)
    (lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (openAppend : FilePath → EStateM IO.Error state handle)
    (acquire : DiskDirectory → handle → EStateM IO.Error state result)
    (resolved : realPath input before = .ok directory.path before)
    (flat : optionalMetadataWith (lookup (directory.file .wal)) before = .ok none before)
    {metadata : IO.FS.Metadata} (present : lookup (directory.file .lock) before = .ok (.ok metadata) before)
    (invalid : (metadata.type == .file && metadata.numLinks == 1) = false) :
    DiskTable.withOpenAdmission input realPath lookup openAppend acquire before =
      .error (IO.userError s!"expected a regular database file with one link: '{directory.file .lock}'") before := by
  have probed : optionalMetadataWith (lookup (directory.file .lock)) before = .ok (some metadata) before := by
    simp [optionalMetadataWith, Bind.bind, EStateM.bind, present, Pure.pure, EStateM.pure]
  have rejected :
      checkPrivateRegularWith (m := EStateM IO.Error state) (directory.file .lock) metadata before =
        .error (IO.userError s!"expected a regular database file with one link: '{directory.file .lock}'") before := by
    unfold checkPrivateRegularWith
    rw [invalid]
    rfl
  simp only [DiskTable.withOpenAdmission, DiskDirectory.openWith_reported realPath directory resolved,
    rejectFlatWalWith, Bind.bind, EStateM.bind, flat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Pure.pure, EStateM.pure, probed, rejected]

/-- A reported append-open error returns its reached state before flock.
Creating the lock name or obtaining a raw descriptor can precede the
failed runtime handle allocation, so the result retains those effects. -/
theorem _root_.Alvoki.Storage.DiskTable.withOpenAdmission_lockOpenError {state handle result : Type}
    {input : FilePath} {directory : DiskDirectory} {before reached : state}
    (realPath : FilePath → EStateM IO.Error state FilePath)
    (lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (openAppend : FilePath → EStateM IO.Error state handle)
    (acquire : DiskDirectory → handle → EStateM IO.Error state result)
    (resolved : realPath input before = .ok directory.path before)
    (flat : optionalMetadataWith (lookup (directory.file .wal)) before = .ok none before)
    {lock : Option IO.FS.Metadata}
    (probed : optionalMetadataWith (lookup (directory.file .lock)) before = .ok lock before)
    (safe : ∀ metadata, lock = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true)
    {cause : IO.Error} (failed : openAppend (directory.file .lock) before = .error cause reached) :
    DiskTable.withOpenAdmission input realPath lookup openAppend acquire before = .error cause reached := by
  have checked := DiskDirectory.openWith_reported realPath directory resolved
  cases lock with
  | none =>
    simp [DiskTable.withOpenAdmission, checked, rejectFlatWalWith, flat, probed, failed, Bind.bind,
      EStateM.bind, Pure.pure, EStateM.pure]
  | some metadata =>
    have regular := safe metadata rfl
    simp [DiskTable.withOpenAdmission, checked, rejectFlatWalWith, flat, probed, checkPrivateRegularWith,
      regular, failed, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

def MarkedRetryChunkReports.runWithAdmission {files : Type} {input : FilePath}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    (admission : OpenAdmissionReports input directory observed.slot) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
    (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path))
    observed.runAt before

theorem MarkedRetryChunkReports.runWithAdmission_eq {files : Type} {input : FilePath}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    (admission : OpenAdmissionReports input directory observed.slot) :
    observed.runWithAdmission admission = observed.run :=
  admission.admits observed.runAt before

/-- The exact admitted result uses the allocation reported by that same
open. Its token is distinct from every older reference in the census. -/
theorem MarkedRetryChunkReports.admittedSessionRefs {files : Type} {input : FilePath}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    (admission : OpenAdmissionReports input directory observed.slot)
    {session : SegmentedSession} {final : LockedFileState FileImage}
    (opened : observed.runWithAdmission admission = .ok session final) :
    session.phaseRef = observed.nextRef ∧ session.sessionRef = observed.nextRef + 1 ∧
      session.phaseRef ∉ observed.liveRefs ∧ session.sessionRef ∉ observed.liveRefs := by
  rw [observed.runWithAdmission_eq admission, MarkedRetryChunkReports.run, MarkedRetryChunkReports.runAt,
    runOpenWithInstallation_outcome] at opened
  cases reached : runOpenWithImage directory observed.slot.description (observed.flock observed.slot)
      observed.unlock (observed.recoverAt directory) before with
  | error cause after => rw [reached] at opened; contradiction
  | ok table after =>
    rw [reached] at opened
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj opened
    refine ⟨rfl, rfl, Nat.lt_irrefl _ ∘ observed.fresh _, ?_⟩
    intro current
    change observed.nextRef + 1 ∈ observed.liveRefs at current
    have earlier := observed.fresh _ current
    omega

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
      published observed.liveRefs (observed.runWithAdmission admission) := by
  rw [observed.runWithAdmission_eq admission]
  exact runOpenWithInstallation_markedRetryFromChunks observed keeperValid laterValid following accepted ordered

end Alvoki.Storage.DiskSession
