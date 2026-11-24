import Alvoki.Storage.Disk.CachedMarkedRetryInstallation
import Alvoki.Storage.Disk.AppendCutSession

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

private theorem followingAfterSelection {offsets selected : List Nat} {watermark first : Nat}
    (chosen : selectWalSegmentReads offsets watermark = some (first, selected))
    (ordered : selected.Pairwise (· < ·)) (head : selected.head? = some first) :
    ∀ start ∈ selected.drop 1, watermark < start := by
  unfold selectWalSegmentReads at chosen
  cases maximum : (offsets.filter fun offset => decide (offset ≤ watermark)).max? with
  | none => simp [maximum, Bind.bind, Option.bind] at chosen
  | some greatest =>
    have pair : (greatest, offsets.filter fun offset => decide (greatest ≤ offset)) = (first, selected) := by
      simpa [maximum, Bind.bind, Option.bind, Pure.pure] using chosen
    obtain ⟨rfl, selectedOffsets⟩ := Prod.mk.inj pair
    have upper := (List.max?_eq_some_iff.mp maximum).2
    cases selected with
    | nil => contradiction
    | cons start rest =>
      have exactHead : start = greatest := Option.some.inj head
      subst start
      intro later member
      have greater := (List.pairwise_cons.mp ordered).1 _ member
      have listed := List.mem_filter.mp (selectedOffsets ▸ List.mem_cons_of_mem _ member)
      apply Nat.lt_of_not_ge
      intro within
      exact Nat.not_le_of_gt greater (upper _ (List.mem_filter.mpr ⟨listed.1, decide_eq_true within⟩))

private theorem headOfChain {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history first segments) (nonempty : segments ≠ []) :
    (segments.map WalSegment.first).head? = some first := by
  cases chain with
  | endOfHistory => contradiction
  | cons => rfl

/-- The selected canonical descriptors are ordered, and every descriptor
after the first begins strictly above the loaded checkpoint watermark. -/
theorem MarkedRetryChunkReports.selectedAfterWatermark {files : Type} {directory : DiskDirectory}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    {offsets : List Nat} {selected : List WalSegment}
    (chosen : selectWalSegmentReads offsets layout.range.watermark = some (layout.first, selected.map WalSegment.first))
    (descriptors : layout.sealed ++ [layout.keeper] = selected) :
    ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start := by
  rw [← descriptors] at chosen
  have ordered := (List.pairwise_append.mp (List.pairwise_append.mp observed.reported.ordered).1).2.1
  exact followingAfterSelection chosen ordered (headOfChain layout.chain (by simp))

/-- The cached callback and installation proof supplies the same exact
inputs used to reconstruct a retained writer after a bounded reopen. -/
theorem CachedRetryInstalled.appendCutReady
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {reported : CachedRetryReadReports directory layout}
    {descriptors slot bindings published liveRefs result}
    (installed : CachedRetryInstalled reported descriptors slot bindings published liveRefs result)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ generation, AppendCutReady directory reported.inventory.descriptor liveRefs history published before.image
      layout.target generation result := by
  obtain ⟨opened, checkpoint, model, session, final, returned, path, descriptor, phase, _, _, _, _, held,
    distinct, freshPhase, freshSession, ready, effects, selected, replay, generation, bytes, keeper, committed,
    bounds, refines, represents, pins⟩ := installed
  have exactBytes : opened.walBytes.toNat = (WAL.encode history).size := by
    rw [bytes, WAL.encode_size, Nat.mul_comm]
  have payload : session.phase = .ready ⟨opened.table, opened.generation, (WAL.encode history).size, layout.target.first⟩ := by
    simpa only [Reopened.installed, exactBytes, keeper, CanonicalKeeperLayout.target] using phase
  exact ⟨opened.generation, layout.through, layout.chain.keeperBytes, accepted, ordered, checkpoint, opened.table,
    model, session, final, returned, selected, generation, replay, path, descriptor, payload, ready, effects.keepsSealed,
    descriptor ▸ held, committed, bounds, refines, represents, pins, distinct, freshPhase, freshSession⟩

end Alvoki.Storage.DiskSession
