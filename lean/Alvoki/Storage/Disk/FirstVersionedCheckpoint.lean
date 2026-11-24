import Alvoki.Storage.Disk.MarkedDatabaseTrace
import Alvoki.Storage.Disk.VersionedCheckpointRetry
import Alvoki.Storage.Disk.VersionedCheckpointReopen

namespace Alvoki.Storage.CheckpointPublication
open Manifest

private theorem Image.accepts_legacy_as_versioned {image : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {binding : Option ByteArray}
    (legacy : image.Accepts walSequence expected binding) :
    image.AcceptsVersioned walSequence expected binding := by
  cases binding with
  | none => trivial
  | some bytes =>
    have ⟨_, _, decoded, _⟩ := legacy
    exact (Image.acceptsVersioned_legacy_iff decoded).mpr legacy

theorem Image.validVersioned_of_legacy {image : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} (legacy : image.Valid walSequence expected) :
    image.ValidVersioned walSequence expected :=
  ⟨legacy.hasCrashImage, Image.accepts_legacy_as_versioned legacy.activeValid,
    fun _ survives => Image.accepts_legacy_as_versioned (legacy.crashValid _ survives)⟩

/-- A valid legacy image has only v1 or absent bindings. Its generation
test also excludes every raw binding recognized by the dual-format decoder. -/
theorem Image.unreachableVersioned_of_legacy {image : Image} {walSequence generation : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} (legacy : image.Valid walSequence expected)
    (fresh : image.Unreachable generation) : image.UnreachableVersioned generation := by
  intro bytes selectable selected decoded
  have accepted : image.Accepts walSequence expected (some bytes) := by
    rcases selectable with visible | survives
    · exact visible ▸ legacy.activeValid
    · exact legacy.crashValid _ survives
  obtain ⟨header, _, legacyDecode, _⟩ := accepted
  have same := Except.ok.inj (decoded.symm.trans (VersionedCheckpoint.decode_legacy legacyDecode))
  subst selected
  exact fresh bytes selectable header legacyDecode

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.WAL.Boundary
open Storage CheckpointPublication

theorem CheckpointPreparation.decodeVersionedManifest {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (floor : prepared.runs.header.floor ≤ prepared.runs.header.committed) :
    Manifest.VersionedCheckpoint.decode (VersionedRunSet.integrity prepared.runs).manifest.encode =
      .ok (VersionedRunSet.integrity prepared.runs).manifest := by
  let next := prepared.runs
  let metadata := Manifest.IntegrityCheckpoint.fromRuns next.header next.files
  have metadataCount : metadata.runs.length = metadata.header.runCount.toNat := by
    change ((prepared.table.runs.map (·.run.bytes)).map Manifest.RunIntegrity.ofBytes).length =
      prepared.table.runs.length.toUInt64.toNat
    rw [List.length_map, List.length_map, UInt64.toNat_ofNat_of_lt' prepared.runCountFits]
  exact Manifest.VersionedCheckpoint.decode_integrity
    (Manifest.IntegrityCheckpoint.decode_encode metadata floor metadataCount)

/-- Construct the reported attempt from the prepared writer's real ordered
runs. Freshness is stated against both manifest formats. -/
theorem CheckpointPreparation.versionedAttempt {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) {manifest : Option ByteArray}
    {model : Sequential.SnapshotTable UInt64}
    (ready : state.writer.ReadyFor manifest) (refines : state.writer.table.Refines model)
    (represents : RepresentsWalHistory state.writer.history model)
    (fresh : state.publicationInput.UnreachableVersioned prepared.runs.header.generation)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {report : Step → StepReport} {result : EStateM.Result Unit Image Unit}
    (reported : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) report = some result) :
    match result with
    | .ok _ after | .error _ after => VersionedRetry state.writer.history.length.toUInt64
        (CheckpointRepresentsPrefix state.writer.history) state.publicationInput after := by
  let next := prepared.runs
  obtain ⟨floor, count, covered, witness⟩ := checkpointPublicationWitness ready prepared.flushed refines
    represents prepared.runCountFits next.header.generation
  have decoded := prepared.decodeVersionedManifest floor
  have checked := Manifest.IntegrityCheckpoint.validateRuns_fromRuns next.header next.files count byteLengthsFit
  have retry := VersionedRetry.reported (.refl _) (.integrity next) fresh decoded count.symm checked
    covered witness report reported
  cases result <;> exact retry

/-- A valid v1 writer can start versioned publication with the existing
flush result and successor generation. Both success and a reported error
leave a versioned retry image for the same acknowledged WAL. -/
theorem CheckpointPreparation.versionedReported {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (valid : state.Valid)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {report : Step → StepReport} {result : EStateM.Result Unit Image Unit}
    (reported : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) report = some result) :
    let expected := CheckpointRepresentsPrefix state.writer.history
    state.publicationInput.ValidVersioned state.writer.history.length.toUInt64 expected ∧
      match result with
      | .ok _ after | .error _ after =>
        VersionedRetry state.writer.history.length.toUInt64 expected state.publicationInput after := by
  intro expected
  obtain ⟨fixed, durable, prior⟩ := valid
  obtain ⟨pending, history⟩ := prior.coveredPrefix
  obtain ⟨model, refines, represents⟩ := prior.live
  have sameInput : fixed.publicationInput state.writer = state.publicationInput := by
    change Image.mk _ fixed.image.durable = Image.mk _ state.durable
    rw [durable]
  have legacy : state.publicationInput.Valid state.writer.history.length.toUInt64 expected := by
    rw [← sameInput]
    exact fixed.validPublicationInput prior.ready history prior.covered
  have legacyFresh : state.publicationInput.Unreachable prepared.runs.header.generation :=
    checkpointSuccessorUnreachable prior.ready rfl prior.generationMatches prepared.generationFits
  refine ⟨state.publicationInput.validVersioned_of_legacy legacy, ?_⟩
  have fresh := state.publicationInput.unreachableVersioned_of_legacy legacy legacyFresh
  have attempt := prepared.versionedAttempt prior.ready refines represents fresh byteLengthsFit reported
  cases result <;> exact attempt

/-- Start from the actual v1 writer's preparation and a reported error of
its first v2 publication plan. After admissible crashes and reopen attempts,
successful reads and aligned sync under the canonical lock recover a writer
ready to continue, including when the older manifest or absence survived. -/
theorem CheckpointPreparation.reopenAfterFirstVersionedError {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (valid : state.Valid)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {checkpointReport : Step → StepReport} {published : Image}
    (failed : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) checkpointReport =
      some (.error () published))
    {reopen : ReopenImage} (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) reopen)
    {dir : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners dir (.ok true))
    {reports : OpenPathReadReports}
    (observes : (owners.set (dir.file .lock) (some descriptor)).Owns dir descriptor →
      reports.ObservesVersioned dir reopen published.durable)
    (manifestRead : ∃ value, reports.readOptional (dir.file .manifest) = .ok value)
    (runReads : ∀ bytes selected, reopen.directory.active.manifest = some bytes →
      Manifest.VersionedCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, reports.readBin (dir.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ value, reports.readOptional (dir.file .walBoundary) = .ok value)
    (walRead : ∃ value, reports.readOptional (dir.file .wal) = .ok value)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let acquiredOwners := owners.set (dir.file .lock) (some descriptor)
    let held : acquiredOwners.Owns dir descriptor := by
      simp [DiskSession.LockOwners.Owns, DiskSession.LockOwners.set, acquiredOwners]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let recovered := runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report .success reopen
    ∃ table generation model,
      DiskSession.runLockedMarkedOpen dir descriptor (.ok true) unlock cause recovered owners =
        .ok ((table, generation, (WAL.encode state.writer.history).size), reopen.syncDirectory) acquiredOwners ∧
      acquiredOwners.Owns dir descriptor ∧
      (⟨table, (WAL.encode state.writer.history).size, reopen.syncDirectory, state.writer.history⟩ :
        MarkedWriterState).ReadyFor reopen.directory.active.manifest ∧
      table.Refines model ∧ RepresentsWalHistory state.writer.history model := by
  obtain ⟨accepted, retry⟩ := prepared.versionedReported valid byteLengthsFit failed
  obtain ⟨_, _, prior⟩ := valid
  have fits : (WAL.encode state.writer.history).size < UInt64.size := prior.ready.length ▸ prior.ready.fits
  obtain ⟨_, table, generation, model, _, installed, _, held, ready, _, refined, represents, _⟩ :=
    retry.installs_marked_locked accepted prior.ready.settled rfl fits prior.ready.ordered attempts acquisition
      observes manifestRead runReads markerRead walRead report unlock cause
  exact ⟨table, generation, model, installed, held, ready, refined, represents⟩

end Alvoki.WAL.Boundary
