import Alvoki.Storage.Disk.CheckpointHistory
import Alvoki.Storage.Disk.MarkedSessionTrace

namespace Alvoki.WAL.Boundary
open Storage

/-- The live names and every admitted crash image of the owned, durable
directory lack a manifest, WAL and WAL marker. -/
def ReopenImage.Fresh (image : ReopenImage) : Prop :=
  image.directory.active = ⟨none, none⟩ ∧
    image.directory.crashImages = [image.directory.active] ∧
    image.wal.active = none ∧ image.wal.crashImages = [none]

/-- The locked Linux callbacks report their outcomes. A successful create
exposes an empty WAL, a successful grouped sync settles its bytes and name,
and the marker callbacks obey the ordinary replacement step contract. An
error has no result image here, since it may have applied partial effects. -/
structure FreshOpenReports where
  createWal : Except String Unit
  syncWalDirectory : Except String Unit
  marker : Publication.Step → Except String Unit

private abbrev FreshOpenM := StateT ReopenImage (Except String)

private def observed (result : Except String α) : FreshOpenM α :=
  fun image => result.map (·, image)

private def visibleEmptyWal (image : ReopenImage) : ReopenImage :=
  { image with wal := { image.wal with
      active := some ByteArray.empty
      crashImages := some ByteArray.empty :: image.wal.crashImages } }

private def createEmptyWal (report : Except String Unit) : FreshOpenM Unit :=
  fun image => report.map fun () => ((), visibleEmptyWal image)

private def syncNewWal (report : Except String Unit) : FreshOpenM Unit :=
  fun image => report.map fun () => ((), image.syncDirectory)

private def publishMarker (report : Publication.Step → Except String Unit)
    (bytes : ByteArray) (step : Publication.Step) : FreshOpenM Unit := fun image => do
  report step
  let some directory := image.directory.step .walBoundary bytes step |
    throw "fresh WAL marker replacement was not ready"
  return ((), { image with directory })

/-- Model the empty bootstrap branches of `DiskTable.openLocked`. A missing
WAL with absent metadata triggers creation. The aligned action settles the
file and directory, then an unmarked WAL requires full marker replacement.
A retry that already sees the marker follows the ordinary marked selection. -/
def runFreshMarkedOpen (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) (reports : FreshOpenReports) :
    StateT ReopenImage (Except String) (PackedTable × UInt64 × Nat) := do
  let checkpoint ← observed checkpoint
  withRecoveredOpen checkpoint (observed marker) (observed wal) observed (fun message => observed (.error message))
    (fun _ => createEmptyWal reports.createWal)
    (fun _ => observed (.error "unexpected repair of an empty WAL"))
    (fun _ => syncNewWal reports.syncWalDirectory)
    (fun length => Publication.run (publishMarker reports.marker (encode length.toUInt64)))
    (fun table generation length => pure (table, generation, length))

private theorem emptyReplay : recoverSelected .empty ByteArray.empty = .ok .empty := by
  exact recoverSelected_encoded .empty [] [] trivial rfl

private def afterFreshOpen (before : ReopenImage) : ReopenImage :=
  ⟨{ before.directory with
      active := before.directory.active.replace .walBoundary (encode 0)
      crashImages := [before.directory.active.replace .walBoundary (encode 0)]
      staged := fun entry => if entry = .walBoundary then none else before.directory.staged entry },
    { before.wal with active := some ByteArray.empty, crashImages := [some ByteArray.empty] }⟩

private theorem runFreshMarkedOpen_unmarked
    (before : ReopenImage) (reports : FreshOpenReports) (wal : Option ByteArray)
    (observes : before.wal.active = wal) (empty : wal = none ∨ wal = some ByteArray.empty)
    (created : wal = none → reports.createWal = .ok ()) (synced : reports.syncWalDirectory = .ok ())
    (published : ∀ step, reports.marker step = .ok ()) :
    (runFreshMarkedOpen (.ok none) (.ok none) (.ok wal) reports).run before =
      .ok ((.empty, 0, 0), afterFreshOpen before) := by
  rcases empty with rfl | rfl
  all_goals
    simp [runFreshMarkedOpen, withRecoveredOpen, StateT.run, Bind.bind, StateT.bind, Except.bind,
      Pure.pure, StateT.pure, Except.pure, Except.map, observed, withOpenWal, Option.mapM,
      createEmptyWal, created, recoverLegacy, WAL.repairPrefix, emptyReplay, Publication.finishReopen,
      Publication.runReopen, syncNewWal, synced, published, Publication.run, Publication.steps,
      publishMarker, visibleEmptyWal, ReopenImage.syncDirectory, DirectoryPublication.Image.syncDirectory,
      DirectoryPublication.Image.step, observes]
  all_goals change Except.ok ((PackedTable.empty, (0 : UInt64), (0 : Nat)),
    (⟨{ before.directory with
      active := before.directory.active.replace .walBoundary (encode 0),
      crashImages := [before.directory.active.replace .walBoundary (encode 0)],
      staged := fun entry => if entry = .walBoundary then none else
        if entry = .walBoundary then some (encode 0, true) else
        if entry = .walBoundary then some (encode 0, false) else before.directory.staged entry },
      { before.wal with active := some ByteArray.empty, crashImages := [some ByteArray.empty] }⟩ :
      ReopenImage)) = _
  all_goals
    unfold afterFreshOpen
    congr 4
    funext entry
    cases entry <;> rfl

private theorem runFreshMarkedOpen_marked (before : ReopenImage) (reports : FreshOpenReports)
    (synced : reports.syncWalDirectory = .ok ()) :
    (runFreshMarkedOpen (.ok none) (.ok (some (encode 0))) (.ok (some ByteArray.empty)) reports).run
        before = .ok ((.empty, 0, 0), before.syncDirectory) := by
  have recoverEmpty : recoverMarked .empty 0 ByteArray.empty = .ok (ByteArray.empty, .empty) := by
    have selected : select 0 ByteArray.empty = .ok ByteArray.empty := rfl
    simp [recoverMarked, selected, emptyReplay, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [runFreshMarkedOpen, withRecoveredOpen, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map, Except.map,
    observed, withOpenWal, Option.mapM, decode_encode,
    recoverEmpty, Publication.finishReopen, Publication.runReopen, syncNewWal, synced]

private theorem afterFreshOpen_settled {before : ReopenImage}
    (absent : before.directory.active.manifest = none) : (afterFreshOpen before).SettledFor none [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change before.directory.active.replace .walBoundary (encode 0) = ⟨none, some (encode 0)⟩
  exact congrArg (fun manifest => DirectoryPublication.Bindings.mk manifest (some (encode 0))) absent

private theorem emptyWriterReady (after : ReopenImage) (checkpointImage : CheckpointPublication.Image)
    (settled : after.SettledFor none []) :
    ∃ fixed : FixedMarkedCheckpoint,
      let writer : MarkedWriterState := ⟨.empty, 0, after, []⟩
      writer.ReadyFor fixed.manifest ∧ fixed.manifest = none ∧ fixed.covered = [] ∧
      fixed.image.manifest = after.directory.project .manifest ∧
      writer.table.Refines fixed.model ∧ RepresentsWalHistory writer.history fixed.model ∧
      fixed.image.durable = checkpointImage.durable := by
  let fixed : FixedMarkedCheckpoint := {
    manifest := none
    files := []
    image := { checkpointImage with manifest := after.directory.project .manifest }
    walSequence := 0
    table := .empty
    model := .empty
    covered := []
    written := .absent
    accepted := trivial
    represents := PackedTable.empty_refines
    watermark := rfl
  }
  have fits : 0 < UInt64.size := by decide
  exact ⟨fixed, ⟨settled, trivial, rfl, rfl, fits, PackedTable.empty_rowBounds⟩,
    rfl, rfl, rfl, PackedTable.empty_refines, RepresentsWalHistory.empty, rfl⟩

/-- An empty database can publish only the zero marker, with no manifest. -/
private def EmptyBootstrapBindings (pair : DirectoryPublication.Bindings) : Prop :=
  pair.manifest = none ∧ (pair.walBoundary = none ∨ pair.walBoundary = some (encode 0))

/-- Both the visible and all selectable crash WAL files exist and are empty. -/
def ReopenImage.DurableEmptyWal (image : ReopenImage) : Prop :=
  ∀ wal ∈ image.wal.active :: image.wal.crashImages, wal = some ByteArray.empty

/-- Every possible marker selects an empty WAL whose bytes and binding are
already durable. Before marker publication the empty file may still be absent. -/
structure ReopenImage.EmptyBootstrapValid (image : ReopenImage) : Prop where
  metadata : image.directory.Valid EmptyBootstrapBindings
  walChoices : ∀ wal ∈ image.wal.active :: image.wal.crashImages,
    wal = none ∨ wal = some ByteArray.empty
  markedWal : ∀ pair ∈ image.directory.crashImages, pair.walBoundary ≠ none → image.DurableEmptyWal

private def alignedBootstrapImage (image : ReopenImage) (report : AlignedSyncReport) : ReopenImage :=
  match performAlignedSync false report image with
  | .ok _ after | .error _ after => after

/-- Apply a successful prefix of the shared marker replacement schedule. -/
def runEmptyBootstrapMarkerCut (image : ReopenImage) (cut : Nat) : Except String (Unit × ReopenImage) :=
  ((Publication.steps.take cut).forM (publishMarker (fun _ => .ok ()) (encode 0))).run image

/-- A failed staging write may leave arbitrary scratch contents. A retry
starts a new marker schedule by overwriting that name. -/
private def withBootstrapMarkerScratch (image : ReopenImage)
    (scratch : Option (ByteArray × Bool)) : ReopenImage :=
  { image with directory := { image.directory with
      staged := fun entry => if entry = .walBoundary then scratch else image.directory.staged entry } }

/-- Cuts can leave a successful prefix of the marker schedule visible, even
if the final syscall reported an error. Another attempt starts from that
visible state or from a selectable power-loss image. The marker schedule can
start only after an empty WAL has been synced and its name made durable. -/
inductive EmptyBootstrapAttempts (initial : ReopenImage) : ReopenImage → Prop where
  | start : EmptyBootstrapAttempts initial initial
  | createWal (prior : EmptyBootstrapAttempts initial before)
      (absentManifest : before.directory.active.manifest = none)
      (absentMarker : before.directory.active.walBoundary = none) (absentWal : before.wal.active = none) :
      EmptyBootstrapAttempts initial (visibleEmptyWal before)
  | aligned (prior : EmptyBootstrapAttempts initial before) (wal : before.wal.active = some ByteArray.empty)
      (report : AlignedSyncReport) : EmptyBootstrapAttempts initial (alignedBootstrapImage before report)
  | marker (prior : EmptyBootstrapAttempts initial before)
      (unmarked : before.directory.active.walBoundary = none) (synced : before.DurableEmptyWal) (cut : Nat)
      (executed : runEmptyBootstrapMarkerCut before cut = .ok ((), after)) :
      EmptyBootstrapAttempts initial after
  | interruptedStage (prior : EmptyBootstrapAttempts initial before)
      (unmarked : before.directory.active.walBoundary = none) (synced : before.DurableEmptyWal)
      (scratch : Option (ByteArray × Bool)) : EmptyBootstrapAttempts initial (withBootstrapMarkerScratch before scratch)
  | crash (prior : EmptyBootstrapAttempts initial before) (pairSurvives : pair ∈ before.directory.crashImages)
      (walSurvives : wal ∈ before.wal.crashImages) : EmptyBootstrapAttempts initial (ReopenImage.crash pair wal)

private theorem ReopenImage.Fresh.emptyBootstrapValid {image : ReopenImage} (fresh : image.Fresh) :
    image.EmptyBootstrapValid := by
  obtain ⟨active, crashes, wal, walCrashes⟩ := fresh
  refine ⟨⟨by rw [crashes]; simp, ?_⟩, ?_, ?_⟩
  · intro pair chosen
    rw [crashes, active] at chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact ⟨rfl, Or.inl rfl⟩
  · intro contents chosen
    rw [wal, walCrashes] at chosen
    exact Or.inl (by simpa using chosen)
  · intro pair chosen marked
    rw [crashes, active] at chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact False.elim (marked rfl)

private theorem ReopenImage.EmptyBootstrapValid.create {image : ReopenImage}
    (valid : image.EmptyBootstrapValid) (absent : image.wal.active = none) :
    (visibleEmptyWal image).EmptyBootstrapValid := by
  refine ⟨valid.metadata, ?_, ?_⟩
  · intro wal chosen
    rcases List.mem_cons.mp chosen with rfl | remaining
    · exact Or.inr rfl
    · rcases List.mem_cons.mp remaining with rfl | previous
      · exact Or.inr rfl
      · exact valid.walChoices wal (List.mem_cons_of_mem _ previous)
  · intro pair chosen marked
    have present := valid.markedWal pair chosen marked _ (List.mem_cons_self ..)
    rw [absent] at present
    contradiction

private theorem ReopenImage.EmptyBootstrapValid.sync {image : ReopenImage}
    (valid : image.EmptyBootstrapValid) (wal : image.wal.active = some ByteArray.empty) :
    image.syncDirectory.EmptyBootstrapValid := by
  have durable : image.syncDirectory.DurableEmptyWal := by
    intro contents chosen
    change contents ∈ [image.wal.active, image.wal.active] at chosen
    simpa [wal] using chosen
  exact ⟨valid.metadata.syncDirectory, fun contents chosen => Or.inr (durable contents chosen),
    fun _ _ _ => durable⟩

private theorem ReopenImage.EmptyBootstrapValid.metadataSync {image : ReopenImage}
    (valid : image.EmptyBootstrapValid) : image.syncMetadata.EmptyBootstrapValid := by
  refine ⟨valid.metadata.syncDirectory, valid.walChoices, ?_⟩
  intro pair chosen marked
  obtain rfl := List.mem_singleton.mp chosen
  exact valid.markedWal _ valid.metadata.activeMaySurvive marked

private theorem ReopenImage.EmptyBootstrapValid.allowWal {image : ReopenImage}
    (valid : image.EmptyBootstrapValid) : image.allowVisibleWal.EmptyBootstrapValid := by
  have previous (wal : Option ByteArray) (chosen : wal ∈ image.allowVisibleWal.wal.active ::
      image.allowVisibleWal.wal.crashImages) : wal ∈ image.wal.active :: image.wal.crashImages := by
    rcases List.mem_cons.mp chosen with rfl | compatible
    · exact List.mem_cons_self
    · exact compatible
  exact ⟨valid.metadata, fun wal chosen => valid.walChoices wal (previous wal chosen),
    fun pair chosen marked wal selected => valid.markedWal pair chosen marked wal (previous wal selected)⟩

private theorem markerBootstrapCut_valid {before after : ReopenImage} {cut : Nat}
    (valid : before.directory.Valid EmptyBootstrapBindings)
    (executed : runEmptyBootstrapMarkerCut before cut = .ok ((), after)) :
    after.directory.Valid EmptyBootstrapBindings ∧ after.wal = before.wal := by
  have replacement (pair : DirectoryPublication.Bindings) (accepted : EmptyBootstrapBindings pair) :
      EmptyBootstrapBindings (pair.replace .walBoundary (encode 0)) := ⟨accepted.1, Or.inr rfl⟩
  rcases cut with _ | _ | _ | _ | cut
  · cases executed
    exact ⟨valid, rfl⟩
  · cases executed
    exact ⟨⟨valid.activeMaySurvive, valid.crashValid⟩, rfl⟩
  · cases executed
    exact ⟨⟨valid.activeMaySurvive, valid.crashValid⟩, rfl⟩
  · cases executed
    refine ⟨⟨List.mem_append_left _ (List.mem_map_of_mem valid.activeMaySurvive), ?_⟩, rfl⟩
    intro pair chosen
    rcases List.mem_append.mp chosen with new | old
    · obtain ⟨earlier, survived, rfl⟩ := List.mem_map.mp new
      exact replacement _ (valid.crashValid _ survived)
    · exact valid.crashValid _ old
  · simp only [runEmptyBootstrapMarkerCut, Publication.steps, List.take_succ_cons, List.take_nil] at executed
    cases executed
    refine ⟨⟨List.mem_cons_self, ?_⟩, rfl⟩
    intro pair chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact replacement _ valid.activeValid

/-- Creating or syncing the empty WAL, cutting marker replacement, and
retrying after any admitted crash all preserve the bootstrap invariant. -/
theorem EmptyBootstrapAttempts.valid {initial after : ReopenImage} (fresh : initial.Fresh)
    (attempts : EmptyBootstrapAttempts initial after) : after.EmptyBootstrapValid := by
  induction attempts with
  | start => exact fresh.emptyBootstrapValid
  | createWal _ _ _ absent valid => exact valid.create absent
  | aligned _ wal report valid =>
    cases report with
    | success => exact valid.sync wal
    | failure message walSynced directorySynced =>
      cases walSynced <;> cases directorySynced
      · exact valid
      · exact valid.metadataSync.allowWal
      · exact valid.allowWal
      · exact valid.sync wal
  | marker _ _ synced _ executed valid =>
    obtain ⟨metadata, sameWal⟩ := markerBootstrapCut_valid valid.metadata executed
    refine ⟨metadata, ?_, fun _ _ _ => ?_⟩
    · rw [sameWal]
      exact valid.walChoices
    · unfold ReopenImage.DurableEmptyWal
      rw [sameWal]
      exact synced
  | interruptedStage _ _ _ _ valid =>
    exact ⟨⟨valid.metadata.activeMaySurvive, valid.metadata.crashValid⟩,
      valid.walChoices, valid.markedWal⟩
  | @crash before pair wal _ pairSurvives walSurvives valid =>
    refine ⟨DirectoryPublication.Image.settled_valid (valid.metadata.crashValid _ pairSurvives), ?_, ?_⟩
    · intro choice selected
      have same : choice = wal := by simpa [ReopenImage.crash, Publication.Image.settled] using selected
      rw [same]
      exact valid.walChoices _ (List.mem_cons_of_mem _ walSurvives)
    · intro candidate chosen marked contents selected
      obtain rfl := List.mem_singleton.mp chosen
      have present := valid.markedWal _ pairSurvives marked _ (List.mem_cons_of_mem _ walSurvives)
      have selectedWal : contents = wal := by simpa [ReopenImage.crash, Publication.Image.settled] using selected
      exact selectedWal.trans present

/-- The three open paths that can observe a cut of empty bootstrap. A
marked open must find the existing empty WAL and does not create one. -/
inductive EmptyBootstrapObservation : DirectoryPublication.Bindings → Option ByteArray → Prop where
  | fresh : EmptyBootstrapObservation ⟨none, none⟩ none
  | unmarked : EmptyBootstrapObservation ⟨none, none⟩ (some ByteArray.empty)
  | marked : EmptyBootstrapObservation ⟨none, some (encode 0)⟩ (some ByteArray.empty)

theorem ReopenImage.EmptyBootstrapValid.observe {image : ReopenImage} (valid : image.EmptyBootstrapValid)
    {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadata : pair ∈ image.directory.active :: image.directory.crashImages)
    (contents : wal ∈ image.wal.active :: image.wal.crashImages) : EmptyBootstrapObservation pair wal := by
  have survives : pair ∈ image.directory.crashImages := (List.mem_cons.mp metadata).elim
    (fun same => same.symm ▸ valid.metadata.activeMaySurvive) id
  have accepted := valid.metadata.crashValid _ survives
  rcases pair with ⟨manifest, marker⟩
  obtain ⟨rfl, absent | published⟩ := accepted
  · change marker = none at absent
    subst marker
    rcases valid.walChoices wal contents with rfl | rfl
    · exact .fresh
    · exact .unmarked
  · change marker = some (encode 0) at published
    subst marker
    have present := valid.markedWal _ survives (by simp) wal contents
    subst wal
    exact .marked

/-- Once the required file operations succeed, any classified empty
bootstrap state opens as the first marked writer. Existing WAL bytes skip
creation, and an existing marker skips publication. The WAL and marker
operations leave the durable run map unchanged. -/
theorem emptyBootstrapOpen_ready {before : ReopenImage} (valid : before.EmptyBootstrapValid)
    {checkpointImage : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations checkpointImage before.directory.active.manifest)
    (walReads : MarkedWalReads before) {observedManifest observedMarker observedWal : Option ByteArray}
    (readManifest : checkpointReads.readManifest = .ok observedManifest)
    (readMarker : walReads.marker = .ok observedMarker) (readWal : walReads.wal = .ok observedWal)
    (reports : FreshOpenReports) (created : observedWal = none → reports.createWal = .ok ())
    (synced : reports.syncWalDirectory = .ok ())
    (published : observedMarker = none → ∀ step, reports.marker step = .ok ()) :
    ∃ (after : ReopenImage) (fixed : FixedMarkedCheckpoint),
      let writer : MarkedWriterState := ⟨.empty, 0, after, []⟩
      (runFreshMarkedOpen checkpointReads.result walReads.marker walReads.wal reports).run before =
          .ok ((writer.table, 0, writer.walBytes), writer.image) ∧
      writer.ReadyFor fixed.manifest ∧ fixed.manifest = none ∧ fixed.covered = [] ∧
      fixed.image.manifest = after.directory.project .manifest ∧
      writer.table.Refines fixed.model ∧ RepresentsWalHistory writer.history fixed.model ∧
      fixed.image.durable = checkpointImage.durable := by
  have absentManifest : before.directory.active.manifest = none := valid.metadata.activeValid.1
  have seenManifest := (checkpointReads.manifestVisible _ readManifest).trans absentManifest
  have seenMarker := walReads.markerVisible _ readMarker
  have seenWal := walReads.walVisible _ readWal
  have load : checkpointReads.result = .ok none := by
    rw [CheckpointFileReads.result, readManifest, seenManifest]
    rfl
  have branch := valid.observe (List.mem_cons_self ..) (List.mem_cons_self ..)
  obtain ⟨after, opened, settled⟩ : ∃ after,
      (runFreshMarkedOpen checkpointReads.result walReads.marker walReads.wal reports).run before =
        .ok ((.empty, 0, 0), after) ∧ after.SettledFor none [] := by
    rw [load, readMarker, ← seenMarker, readWal, ← seenWal]
    generalize active : before.directory.active = pair at branch ⊢
    generalize current : before.wal.active = wal at branch ⊢
    cases branch with
    | fresh =>
      exact ⟨_, runFreshMarkedOpen_unmarked before reports none current (Or.inl rfl)
        (fun _ => created (seenWal.symm.trans current)) synced
        (published (seenMarker.symm.trans (congrArg DirectoryPublication.Bindings.walBoundary active))),
        afterFreshOpen_settled absentManifest⟩
    | unmarked =>
      exact ⟨_, runFreshMarkedOpen_unmarked before reports (some ByteArray.empty) current (Or.inr rfl)
        (fun contradiction => nomatch contradiction) synced
        (published (seenMarker.symm.trans (congrArg DirectoryPublication.Bindings.walBoundary active))),
        afterFreshOpen_settled absentManifest⟩
    | marked =>
      exact ⟨_, runFreshMarkedOpen_marked before reports synced, ⟨active, rfl, current, rfl⟩⟩
  obtain ⟨fixed, ready, noManifest, noCovered, projects, refined, history, durable⟩ :=
    emptyWriterReady after checkpointImage settled
  exact ⟨after, fixed, opened, ready, noManifest, noCovered, projects, refined, history, durable⟩

/-- A fresh directory starts the same marked writer after creating and
syncing the empty WAL and publishing its zero marker. -/
theorem freshMarkedOpen_ready {before : ReopenImage} (fresh : before.Fresh)
    {checkpointImage : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations checkpointImage before.directory.active.manifest)
    (walReads : MarkedWalReads before) {observedManifest observedMarker observedWal : Option ByteArray}
    (readManifest : checkpointReads.readManifest = .ok observedManifest)
    (readMarker : walReads.marker = .ok observedMarker) (readWal : walReads.wal = .ok observedWal)
    (reports : FreshOpenReports)
    (created : reports.createWal = .ok ()) (synced : reports.syncWalDirectory = .ok ())
    (published : ∀ step, reports.marker step = .ok ()) :
    ∃ (after : ReopenImage) (fixed : FixedMarkedCheckpoint),
      let writer : MarkedWriterState := ⟨.empty, 0, after, []⟩
      (runFreshMarkedOpen checkpointReads.result walReads.marker walReads.wal reports).run before =
          .ok ((writer.table, 0, writer.walBytes), writer.image) ∧
      writer.ReadyFor fixed.manifest ∧ fixed.manifest = none ∧ fixed.covered = [] ∧
      fixed.image.manifest = writer.image.directory.project .manifest ∧
      writer.table.Refines fixed.model ∧ RepresentsWalHistory writer.history fixed.model := by
  obtain ⟨after, fixed, opened, ready, noManifest, noCovered, projects, refined, history, _⟩ :=
    emptyBootstrapOpen_ready fresh.emptyBootstrapValid checkpointReads walReads
      readManifest readMarker readWal reports (fun _ => created) synced (fun _ => published)
  exact ⟨after, fixed, opened, ready, noManifest, noCovered, projects, refined, history⟩

end Alvoki.WAL.Boundary
