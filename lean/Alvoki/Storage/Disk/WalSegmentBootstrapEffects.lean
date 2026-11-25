import Alvoki.Storage.Disk.WalSegmentBootstrapIO
import Alvoki.Storage.Disk.WalSegmentRotation

namespace Alvoki.Storage.WalSegmentRepair

open System WalSegmentRotation

private def EmptyBindings (pair : DirectoryPublication.Bindings) : Prop :=
  pair.manifest = none ∧ (pair.walBoundary = none ∨ pair.walBoundary = some (WAL.Boundary.encode 0))

/-- A selectable zero marker always has the durable empty segment it names.
Without a marker, an unfinished segment creation may survive or disappear. -/
structure BootstrapValid (state : State) : Prop where
  metadata : state.metadata.Valid EmptyBindings
  marked : ∀ pair ∈ state.metadata.crashImages, pair.walBoundary ≠ none → state.successor = .durable

structure BootstrapReady (state : State) : Prop where
  zeroDurable : state.successor = .durable
  manifestAbsent : state.metadata.active.manifest = none
  zeroMarker : state.metadata.active.walBoundary = some (WAL.Boundary.encode 0)
  settled : state.metadata.crashImages = [state.metadata.active]

theorem bootstrap_fresh : BootstrapValid ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩ := by
  refine ⟨DirectoryPublication.Image.settled_valid ⟨rfl, Or.inl rfl⟩, ?_⟩
  intro pair chosen marked
  cases List.mem_singleton.mp chosen
  exact False.elim (marked rfl)

/-- Classify each admitted power-loss image for a subsequent open. A
surviving empty binding is durable in the new image. -/
theorem BootstrapValid.crash {before : State} (valid : BootstrapValid before)
    {pair : DirectoryPublication.Bindings} (chosen : pair ∈ before.metadata.crashImages)
    {survives : Bool} (allowed : before.successor.MaySurvive survives) :
    BootstrapValid ⟨.settled pair, if survives then .durable else .absent⟩ := by
  refine ⟨DirectoryPublication.Image.settled_valid (valid.metadata.crashValid pair chosen), ?_⟩
  intro selected reported marked
  have same : selected = pair := List.mem_singleton.mp reported
  subst selected
  have durable := valid.marked pair chosen marked
  rw [durable] at allowed
  have present : survives = true := allowed
  simp [present]

private theorem BootstrapValid.rotate {before after : State} {action : WalSegmentRotation.Step}
    (valid : BootstrapValid before) (effect : before.step action = some after) : BootstrapValid after := by
  cases before with
  | mk metadata binding =>
    cases action <;> cases binding <;> simp [State.step] at effect <;> subst after
    all_goals first
      | exact valid
      | exact ⟨valid.metadata.syncDirectory, fun _ _ _ => rfl⟩
      | refine ⟨valid.metadata, ?_⟩
        intro pair chosen marked
        have impossible := valid.marked pair chosen marked
        contradiction

private theorem BootstrapValid.rotatePrefix {before after : State} {actions : List WalSegmentRotation.Step}
    (valid : BootstrapValid before) (ran : before.execute actions = some after) : BootstrapValid after := by
  induction actions generalizing before with
  | nil => cases ran; exact valid
  | cons action rest ih =>
    change (before.step action >>= fun next => next.execute rest) = some after at ran
    cases applied : before.step action with
    | none => simp [applied] at ran
    | some next => exact ih (valid.rotate applied) (by simpa [applied] using ran)

def bootstrapMarkerStep (state : State) (action : Publication.Step) : Option State :=
  if action = .renameStaged ∧ state.metadata.staged .walBoundary ≠ some (WAL.Boundary.encode 0, true) then
    none
  else
    (state.metadata.step .walBoundary (WAL.Boundary.encode 0) action).map fun metadata =>
      { state with metadata }

private theorem markerStep_valid {before after : State} {action : Publication.Step}
    (valid : BootstrapValid before) (durable : before.successor = .durable)
    (applied : bootstrapMarkerStep before action = some after) :
    BootstrapValid after ∧ after.successor = .durable := by
  unfold bootstrapMarkerStep at applied
  split at applied
  · contradiction
  next allowed =>
    have stage : action = .renameStaged → before.metadata.staged .walBoundary = some (WAL.Boundary.encode 0, true) :=
      fun rename => Classical.byContradiction fun wrong => allowed ⟨rename, wrong⟩
    obtain ⟨metadata, effect, rfl⟩ := Option.map_eq_some_iff.mp applied
    refine ⟨⟨DirectoryPublication.Image.step_valid valid.metadata ?_ effect, fun _ _ _ => durable⟩, durable⟩
    intro rename bytes staged pair chosen
    have exactBytes := congrArg Prod.fst (Option.some.inj (staged.symm.trans (stage rename)))
    exact ⟨(valid.metadata.crashValid pair chosen).1, Or.inr (congrArg some exactBytes)⟩

private abbrev BootstrapM := EStateM IO.Error State

/-- Failed marker writes may leave arbitrary scratch bytes, which the next
attempt overwrites. Live metadata and its crash choices change only through
the corresponding admitted replacement effect. -/
def BootstrapMarkerReports (perform : Publication.Step → BootstrapM Unit) : Prop :=
  ∀ action before, before.successor = .durable → match perform action before with
  | .ok _ after => bootstrapMarkerStep before action = some after
  | .error _ after => bootstrapMarkerStep before action = some after ∨
    (after.metadata.active = before.metadata.active ∧
      after.metadata.crashImages = before.metadata.crashImages ∧ after.successor = before.successor ∧
      after.metadata.staged .manifest = before.metadata.staged .manifest ∧
      (action ≠ .writeStaged → after.metadata.staged .walBoundary = before.metadata.staged .walBoundary))

private theorem markerRun (perform : Publication.Step → BootstrapM Unit) (reports : BootstrapMarkerReports perform)
    (actions : List Publication.Step) {before : State} (valid : BootstrapValid before)
    (durable : before.successor = .durable) :
    match (actions.forM perform) before with
    | .ok _ after => actions.foldlM bootstrapMarkerStep before = some after
    | .error _ after => BootstrapValid after := by
  induction actions generalizing before with
  | nil => rfl
  | cons action rest ih =>
    have report := reports action before durable
    change (match EStateM.bind (perform action) (fun _ => rest.forM perform) before with
      | .ok _ after => (action :: rest).foldlM bootstrapMarkerStep before = some after
      | .error _ after => BootstrapValid after)
    unfold EStateM.bind
    cases effect : perform action before with
    | ok _ after =>
      rw [effect] at report
      obtain ⟨kept, durable⟩ := markerStep_valid valid durable report
      have tail := ih kept durable
      cases ran : (rest.forM perform) after <;> simpa [ran, List.foldlM_cons, report] using tail
    | error _ after =>
      rw [effect] at report
      change BootstrapValid after
      rcases report with applied | ⟨active, candidates, zero, _, _⟩
      · exact (markerStep_valid valid durable applied).1
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [active, candidates]
          exact valid.metadata.activeMaySurvive
        · rw [candidates]
          exact valid.metadata.crashValid
        · exact fun _ _ _ => zero.trans durable

private theorem completeMarker {before after : State} (valid : BootstrapValid before)
    (durable : before.successor = .durable)
    (complete : Publication.steps.foldlM bootstrapMarkerStep before = some after) : BootstrapReady after := by
  have absent := valid.metadata.activeValid.1
  cases before with
  | mk metadata successor =>
    change successor = .durable at durable
    subst successor
    change some _ = some after at complete
    obtain rfl := Option.some.inj complete
    exact ⟨rfl, absent, rfl, rfl⟩

private theorem runReachedSteps {action : Type} (effect : State → action → Option State)
    (perform : action → BootstrapM Unit) {steps : List action} {before after : State}
    (complete : steps.foldlM effect before = some after)
    (reports : ∀ done step todo prior next, steps = done ++ step :: todo →
      done.foldlM effect before = some prior → effect prior step = some next →
      perform step prior = .ok () next) :
    (steps.forM perform) before = .ok () after := by
  induction steps generalizing before with
  | nil => cases complete; rfl
  | cons step rest ih =>
    cases applied : effect before step with
    | none => simp [List.foldlM_cons, applied] at complete
    | some next =>
      have head := reports [] step rest before next rfl rfl applied
      have tail : rest.foldlM effect next = some after := by
        simpa [List.foldlM_cons, applied] using complete
      have returned := ih tail (by
        intro done action todo prior final order reached effectAt
        exact reports (step :: done) action todo prior final (congrArg (List.cons step) order)
          (by simpa [List.foldlM_cons, applied] using reached) effectAt)
      change EStateM.bind (perform step) (fun _ => rest.forM perform) before = _
      simp only [EStateM.bind, head, returned]

private theorem bootstrapRotation_completes (directory : DiskDirectory) (before : State)
    (empty : Option ByteArray) (seen : before.observeSuccessor = empty)
    (createEmpty : FilePath → BootstrapM Unit) (sync : Array FilePath → BootstrapM Unit) :
    let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
    let settled : State := ⟨before.metadata.syncDirectory, .durable⟩
    (∀ done step todo prior next, WalSegmentRotation.steps empty.isSome = done ++ step :: todo →
      before.execute done = some prior → prior.step step = some next → rotate step prior = .ok () next) →
    before.execute (WalSegmentRotation.steps empty.isSome) = some settled ∧
    WalSegmentRotation.runAt directory 0 (fun _ => (EStateM.pure empty : BootstrapM _))
      createEmpty (fun path => sync #[path]) before = .ok () settled := by
  intro rotate settled rotation
  have rotates : before.execute (WalSegmentRotation.steps empty.isSome) = some settled := by
    rw [← seen]
    cases before with
    | mk metadata binding => cases binding <;> rfl
  have rotated := runReachedSteps State.step rotate rotates rotation
  have observed : WalSegmentRotation.observeSuccessorWith (EStateM.pure empty : BootstrapM (Option ByteArray)) before =
      .ok empty.isSome before := by
    rw [← seen]
    cases before with
    | mk metadata binding => cases binding <;> rfl
  refine ⟨rotates, ?_⟩
  change EStateM.bind (WalSegmentRotation.observeSuccessorWith (EStateM.pure empty))
    (fun present => WalSegmentRotation.run present rotate) before = _
  simp only [EStateM.bind, observed, WalSegmentRotation.run, rotated]

/-- Successful reached reports give the worker the exact final image of
the ordered marker effects on the settled zero segment. -/
theorem bootstrapEmptyWith_completesAt (directory : DiskDirectory) (before : State)
    (valid : BootstrapValid before) (empty : Option ByteArray) (seen : before.observeSuccessor = empty)
    (createEmpty : FilePath → BootstrapM Unit) (write : FilePath → ByteArray → BootstrapM Unit)
    (sync : Array FilePath → BootstrapM Unit) (renameFile : FilePath → FilePath → BootstrapM Unit) :
    let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
    let publish := Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]
    let settled : State := ⟨before.metadata.syncDirectory, .durable⟩
    (∀ done step todo prior next, WalSegmentRotation.steps empty.isSome = done ++ step :: todo →
      before.execute done = some prior → prior.step step = some next → rotate step prior = .ok () next) →
    (∀ done step todo prior next, Publication.steps = done ++ step :: todo →
      done.foldlM bootstrapMarkerStep settled = some prior → bootstrapMarkerStep prior step = some next →
      publish step prior = .ok () next) →
    ∀ after, Publication.steps.foldlM bootstrapMarkerStep settled = some after →
      bootstrapEmptyWith directory empty createEmpty write sync renameFile before =
      .ok ⟨.empty, 0, 0, 0⟩ after ∧ BootstrapReady after := by
  intro rotate publish settled rotation marker after completed
  obtain ⟨rotates, runRotation⟩ := bootstrapRotation_completes directory before empty seen createEmpty sync rotation
  have published := runReachedSteps bootstrapMarkerStep publish completed marker
  refine ⟨?_, completeMarker (valid.rotatePrefix rotates) rfl completed⟩
  dsimp only [publish, settled] at published
  simp only [bootstrapEmptyWith, Bind.bind, EStateM.bind, Pure.pure, runRotation, Publication.run, published, EStateM.pure]

/-- Once the empty successor is observed, successful primitive reports at
the reached steps complete the native bootstrap worker with a ready image. -/
theorem bootstrapEmptyWith_completes (directory : DiskDirectory) (before : State)
    (valid : BootstrapValid before) (empty : Option ByteArray) (seen : before.observeSuccessor = empty)
    (createEmpty : FilePath → BootstrapM Unit) (write : FilePath → ByteArray → BootstrapM Unit)
    (sync : Array FilePath → BootstrapM Unit) (renameFile : FilePath → FilePath → BootstrapM Unit) :
    let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
    let publish := Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]
    let settled : State := ⟨before.metadata.syncDirectory, .durable⟩
    (∀ done step todo prior next, WalSegmentRotation.steps empty.isSome = done ++ step :: todo →
      before.execute done = some prior → prior.step step = some next → rotate step prior = .ok () next) →
    (∀ done step todo prior next, Publication.steps = done ++ step :: todo →
      done.foldlM bootstrapMarkerStep settled = some prior → bootstrapMarkerStep prior step = some next →
      publish step prior = .ok () next) →
    ∃ after, bootstrapEmptyWith directory empty createEmpty write sync renameFile before =
      .ok ⟨.empty, 0, 0, 0⟩ after ∧ BootstrapReady after := by
  intro _ _ settled rotation marker
  have publishes : ∃ after, Publication.steps.foldlM bootstrapMarkerStep settled = some after := ⟨_, rfl⟩
  obtain ⟨after, completed⟩ := publishes
  exact ⟨after, bootstrapEmptyWith_completesAt directory before valid empty seen createEmpty write sync renameFile
    rotation marker after completed⟩

/-- Once the zero keeper and marker write complete, a returned error
from the staged file sync stops publication before rename and directory sync.
The reported file effect may leave the stage written or fully file-synced. -/
theorem bootstrapEmptyWith_syncStagedError (directory : DiskDirectory) (before : State)
    (valid : BootstrapValid before) (empty : Option ByteArray) (seen : before.observeSuccessor = empty)
    (createEmpty : FilePath → BootstrapM Unit) (write : FilePath → ByteArray → BootstrapM Unit)
    (sync : Array FilePath → BootstrapM Unit) (renameFile : FilePath → FilePath → BootstrapM Unit)
    {written reached : State} {cause : IO.Error} :
    let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
    let settled : State := ⟨before.metadata.syncDirectory, .durable⟩
    (∀ done step todo prior next, WalSegmentRotation.steps empty.isSome = done ++ step :: todo →
      before.execute done = some prior → prior.step step = some next → rotate step prior = .ok () next) →
    bootstrapMarkerStep settled .writeStaged = some written →
    write (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0) settled = .ok () written →
    sync #[directory.file .stagedWalBoundary] written = .error cause reached →
    (reached = written ∨ bootstrapMarkerStep written .syncStaged = some reached) →
    bootstrapEmptyWith directory empty createEmpty write sync renameFile before = .error cause reached ∧
      BootstrapValid reached := by
  intro _ settled rotation writeEffect writeOk failed reachedEffect
  obtain ⟨rotates, runRotation⟩ := bootstrapRotation_completes directory before empty seen createEmpty sync rotation
  obtain ⟨validWritten, durable⟩ := markerStep_valid (valid.rotatePrefix rotates) rfl writeEffect
  have preserves : BootstrapValid reached := by
    rcases reachedEffect with rfl | applied
    · exact validWritten
    · exact (markerStep_valid validWritten durable applied).1
  refine ⟨?_, preserves⟩
  rw [bootstrapEmptyWith]
  have single : (#[].push (directory.file .stagedWalBoundary)) = #[directory.file .stagedWalBoundary] := rfl
  dsimp only [settled] at writeOk
  simp only [Publication.run_performReplacement, Bind.bind, EStateM.bind, Pure.pure,
    runRotation, writeOk, single, failed]

/-- The native markerless schedule runs the segment creation and sync
before starting marker publication. Its reported failures preserve the
bootstrap invariant, including when a failing syscall did take effect. -/
theorem bootstrapEmptyWith_safe (directory : DiskDirectory) (before : State)
    (valid : BootstrapValid before) (empty : Option ByteArray) (seen : before.observeSuccessor = empty)
    (createEmpty : FilePath → BootstrapM Unit) (write : FilePath → ByteArray → BootstrapM Unit)
    (sync : Array FilePath → BootstrapM Unit) (renameFile : FilePath → FilePath → BootstrapM Unit)
    (rotation : EffectReports (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])) :
    match bootstrapEmptyWith directory empty createEmpty write sync renameFile before with
    | .ok reopened after => reopened = ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after
    | .error _ after => BootstrapValid after := by
  let rotate := WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])
  let publish := Publication.performReplacement (write · (WAL.Boundary.encode 0))
    sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]
  have observed : WalSegmentRotation.observeSuccessorWith (pure empty : BootstrapM (Option ByteArray)) before =
      .ok empty.isSome before := by
    rw [← seen]
    cases before with
    | mk metadata binding => cases binding <;> rfl
  have flow := before.runObserved_effects empty.isSome rotate rotation
  change (match (do
    WalSegmentRotation.runAt directory 0 (fun _ => pure empty) createEmpty (fun path => sync #[path])
    Publication.run publish
    pure ⟨.empty, 0, 0, 0⟩ : BootstrapM Reopened) before with
    | .ok reopened after => reopened = ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after
    | .error _ after => BootstrapValid after)
  change WalSegmentRotation.observeSuccessorWith (EStateM.pure empty) before = .ok empty.isSome before at observed
  simp only [WalSegmentRotation.runAt, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, observed]
  cases rotated : WalSegmentRotation.run empty.isSome
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])) before with
  | error _ after =>
    dsimp [rotate] at flow
    rw [rotated] at flow
    obtain ⟨_, cut⟩ := flow
    exact valid.rotatePrefix cut
  | ok _ next =>
    dsimp [rotate] at flow
    rw [rotated] at flow
    have nextValid := valid.rotatePrefix flow
    have executes : before.execute (WalSegmentRotation.steps empty.isSome) =
        some ⟨before.metadata.syncDirectory, .durable⟩ := by
      rw [← seen]
      cases before with
      | mk metadata binding => cases binding <;> rfl
    have durable : next.successor = .durable :=
      congrArg State.successor (Option.some.inj (flow.symm.trans executes))
    have markerOutcome := markerRun publish marker Publication.steps nextValid durable
    change (match Publication.run publish next with
      | .ok _ after => Publication.steps.foldlM bootstrapMarkerStep next = some after
      | .error _ after => BootstrapValid after) at markerOutcome
    cases published : Publication.run publish next with
    | error _ after =>
      rw [published] at markerOutcome
      simpa only [published] using markerOutcome
    | ok _ after =>
      rw [published] at markerOutcome
      simp only [published]
      exact ⟨True.intro, completeMarker nextValid durable markerOutcome⟩

end Alvoki.Storage.WalSegmentRepair
