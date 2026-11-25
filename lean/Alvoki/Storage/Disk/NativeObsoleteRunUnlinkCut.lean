import Alvoki.Storage.Disk.NativeObsoleteRunCollection

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

/-- The checked plan selected the reached unlink. Its completed prefix
and subsequent effect describe the exact visible and crash namespaces.
The drop-only intervals account for the original directory and lock. -/
structure NativeObsoleteRunUnlinkCut (state : NativeReadyState) where
  plan : NativeObsoleteRunPlan state
  done : List RunAddress
  target : RunAddress
  remaining : List RunAddress
  ordered : plan.reports.selected = done ++ target :: remaining
  issue : RunUnlinkImage
  completed : ((done.map RunCollection.Step.unlink).forM plan.reports.perform) plan.initial = .ok () issue
  effective : Bool
  beforeUnlink : List LockReferenceDrop
  afterUnlink : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots, ∀ drop ∈ beforeUnlink ++ afterUnlink,
    drop.removes slot.reference = false
  bindings : DescriptorInventory × RunUnlinkImage → FilePath → Option DeviceInode
  directory : bindings (plan.listing.afterClose.afterDrops beforeUnlink, issue) state.session.directory.path =
    some plan.lifetime.root
  lock : bindings (plan.listing.afterClose.afterDrops beforeUnlink, issue) (state.session.directory.file .lock) =
    some plan.lifetime.lock
  kept : ∀ path ∈ [state.session.directory.path, state.session.directory.file .lock],
    bindings (plan.listing.afterClose.afterDrops (beforeUnlink ++ afterUnlink),
      if effective then issue.applyCollectionStep (.unlink target) else issue) path =
      bindings (plan.listing.afterClose.afterDrops beforeUnlink, issue) path

namespace NativeObsoleteRunUnlinkCut

variable {state : NativeReadyState}

def path (cut : NativeObsoleteRunUnlinkCut state) : FilePath :=
  state.session.directory.file (.run cut.target.1 cut.target.2)

def issueCensus (cut : NativeObsoleteRunUnlinkCut state) : DescriptorInventory :=
  cut.plan.listing.afterClose.afterDrops cut.beforeUnlink

def reachedCensus (cut : NativeObsoleteRunUnlinkCut state) : DescriptorInventory :=
  cut.plan.listing.afterClose.afterDrops (cut.beforeUnlink ++ cut.afterUnlink)

def reached (cut : NativeObsoleteRunUnlinkCut state) : RunUnlinkImage :=
  if cut.effective then cut.issue.applyCollectionStep (.unlink cut.target) else cut.issue

theorem census (cut : NativeObsoleteRunUnlinkCut state) :
    cut.issueCensus = state.census ∧ cut.reachedCensus = state.census := by
  exact ⟨cut.plan.keepsCensus cut.beforeUnlink (fun slot live drop occurred =>
    cut.keepsSlots slot live drop (List.mem_append_left _ occurred)),
    cut.plan.keepsCensus _ cut.keepsSlots⟩

theorem custody (cut : NativeObsoleteRunUnlinkCut state) (valid : state.Valid) :
    state.owner ∈ cut.issueCensus.slots ∧ state.directorySlot ∈ cut.issueCensus.slots ∧
    state.owner ∈ cut.reachedCensus.slots ∧ state.directorySlot ∈ cut.reachedCensus.slots ∧
    cut.plan.lifetime.namespaceView.modelObject cut.plan.lifetime.lock = cut.issueCensus.inode state.owner.description ∧
    cut.plan.lifetime.namespaceView.modelObject cut.plan.lifetime.root = cut.issueCensus.inode state.directorySlot.description ∧
    cut.bindings (cut.issueCensus, cut.issue) state.session.directory.path = some cut.plan.lifetime.root ∧
    cut.bindings (cut.issueCensus, cut.issue) (state.session.directory.file .lock) = some cut.plan.lifetime.lock ∧
    cut.bindings (cut.reachedCensus, cut.reached) state.session.directory.path = some cut.plan.lifetime.root ∧
    cut.bindings (cut.reachedCensus, cut.reached) (state.session.directory.file .lock) = some cut.plan.lifetime.lock := by
  obtain ⟨issue, after⟩ := cut.census
  refine ⟨issue.symm ▸ valid.ownerLive, issue.symm ▸ valid.directoryLive,
    after.symm ▸ valid.ownerLive, after.symm ▸ valid.directoryLive, issue.symm ▸ cut.plan.lifetime.identifiesLock,
    ?_, cut.directory, cut.lock, (cut.kept _ (by simp)).trans cut.directory, (cut.kept _ (by simp)).trans cut.lock⟩
  rw [issue, ← cut.plan.cachedSlot]
  exact cut.plan.lifetime.identifiesDirectory

theorem selected (cut : NativeObsoleteRunUnlinkCut state) (valid : state.Valid) :
    renderRunFileName cut.target.1 cut.target.2 ∈ cut.plan.lifetime.namespaceView.names cut.plan.lifetime.root ∧
    cut.target.1 < state.writer.installed.generation ∧ cut.target.1 ∉ cut.plan.reports.held ∧
    cut.plan.reports.inventory.kindAt cut.path = .ok .file := by
  have member : cut.target ∈ cut.plan.reports.selected := by
    rw [cut.ordered]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨listed, older, unheld, regular⟩ := (cut.plan.reports.selected_eligible valid.retained).mp member
  exact ⟨cut.plan.checkedNames.mem_iff.mp listed, older, unheld, regular⟩

theorem issuedImage (cut : NativeObsoleteRunUnlinkCut state) :
    cut.issue = (cut.done.map RunCollection.Step.unlink).foldl RunUnlinkImage.applyCollectionStep cut.plan.initial := by
  have reached := runCollectionSteps_outcome (cut.done.map RunCollection.Step.unlink)
    cut.plan.initial cut.plan.reports.perform cut.plan.reports.effects
  rw [cut.completed] at reached
  exact reached

private theorem included (cut : NativeObsoleteRunUnlinkCut state) :
    ∀ address ∈ cut.done, address ∈ cut.plan.reports.selected := by
  intro address present
  rw [cut.ordered]
  exact List.mem_append_left _ present

theorem lineage (cut : NativeObsoleteRunUnlinkCut state) :
    RunUnlinkRetry cut.plan.reports.selected cut.plan.initial cut.reached := by
  have prior := (RunUnlinkRetry.start cut.plan.initial).interruptedSchedule cut.done cut.included cut.done.length
  have onlyUnlinks :
      (RunCollection.steps cut.done).take cut.done.length = cut.done.map RunCollection.Step.unlink := by
    simp [RunCollection.steps]
  rw [onlyUnlinks, ← cut.issuedImage] at prior
  by_cases effected : cut.effective = true
  · have current : cut.target ∈ cut.plan.reports.selected := by
      rw [cut.ordered]
      exact List.mem_append_right _ List.mem_cons_self
    unfold reached
    rw [effected]
    change RunUnlinkRetry cut.plan.reports.selected cut.plan.initial
      (if cut.issue.visible cut.target.1 cut.target.2 = none then cut.issue else cut.issue.unlink cut.target)
    split
    · exact prior
    · exact .unlink prior current
  · simpa only [reached, Bool.eq_false_iff.mpr effected, Bool.false_eq_true, ↓reduceIte] using prior

/-- No directory barrier was issued. The original crash alternatives
remain possible. Every completed unlink has removed its visible name,
and the currently issued name is removed when its effect occurred. -/
theorem namespaceAtCut (cut : NativeObsoleteRunUnlinkCut state) :
    (∀ address ∈ cut.done, cut.reached.visible address.1 address.2 = none) ∧
    (cut.effective = true → cut.reached.visible cut.target.1 cut.target.2 = none) ∧
    (cut.effective = false → cut.reached = cut.issue) ∧
    ∀ candidate ∈ cut.plan.initial.crashImages, candidate ∈ cut.reached.crashImages := by
  have prior := (runUnlinkSchedule_reachesBarrier cut.done cut.plan.reports.perform
    cut.plan.reports.effects cut.completed).2
  have visible (address : RunAddress) (chosen : address ∈ cut.done) :
      cut.issue.visible address.1 address.2 = none := by
    change cut.issue.syncDirectory.visible address.1 address.2 = none
    rw [prior]
    exact (cut.plan.initial.finishPass_absent chosen).1
  have atIssue (candidate : RunFiles) (present : candidate ∈ cut.plan.initial.crashImages) :
      candidate ∈ cut.issue.crashImages := cut.issuedImage ▸ cut.plan.initial.crashChoices_afterUnlinks cut.done present
  constructor
  · intro address chosen
    have gone := visible address chosen
    unfold reached
    split
    · change (if cut.issue.visible cut.target.1 cut.target.2 = none then cut.issue else cut.issue.unlink cut.target).visible
        address.1 address.2 = none
      split
      · exact gone
      · simp [RunUnlinkImage.unlink, RunFiles.eraseName, gone]
    · exact gone
  constructor
  · intro effected
    simp only [reached, effected, ↓reduceIte, RunUnlinkImage.applyCollectionStep]
    split
    · assumption
    · simp [RunUnlinkImage.unlink, RunFiles.eraseName]
  refine ⟨fun stopped => by simp [reached, stopped], ?_⟩
  intro candidate present
  have earlier := atIssue candidate present
  unfold reached
  split
  · change candidate ∈ (if cut.issue.visible cut.target.1 cut.target.2 = none then cut.issue else cut.issue.unlink cut.target).crashImages
    split
    · exact earlier
    · exact RunUnlinkImage.unlink_crashImages.mpr (.inl earlier)
  · exact earlier

def next (cut : NativeObsoleteRunUnlinkCut state) : NativeReadyState :=
  { state with
    writer := state.writer.afterRunCollection cut.reached.guaranteed
    census := cut.reachedCensus }

theorem preservesReady (cut : NativeObsoleteRunUnlinkCut state) (valid : state.Valid) :
    cut.next.Valid ∧
    (∀ candidate ∈ cut.reached.crashImages,
      SelectedIntegrityCheckpoint candidate state.writer.target.pair.manifest state.writer.checkpoint) ∧
    ∀ generation index bytes, state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
      cut.plan.initial.guaranteed generation index = some bytes → cut.reached.guaranteed generation index = some bytes := by
  have older (address : RunAddress) (chosen : address ∈ cut.plan.reports.selected) :
      address.1 < state.writer.installed.generation := ((cut.plan.reports.selected_eligible valid.retained).mp chosen).2.1
  obtain ⟨ready, survivor⟩ := valid.retained.afterRunCollection cut.lineage older cut.plan.reports.known
  refine ⟨{ valid with ownerLive := by simpa only [next, cut.census.2] using valid.ownerLive,
                       directoryLive := by simpa only [next, cut.census.2] using valid.directoryLive,
                       retained := ready }, survivor, ?_⟩
  intro generation index bytes retained present
  apply cut.lineage.keepsKnown (name := (generation, index)) present
  intro chosen
  have eligible := (cut.plan.reports.selected_eligible valid.retained).mp chosen
  exact retained.elim (fun le => UInt64.not_lt.mpr le eligible.2.1) eligible.2.2.1

end NativeObsoleteRunUnlinkCut

/-- The actual unlink returns an error at the reached canonical path.
A returned Linux ENOENT is handled inside the selector's native
unlink schedule and is therefore not a returned collector error. -/
structure NativeObsoleteRunUnlinkError {state : NativeReadyState} (cut : NativeObsoleteRunUnlinkCut state) where
  cause : IO.Error
  remove : FilePath → EStateM IO.Error (DescriptorInventory × RunUnlinkImage) (Except IO.Error Unit)
  returned : remove cut.path (cut.issueCensus, cut.issue) =
    .ok (.error cause) (cut.reachedCensus, cut.reached)
  projected : cut.plan.reports.removeFile cut.path cut.issue =
    match remove cut.path (cut.issueCensus, cut.issue) with
    | .ok value (_, after) => .ok value after
    | .error error (_, after) => .error error after
  reported : RunCollection.ownedUnlinkResult (.error cause) = .error cause

theorem NativeObsoleteRunUnlinkError.returns {state : NativeReadyState} {cut : NativeObsoleteRunUnlinkCut state}
    (error : NativeObsoleteRunUnlinkError cut) (valid : state.Valid) :
    cut.plan.run = .error error.cause (state.session.phase,
      ⟨(state.cache, cut.reached), state.files.owners⟩) := by
  have raw : cut.plan.reports.removeFile
      (state.session.directory.file (.run cut.target.1 cut.target.2)) cut.issue = .ok (.error error.cause) cut.reached := by
    change cut.plan.reports.removeFile cut.path cut.issue = _
    rw [error.projected, error.returned]
  have dispatched : cut.plan.reports.perform (.unlink cut.target) cut.issue = .error error.cause cut.reached := by
    change (RunCollection.performPaths cut.plan.reports.removeFile cut.plan.reports.syncDirectory throw
      (fun address => state.session.directory.file (.run address.1 address.2)) state.session.directory.path
      (.unlink cut.target)) cut.issue = _
    simp [RunCollection.performPaths, Bind.bind, EStateM.bind, raw, error.reported, throw,
      throwThe, MonadExceptOf.throw, EStateM.throw]
  have stopped : RunCollection.run cut.plan.reports.selected cut.plan.reports.perform cut.plan.initial =
      .error error.cause cut.reached := by
    rw [cut.ordered, runUnlinkSchedule_reachesUnlink _ _ _ _ cut.completed]
    simp only [Bind.bind, EStateM.bind, dispatched]
  simp only [NativeObsoleteRunPlan.run, cut.plan.plans valid, stopped]

/-- A rejected unlink returns ready. Its exact reached namespace
and selected checkpoint supply the next native position even if
the collector has only completed a prefix of its deletions. -/
structure NativeObsoleteRunUnlinkErrorStep (current : NativeReadPosition history log)
    (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut)
    (next : NativeReadPosition history log) : Prop where
  state : next.state = cut.next
  returned : cut.plan.run = .error error.cause
    (next.state.session.phase, ⟨(next.state.cache, cut.reached), next.state.files.owners⟩)
  session : next.state.session = current.state.session
  installed : next.state.writer.installed = current.state.writer.installed
  files : next.state.files = current.state.files
  cache : next.state.cache = current.state.cache
  census : next.state.census = cut.reachedCensus
  held : next.state.files.owners.Owns next.state.session.directory next.state.session.descriptor
  reads : next.reads = current.reads
  retainedNames : ∀ generation index bytes,
    current.state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
    cut.plan.initial.guaranteed generation index = some bytes → cut.reached.guaranteed generation index = some bytes
  survivors : ∀ candidate ∈ cut.reached.crashImages,
    SelectedIntegrityCheckpoint candidate current.state.writer.target.pair.manifest current.state.writer.checkpoint
  replay : InstalledClientReplay log next.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.reachesObsoleteRunUnlinkError (current : NativeReadPosition history log)
    (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut) :
    ∃ next, NativeObsoleteRunUnlinkErrorStep current cut error next := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨ready, survivors, kept⟩ := cut.preservesReady valid
  let state := cut.next
  let next : NativeReadPosition history log := ⟨.ok state.session (state.census, state.files), state, state, current.reads,
    .installed rfl ready sameHistory pending current.readPrefix.readsBounded⟩
  exact ⟨next, rfl, error.returns valid, rfl, rfl, rfl, rfl, rfl, ready.retained.held, rfl, kept, survivors,
    next.readPrefix.guardedReplay⟩

private abbrev StoppableRunUnlink := ExceptT IO.Error (EStateM FilePath (DescriptorInventory × RunUnlinkImage))

/-- The reported stop is an outer interruption inside the selected raw
unlink callback. Completed unlinks use the same dispatch and issue
inventory before the interrupted callback. -/
structure NativeObsoleteRunUnlinkStop {state : NativeReadyState} (cut : NativeObsoleteRunUnlinkCut state) where
  remove : FilePath → StoppableRunUnlink (Except IO.Error Unit)
  completed : (((cut.done.map RunCollection.Step.unlink).forM
    (RunCollection.performPaths remove (fun _ => pure ()) throw
      (fun address => state.session.directory.file (.run address.1 address.2)) state.session.directory.path))).run
      (cut.plan.listing.afterClose, cut.plan.initial) = .ok (.ok ()) (cut.issueCensus, cut.issue)
  stopped : (remove cut.path).run (cut.issueCensus, cut.issue) = .error cut.path (cut.reachedCensus, cut.reached)

namespace NativeObsoleteRunUnlinkStop

variable {state : NativeReadyState} {cut : NativeObsoleteRunUnlinkCut state}

def run (stop : NativeObsoleteRunUnlinkStop cut) (barrier : FilePath → StoppableRunUnlink Unit) :
    EStateM.Result FilePath (DescriptorInventory × RunUnlinkImage) (Except IO.Error Unit) :=
  (do
    let selected ← (ExceptT.mk (fun before => .ok cut.plan.plan before) : StoppableRunUnlink (List RunAddress))
    RunCollection.run selected (RunCollection.performPaths stop.remove barrier throw
      (fun address => state.session.directory.file (.run address.1 address.2)) state.session.directory.path)).run
    (cut.plan.listing.afterClose, cut.plan.initial)

theorem stops (stop : NativeObsoleteRunUnlinkStop cut) (valid : state.Valid)
    (barrier : FilePath → StoppableRunUnlink Unit) :
    stop.run barrier = .error cut.path (cut.reachedCensus, cut.reached) := by
  let perform : RunCollection.Step RunAddress → StoppableRunUnlink Unit :=
    RunCollection.performPaths stop.remove barrier throw
    (fun address => state.session.directory.file (.run address.1 address.2)) state.session.directory.path
  have samePrefix (done : List RunAddress) : ((done.map RunCollection.Step.unlink).forM perform) =
      ((done.map RunCollection.Step.unlink).forM
        (RunCollection.performPaths stop.remove (fun _ => pure ()) throw
          (fun address => state.session.directory.file (.run address.1 address.2)) state.session.directory.path)) := by
    induction done with
    | nil => rfl
    | cons address tail ih =>
      simp only [List.map_cons, List.forM_eq_forM, List.forM_cons] at ih ⊢
      rw [ih]
      rfl
  have completed :
      (((cut.done.map RunCollection.Step.unlink).forM perform)).run (cut.plan.listing.afterClose, cut.plan.initial) =
        .ok (.ok ()) (cut.issueCensus, cut.issue) := by
    rw [samePrefix cut.done]
    exact stop.completed
  have finished : (perform (.unlink cut.target)).run (cut.issueCensus, cut.issue) =
      .error cut.path (cut.reachedCensus, cut.reached) := by
    have raw : (stop.remove (state.session.directory.file (.run cut.target.1 cut.target.2))).run
        (cut.issueCensus, cut.issue) = .error cut.path (cut.reachedCensus, cut.reached) := stop.stopped
    change stop.remove (state.session.directory.file (.run cut.target.1 cut.target.2))
      (cut.issueCensus, cut.issue) = _ at raw
    simp [perform, RunCollection.performPaths, raw, Bind.bind, ExceptT.bind,
      ExceptT.mk, ExceptT.run, EStateM.bind]
  unfold run
  change (do
      let selected ← (ExceptT.mk (fun before => .ok cut.plan.plan before) : StoppableRunUnlink (List RunAddress))
      RunCollection.run selected perform).run _ = _
  rw [cut.plan.plans valid]
  simp only [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind]
  rw [cut.ordered]
  rw [List.forM_eq_forM] at completed
  change (forM (cut.done.map RunCollection.Step.unlink) perform : StoppableRunUnlink Unit)
    (cut.plan.listing.afterClose, cut.plan.initial) = _ at completed
  change perform (.unlink cut.target) (cut.issueCensus, cut.issue) = _ at finished
  simp only [RunCollection.run, RunCollection.steps, List.map_append, List.map_cons, List.append_assoc, List.cons_append,
    List.forM_eq_forM, List.forM_append, List.forM_cons, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
    EStateM.bind, completed, finished]

abbrev ReachedState :=
  Phase Installed × LockedFileState (CensusDirectoryCache × DescriptorInventory × RunUnlinkImage)

/-- The unlink schedule never assigns the phase or changes the cache
or logical lock owner. Keep those exact entry projections alongside
the raw stop's observed run map and descriptor census. -/
def runFromReady (stop : NativeObsoleteRunUnlinkStop cut) (barrier : FilePath → StoppableRunUnlink Unit) :
    EStateM.Result FilePath ReachedState (Except IO.Error Unit) :=
  let stateAt (files : DescriptorInventory × RunUnlinkImage) : ReachedState :=
    (state.session.phase, ⟨(state.cache, files), state.files.owners⟩)
  match stop.run barrier with
  | .ok value files => .ok value (stateAt files)
  | .error path files => .error path (stateAt files)

end NativeObsoleteRunUnlinkStop

/-- An interrupted unlink has its own endpoint and no native return.
The reached slot/census report and run map preserve the bounded reads
and selected checkpoint before any recovery is attempted. -/
theorem NativeReadPosition.stopsDuringObsoleteRunUnlink (current : NativeReadPosition history log)
    (cut : NativeObsoleteRunUnlinkCut current.state) (stop : NativeObsoleteRunUnlinkStop cut) :
    (∀ barrier, stop.runFromReady barrier = .error cut.path
      (.ready current.state.writer.installed, ⟨(current.state.cache, cut.reachedCensus, cut.reached), current.state.files.owners⟩)) ∧
    current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor ∧
    (∀ candidate ∈ cut.reached.crashImages,
      SelectedIntegrityCheckpoint candidate current.state.writer.target.pair.manifest current.state.writer.checkpoint) ∧
    (∀ generation index bytes,
      current.state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
      cut.plan.initial.guaranteed generation index = some bytes →
      cut.reached.guaranteed generation index = some bytes) ∧
    PendingClientReplay log current.reads history ∧ ∀ read ∈ current.reads, read.BoundedBy history.length := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨_, survivors, kept⟩ := cut.preservesReady valid
  refine ⟨?_, valid.retained.held, survivors, kept, replay, current.readPrefix.readsBounded⟩
  intro barrier
  rw [NativeObsoleteRunUnlinkStop.runFromReady, stop.stops valid barrier, valid.phase]

end Alvoki.Storage.DiskSession
