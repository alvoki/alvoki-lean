import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.OptionalFileRead
import Alvoki.Storage.Disk.LockedRunCollection

namespace Alvoki.Storage.DiskSession

open System Manifest CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Replace the run guarantees with the projection of the reached namespace.
The live writer's table, pins, WAL and owner stay fixed. -/
def SegmentedWriterState.afterRunCollection (state : SegmentedWriterState) (runs : RunFiles) :
    SegmentedWriterState :=
  { state with published := { state.published with durable := runs } }

private theorem keepSelectedCheckpoint {published : Image} {binding : Option ByteArray}
    {checkpoint : Option (PackedTable × UInt64)} {generation count : UInt64}
    {expected : Checkpoint → List ByteArray → Prop}
    (selected : SelectedIntegrityCheckpoint published.durable binding checkpoint)
    (accepted : published.AcceptsVersioned count expected binding)
    (installed : generation = (checkpoint.getD (.empty, 0)).2)
    {runs : RunFiles}
    (keep : ∀ index bytes, published.durable generation index = some bytes → runs generation index = some bytes) :
    SelectedIntegrityCheckpoint runs binding checkpoint ∧
      ({ published with durable := runs } : Image).AcceptsVersioned count expected binding := by
  cases selected with
  | absent => exact ⟨.absent, trivial⟩
  | @present bytes manifest files table decoded stored loaded =>
    obtain ⟨acceptedFiles, witness⟩ := (Image.acceptsVersioned_integrity_iff decoded).mp accepted
    have sameFiles := Option.some.inj (witness.ordered.symm.trans stored)
    subst acceptedFiles
    have generationExact : generation = manifest.header.generation := installed
    have kept := witness.withKeptRuns (after := runs) (fun index inside => by
      have known := (witness.durable index inside).trans (List.getElem?_eq_getElem inside)
      rw [← generationExact] at known ⊢
      exact (keep _ _ known).trans known.symm)
    exact ⟨.present decoded kept.ordered loaded, (Image.acceptsVersioned_integrity_iff decoded).mpr ⟨files, kept⟩⟩

/-- The reached run projection preserves the same exact checkpoint, and
every admitted crash run map also selects it under the retained writer's
settled manifest. File effects on the WAL and owner are outside this run
namespace projection. -/
theorem SegmentedWriterState.RetainedReady.afterRunCollection {directory descriptor} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) {approved : List RunAddress} {before after : RunUnlinkImage}
    (retry : RunUnlinkRetry approved before after)
    (older : ∀ address ∈ approved, address.1 < state.installed.generation)
    (known : ∀ index bytes, state.published.durable state.installed.generation index = some bytes →
      before.guaranteed state.installed.generation index = some bytes) :
    (state.afterRunCollection after.guaranteed).RetainedReady directory descriptor ∧
      ∀ survived ∈ after.crashImages, SelectedIntegrityCheckpoint survived state.target.pair.manifest state.checkpoint := by
  have excluded (index : Nat) : (state.installed.generation, index) ∉ approved :=
    fun chosen => UInt64.lt_irrefl _ (older _ chosen)
  obtain ⟨selected, accepted⟩ := keepSelectedCheckpoint ready.resumed.selected ready.resumed.accepted
    ready.resumed.generation (fun index bytes stored => retry.keepsKnown (known index bytes stored) (excluded index))
  refine ⟨{ ready with resumed := { ready.resumed with selected := selected, accepted := accepted } }, ?_⟩
  intro survived observed
  have sameMap : (RunUnlinkImage.settled survived).guaranteed = survived :=
    congrArg Image.durable (RunUnlinkImage.project_settled survived state.published.manifest)
  exact (keepSelectedCheckpoint ready.resumed.selected ready.resumed.accepted ready.resumed.generation
    (fun index bytes stored => sameMap ▸ (retry.crash observed).keepsKnown (known index bytes stored) (excluded index))).1

/-- The reached successful read-only reports and the unlink and directory
sync callbacks of `DiskTable.collectObsoleteRuns_fileEffects`. The
cooperating writer owns the canonical parent, and external holds and
unrelated file bindings stay fixed throughout the pass. -/
structure SegmentedRunCollectionReports (directory : DiskDirectory) (state : SegmentedWriterState)
    (before : RunUnlinkImage) where
  manifest : OptionalPathRead state.files.directory.active.manifest
  observed : Option ByteArray
  manifestRead : manifest.result (directory.file .manifest) = .ok observed
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  entries : Array IO.FS.DirEntry
  listed : list directory.path = .ok entries
  regularAt : FilePath → Prop
  inventory : LockedRunInventory directory regularAt
  names : entries.toList.map (·.fileName) = inventory.names
  known : ∀ index bytes, state.published.durable state.installed.generation index = some bytes →
    before.guaranteed state.installed.generation index = some bytes
  held : List UInt64
  removeFile : FilePath → EStateM IO.Error RunUnlinkImage (Except IO.Error Unit)
  syncDirectory : FilePath → EStateM IO.Error RunUnlinkImage Unit
  effects : RunUnlinkEffectContract (RunCollection.performPaths removeFile syncDirectory throw
    (fun address : RunAddress => directory.file (.run address.1 address.2)) directory.path)

namespace SegmentedRunCollectionReports

variable {directory : DiskDirectory} {state : SegmentedWriterState} {before : RunUnlinkImage}

def perform (reports : SegmentedRunCollectionReports directory state before) :
    RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit :=
  RunCollection.performPaths reports.removeFile reports.syncDirectory throw
    (fun address => directory.file (.run address.1 address.2)) directory.path

/-- Follow the real collector's preflight, checked listing, no-follow
selector, canonical unlinks and final sync, in the same order. -/
def run (reports : SegmentedRunCollectionReports directory state before) :
    EStateM.Result IO.Error RunUnlinkImage Unit :=
  (do
    let manifest ← liftExcept (reports.manifest.result (directory.file .manifest))
    let current ← liftExcept (Except.mapError IO.userError
      (validateIntegrityRunCollectionGeneration state.installed.generation manifest))
    let entries ← liftExcept (reports.list directory.path)
    let selected ← selectRunFilesWith directory current (retainRunGeneration state.installed.generation reports.held)
      (fun path => pure (reports.inventory.kindAt path)) (entries.toList.map (·.fileName))
    RunCollection.run selected reports.perform : EStateM IO.Error RunUnlinkImage Unit) before

def selected (reports : SegmentedRunCollectionReports directory state before) : List RunAddress :=
  selectRunFiles directory (reports.observed.map fun _ => state.installed.generation)
    (retainRunGeneration state.installed.generation reports.held) reports.inventory.kindAt reports.inventory.names

def reached (reports : SegmentedRunCollectionReports directory state before) : RunUnlinkImage :=
  match reports.run with
  | .ok _ after | .error _ after => after

theorem preflight {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) :
    validateIntegrityRunCollectionGeneration state.installed.generation reports.observed =
      .ok (reports.observed.map fun _ => state.installed.generation) := by
  rw [← reports.manifest.resultVisible (directory.file .manifest) reports.manifestRead, ready.resumed.ready.selected]
  have checked := SelectedIntegrityCheckpoint.collectionGeneration ready.resumed.selected
  dsimp only at checked
  rwa [← ready.resumed.generation] at checked

theorem run_eq_schedule {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) :
    reports.run = RunCollection.run reports.selected reports.perform before := by
  have checked :
      Except.mapError IO.userError (validateIntegrityRunCollectionGeneration state.installed.generation reports.observed) =
        .ok (reports.observed.map fun _ => state.installed.generation) := by
    rw [reports.preflight ready]
    rfl
  simp only [run, reports.manifestRead, checked, reports.listed, liftExcept, pure_bind, reports.names,
    selectRunFilesWith_pure, selected]

theorem selected_eligible {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) {generation : UInt64} {index : Nat} :
    (generation, index) ∈ reports.selected ↔
      renderRunFileName generation index ∈ reports.inventory.names ∧ generation < state.installed.generation ∧
      generation ∉ reports.held ∧ reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file :=
  reports.inventory.selectOlderRunsAt_iff reports.held
    (validateObservedRunGeneration_ok_iff.mp (reports.preflight ready)).2

/-- Both returned outcomes extend the same approved namespace lineage.
Each retry supplies its own checked visible inventory. -/
theorem extendsRetry {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before)
    {approved : List RunAddress} {initial : RunUnlinkImage} (prior : RunUnlinkRetry approved initial before)
    (covers : ∀ address ∈ reports.selected, address ∈ approved) :
    RunUnlinkRetry approved initial reports.reached := by
  have effects := prior.runSchedule reports.selected covers reports.perform reports.effects
  rw [← reports.run_eq_schedule ready] at effects
  cases execution : reports.run <;> simpa only [reached, execution] using effects

private theorem selectedOlder {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) :
    ∀ address ∈ reports.selected, address.1 < state.installed.generation := by
  rintro ⟨generation, index⟩ chosen
  exact ((reports.selected_eligible ready).mp chosen).2.1

/-- Use the exact returned namespace on success or failure, including a
completed deletion or barrier that reported an error. The continued writer
is ready and every admitted run crash map keeps its old selected checkpoint. -/
theorem preservesRetained {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) :
    (state.afterRunCollection reports.reached.guaranteed).RetainedReady directory descriptor ∧
      ∀ survived ∈ reports.reached.crashImages,
        SelectedIntegrityCheckpoint survived state.target.pair.manifest state.checkpoint :=
  ready.afterRunCollection (reports.extendsRetry ready (.start before) (fun _ chosen => chosen))
    (reports.selectedOlder ready) reports.known

/-- A reported interruption chooses a prefix of the checked native
unlink/barrier schedule. A machine crash then selects an admitted run map
at that cut, with the exact old checkpoint still available. The next
writer must acquire and reopen through its own reported observations. -/
theorem crashAtCut {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before)
    {approved : List RunAddress} {initial : RunUnlinkImage} (prior : RunUnlinkRetry approved initial before)
    (covers : ∀ address ∈ reports.selected, address ∈ approved) (cut : Nat) {survived : RunFiles}
    (survivor : survived ∈ (((RunCollection.steps reports.selected).take cut).foldl
      RunUnlinkImage.applyCollectionStep before).crashImages) :
    RunUnlinkRetry approved initial (.settled survived) ∧
      SelectedIntegrityCheckpoint survived state.target.pair.manifest state.checkpoint := by
  have atCut := (RunUnlinkRetry.start (approved := reports.selected) before).interruptedSchedule
    reports.selected (fun _ chosen => chosen) cut
  exact ⟨(prior.interruptedSchedule reports.selected covers cut).crash survivor,
    (ready.afterRunCollection atCut (reports.selectedOlder ready) reports.known).2 survived survivor⟩

/-- A healthy retry on a complete current inventory ends a finite lineage
of admitted partial passes or crashes. It durably removes every eligible
name, including names already hidden at retry entry. It keeps original
known bytes outside the older unheld set and selects the exact current
checkpoint from the sole surviving run map. -/
theorem completeAfterRetries {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before)
    {approved : List RunAddress} {initial : RunUnlinkImage} (prior : RunUnlinkRetry approved initial before)
    (approvedOlderUnheld : ∀ address ∈ approved,
      address.1 < state.installed.generation ∧ address.1 ∉ reports.held)
    (covers : ∀ address ∈ reports.selected, address ∈ approved)
    (complete : ∀ generation index bytes, before.visible generation index = some bytes →
      generation < state.installed.generation → generation ∉ reports.held →
      renderRunFileName generation index ∈ reports.inventory.names ∧
        reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file)
    (healthy : RunUnlinkScheduleHealthy before (RunCollection.steps reports.selected) reports.perform) :
    let after := before.finishPass reports.selected
    reports.run = .ok () after ∧ RunUnlinkRetry approved initial after ∧
      after.crashImages = [after.visible] ∧ after.guaranteed = after.visible ∧
      (∀ generation index, after.visible generation index =
        if (generation, index) ∈ reports.selected then none else before.visible generation index) ∧
      (∀ generation index, generation < state.installed.generation → generation ∉ reports.held →
        after.DurablyAbsent (generation, index)) ∧
      (∀ generation index bytes, state.installed.generation ≤ generation ∨ generation ∈ reports.held →
        initial.guaranteed generation index = some bytes → after.guaranteed generation index = some bytes) ∧
      (state.afterRunCollection after.guaranteed).RetainedReady directory descriptor ∧
      SelectedIntegrityCheckpoint after.visible state.target.pair.manifest state.checkpoint := by
  intro after
  have returned := (reports.run_eq_schedule ready).trans
    (runUnlinkSchedule_success _ before reports.perform reports.effects healthy)
  have reached : reports.reached = after := by simp only [SegmentedRunCollectionReports.reached, returned, after]
  have lineage := reports.extendsRetry ready prior covers
  have preserved := reports.preservesRetained ready
  rw [reached] at lineage preserved
  have sameMap : after.guaranteed = after.visible :=
    congrArg Image.durable (RunUnlinkImage.project_settled after.visible state.published.manifest)
  have matching := (validateObservedRunGeneration_ok_iff.mp (reports.preflight ready)).2
  refine ⟨returned, lineage, rfl, sameMap,
    fun generation index => (before.finishPass_binding reports.selected (generation, index)).1,
    reports.inventory.finishOlderPass_absent before reports.held matching complete, ?_,
    preserved.1, preserved.2 after.visible List.mem_cons_self⟩
  intro generation index bytes keepGeneration known
  apply lineage.keepsKnown (name := (generation, index)) known
  intro chosen
  obtain ⟨older, unheld⟩ := approvedOlderUnheld _ chosen
  exact keepGeneration.elim (fun le => UInt64.not_lt.mpr le older) unheld

/-- For one run name, the reached unlink prefix and an effective final
barrier suffice. The name was selected by this pass or already absent
at entry. A reported error after settlement has the same durability
consequence. Later collection retries preserve that absence. -/
theorem reclaimsAfterEffectiveBarrier {descriptor : Nat} (ready : state.RetainedReady directory descriptor)
    (reports : SegmentedRunCollectionReports directory state before) {name : RunAddress}
    (collectible : name ∈ reports.selected ∨ before.visible name.1 name.2 = none)
    {atBarrier : RunUnlinkImage}
    (unlinked : ((reports.selected.map RunCollection.Step.unlink).forM reports.perform) before = .ok () atBarrier)
    (synced : reports.perform .syncDirectory atBarrier = .ok () atBarrier.syncDirectory ∨
      ∃ cause, reports.perform .syncDirectory atBarrier = .error cause atBarrier.syncDirectory) :
    reports.run = reports.perform .syncDirectory atBarrier ∧
      reports.reached = before.finishPass reports.selected ∧ reports.reached.DurablyAbsent name ∧
      ∀ {approved : List RunAddress} {later : RunUnlinkImage}, RunUnlinkRetry approved reports.reached later →
        later.DurablyAbsent name := by
  obtain ⟨barrier, exactImage⟩ := runUnlinkSchedule_reachesBarrier reports.selected reports.perform reports.effects unlinked
  have ran := (reports.run_eq_schedule ready).trans barrier
  have settled : reports.reached = before.finishPass reports.selected := by
    rcases synced with synced | ⟨_, synced⟩ <;>
      simp only [reached, ran, synced, exactImage]
  have absent : reports.reached.DurablyAbsent name := by
    rw [settled]
    exact (before.finishPass_absent_iff reports.selected name).mpr collectible
  exact ⟨ran, settled, absent, fun retry => retry.keepsAbsent absent⟩

end SegmentedRunCollectionReports
end Alvoki.Storage.DiskSession
