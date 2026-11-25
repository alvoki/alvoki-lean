import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.SegmentedRunCollection
import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

/-- Interpret the production no-follow probe. Linux ENOENT denotes an
absent run. Every other lookup error stops the selector. -/
private def runKindAt (stat : FilePath → Except IO.Error IO.FS.Metadata) (path : FilePath) :
    Except IO.Error (Except String IO.FS.FileType) :=
  match stat path with
  | .ok metadata => .ok (.ok metadata.type)
  | .error (.noFileOrDirectory _ 2 _) => .ok (.error "run file is absent")
  | .error cause => .error cause

private def directoryImage (atBarrier : RunUnlinkImage) (outcome : DelayedDirectorySyncOutcome) : RunUnlinkImage :=
  if outcome.effective then atBarrier.syncDirectory else atBarrier

private def syncResult (outcome : DelayedDirectorySyncOutcome) (reached : α) :
    EStateM.Result IO.Error α Unit :=
  match outcome with
  | .completed => .ok () reached
  | .errorBeforeEffect cause | .errorAfterEffect cause => .error cause reached

private def groupedResult (directory : DiskDirectory) (outcome : DelayedDirectorySyncOutcome) (reached : α) :
    EStateM.Result IO.Error α Unit :=
  match outcome with
  | .completed => .ok () reached
  | .errorBeforeEffect cause | .errorAfterEffect cause =>
    .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached

/-- The checked manifest, directory listing and ordered no-follow
probes of an obsolete-run pass determine the exact unlinks the
collector may issue under the caller's holds. -/
structure NativeObsoleteRunPlan (state : NativeReadyState) where
  initial : RunUnlinkImage
  reports : SegmentedRunCollectionReports state.session.directory state.writer initial
  lifetime : HeldDirectoryReadLifetime state.census state.owner
  cachedSlot : lifetime.directorySlot = state.directorySlot
  listing : HeldDirectoryScan lifetime
  listCallback : reports.list state.session.directory.path =
    (CheckedDirectoryReadReport.scanned listing.scan).result state.session.directory.path
  beforeOpen : listing.beforeOpen = []
  duringScan : listing.duringScan = []
  stat : FilePath → Except IO.Error IO.FS.Metadata
  kind : ∀ generation index, renderRunFileName generation index ∈ reports.inventory.names →
    generation < state.writer.installed.generation → generation ∉ reports.held →
    runKindAt stat (state.session.directory.file (.run generation index)) =
      .ok (reports.inventory.kindAt (state.session.directory.file (.run generation index)))
/-- The pass has returned from all of its unlinks and reached the final
directory barrier on the original cached handle. -/
structure NativeObsoleteRunPass (state : NativeReadyState) extends NativeObsoleteRunPlan state where
  complete : ∀ generation index bytes, initial.visible generation index = some bytes →
    generation < state.writer.installed.generation → generation ∉ reports.held →
    renderRunFileName generation index ∈ lifetime.namespaceView.names lifetime.root ∧
      reports.inventory.kindAt (state.session.directory.file (.run generation index)) = .ok .file
  atBarrier : RunUnlinkImage
  unlinked : ((reports.selected.map RunCollection.Step.unlink).forM reports.perform) initial = .ok () atBarrier
  beforeBarrierDrops : List LockReferenceDrop
  afterBarrierDrops : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots, ∀ drop ∈ beforeBarrierDrops ++ afterBarrierDrops,
    drop.removes slot.reference = false
  capture : DescriptorInventory
  cached : state.cache.directory = some (capture, state.directorySlot, 0)
  capturedInode : capture.inode state.directorySlot.description = state.census.inode state.directorySlot.description
  pathObject : DescriptorInventory × RunUnlinkImage → FilePath → Option DeviceInode
  atPath : pathObject (listing.afterClose.afterDrops beforeBarrierDrops, atBarrier) state.session.directory.path =
    some lifetime.root
  atLock : pathObject (listing.afterClose.afterDrops beforeBarrierDrops, atBarrier)
    (state.session.directory.file .lock) = some lifetime.lock
  outcome : DelayedDirectorySyncOutcome
  keepsBindings : ∀ path ∈ [state.session.directory.path, state.session.directory.file .lock],
    pathObject ((listing.afterClose.afterDrops beforeBarrierDrops).afterDrops afterBarrierDrops,
      directoryImage atBarrier outcome) path =
      pathObject (listing.afterClose.afterDrops beforeBarrierDrops, atBarrier) path
  openRead : FilePath → EStateM IO.Error (DescriptorInventory × RunUnlinkImage) CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM IO.Error (DescriptorInventory × RunUnlinkImage) Unit
  synced : fsync (capture, state.directorySlot, 0) (listing.afterClose.afterDrops beforeBarrierDrops, atBarrier) =
    syncResult outcome ((listing.afterClose.afterDrops beforeBarrierDrops).afterDrops afterBarrierDrops,
      directoryImage atBarrier outcome)
  syncProjection : reports.syncDirectory state.session.directory.path atBarrier =
    match SyncPathGroup.run (sync state.session.directory.path openRead fsync)
      #[state.session.directory.path] (state.cache, (listing.afterClose.afterDrops beforeBarrierDrops, atBarrier)) with
    | .ok value (_, (_, reached)) => .ok value reached
    | .error cause (_, (_, reached)) => .error cause reached

namespace NativeObsoleteRunPlan

variable {state : NativeReadyState}

theorem checkedNames (seen : NativeObsoleteRunPlan state) :
    seen.reports.inventory.names.Perm (seen.lifetime.namespaceView.names seen.lifetime.root) := by
  obtain ⟨returned, names⟩ := CheckedDirectoryReadReport.scan_complete state.session.directory.path
    seen.listing.eof seen.listing.closed seen.listing.complete
  have listed := Except.ok.inj (seen.reports.listed.symm.trans (seen.listCallback.trans returned))
  rw [← seen.reports.names, listed]
  simpa only [seen.listing.sameRoot] using names

theorem preservesCensus (seen : NativeObsoleteRunPlan state) : seen.listing.afterClose = state.census := by
  rw [seen.listing.afterClose_eq, seen.listing.drops, seen.beforeOpen, seen.duringScan]
  have free : ∀ slot ∈ state.census.slots, slot.address ≠ seen.listing.stream.address := by
    simpa [seen.beforeOpen, DescriptorInventory.afterDrops] using seen.listing.free
  have stays (inventory : DescriptorInventory) (stream : DescriptorSlot)
      (available : ∀ slot ∈ inventory.slots, slot.address ≠ stream.address) :
      inventory.afterDrops [stream.closeEvent] = inventory := by
    cases inventory with
    | mk slots distinct inode =>
      simp only [DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
      apply List.filter_eq_self.mpr
      intro old member
      by_cases process : old.reference.process = stream.reference.process
      · have different : old.reference.fd ≠ stream.reference.fd := fun same =>
          available old member (Prod.ext process same)
        simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process, different]
      · simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process]
  exact stays state.census seen.listing.stream free

/-- The exact metadata at the selected no-follow probe is regular. -/
theorem reportedRegular (seen : NativeObsoleteRunPlan state) {generation : UInt64} {index : Nat}
    (listed : renderRunFileName generation index ∈ seen.reports.inventory.names)
    (older : generation < state.writer.installed.generation) (unheld : generation ∉ seen.reports.held)
    {metadata : IO.FS.Metadata} (reported : seen.stat (state.session.directory.file (.run generation index)) = .ok metadata)
    (regular : seen.reports.inventory.kindAt (state.session.directory.file (.run generation index)) = .ok .file) :
    metadata.type = .file := by
  simpa [runKindAt, reported, regular, Bind.bind, Except.bind, Pure.pure, Except.pure]
    using seen.kind generation index listed older unheld

private theorem selectsFromLstat (seen : NativeObsoleteRunPlan state) :
    selectRunFilesWith (m := Except IO.Error) state.session.directory
      (seen.reports.observed.map fun _ => state.writer.installed.generation)
      (retainRunGeneration state.writer.installed.generation seen.reports.held)
      (runKindAt seen.stat) seen.reports.inventory.names = .ok seen.reports.selected := by
  let current := seen.reports.observed.map fun _ => state.writer.installed.generation
  let retained := retainRunGeneration state.writer.installed.generation seen.reports.held
  let kind := seen.reports.inventory.kindAt
  have scans (names : List String) (included : ∀ name ∈ names, name ∈ seen.reports.inventory.names) :
      selectRunFilesWith (m := Except IO.Error) state.session.directory current retained (runKindAt seen.stat) names =
        .ok (selectRunFiles state.session.directory current retained kind names) := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
      have tail := ih (fun _ member => included _ (List.mem_cons_of_mem _ member))
      have first :
          selectRunFileWith (m := Except IO.Error) state.session.directory current retained (runKindAt seen.stat) name =
            .ok (selectRunFile state.session.directory current retained kind name) := by
        cases parsed : parseRunFileName name with
        | none => simp [selectRunFile, selectRunFileWith, parsed, Pure.pure, Except.pure]
        | some address =>
          obtain ⟨generation, index⟩ := address
          by_cases eligible : current ≠ some generation ∧ retained generation = false
          · have listed := included name List.mem_cons_self
            rw [parseRunFileName_sound parsed] at listed
            obtain ⟨older, unheld⟩ := retainRunGeneration_false_iff.mp eligible.2
            simp [selectRunFile, selectRunFileWith, parsed, eligible, seen.kind generation index listed older unheld,
              Bind.bind, Except.bind, Pure.pure, Except.pure, kind]
          · simp [selectRunFile, selectRunFileWith, parsed, eligible, Pure.pure, Except.pure]
      simp only [selectRunFilesWith, List.filterMapM_cons, selectRunFiles, List.filterMap_cons, first,
        Bind.bind, Except.bind] at tail ⊢
      cases selectRunFile state.session.directory current retained kind name <;>
        simp [tail, Pure.pure, Except.pure]
  exact scans _ (fun _ member => member)

/-- The checked read-only preflight of the actual native collector.
The phase is read before the manifest, directory list and lstat probes. -/
def plan (seen : NativeObsoleteRunPlan state) : Except IO.Error (List RunAddress) := do
  let installed ← state.session.phase.installed
  let manifest ← seen.reports.manifest.result (state.session.directory.file .manifest)
  let current ← (validateIntegrityRunCollectionGeneration installed.generation manifest).mapError IO.userError
  let entries ← seen.reports.list state.session.directory.path
  selectRunFilesWith state.session.directory current (retainRunGeneration installed.generation seen.reports.held)
    (runKindAt seen.stat) (entries.toList.map (·.fileName))

theorem plans (seen : NativeObsoleteRunPlan state) (valid : state.Valid) :
    seen.plan = .ok seen.reports.selected := by
  simp only [plan, valid.phase, Phase.installed, Pure.pure, Except.pure, Bind.bind, Except.bind,
    seen.reports.manifestRead, seen.reports.preflight valid.retained, Except.mapError, seen.reports.listed,
    seen.reports.names]
  exact seen.selectsFromLstat

def run (seen : NativeObsoleteRunPlan state) :
    EStateM.Result IO.Error (Phase Installed × LockedFileState (CensusDirectoryCache × RunUnlinkImage)) Unit :=
  let reached (image : RunUnlinkImage) :=
    (state.session.phase, (⟨(state.cache, image), state.files.owners⟩ :
      LockedFileState (CensusDirectoryCache × RunUnlinkImage)))
  match seen.plan with
  | .error cause => .error cause (reached seen.initial)
  | .ok selected =>
    match RunCollection.run selected seen.reports.perform seen.initial with
    | .ok () after => .ok () (reached after)
    | .error cause after => .error cause (reached after)

private theorem inventoryKeepsSlots (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    (kept : ∀ slot ∈ inventory.slots, ∀ drop ∈ drops, drop.removes slot.reference = false) :
    inventory.afterDrops drops = inventory := by
  cases inventory with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
    apply List.filter_eq_self.mpr
    intro slot present
    exact List.all_eq_true.mpr fun drop occurred => by simp [kept slot present drop occurred]

/-- The reached inventory includes the checked listing's stream close
and then the reported slot events before the next native callback. -/
theorem keepsCensus (seen : NativeObsoleteRunPlan state) (drops : List LockReferenceDrop)
    (kept : ∀ slot ∈ state.census.slots, ∀ drop ∈ drops, drop.removes slot.reference = false) :
    seen.listing.afterClose.afterDrops drops = state.census := by
  rw [seen.preservesCensus]
  exact inventoryKeepsSlots state.census drops kept

end NativeObsoleteRunPlan

namespace NativeObsoleteRunPass

variable {state : NativeReadyState}

abbrev plan (seen : NativeObsoleteRunPass state) := seen.toNativeObsoleteRunPlan.plan

def issueCensus (seen : NativeObsoleteRunPass state) : DescriptorInventory :=
  seen.listing.afterClose.afterDrops seen.beforeBarrierDrops

def returnCensus (seen : NativeObsoleteRunPass state) : DescriptorInventory :=
  seen.issueCensus.afterDrops seen.afterBarrierDrops

theorem barrierCensus (seen : NativeObsoleteRunPass state) :
    seen.issueCensus = state.census ∧ seen.returnCensus = state.census := by
  have issue : seen.issueCensus = state.census :=
    seen.toNativeObsoleteRunPlan.keepsCensus seen.beforeBarrierDrops fun slot live drop occurred =>
      seen.keepsSlots slot live drop (List.mem_append_left _ occurred)
  have returned := seen.toNativeObsoleteRunPlan.keepsCensus seen.afterBarrierDrops fun slot live drop occurred =>
    seen.keepsSlots slot live drop (List.mem_append_right _ occurred)
  exact ⟨issue, by simpa only [returnCensus, issue, seen.toNativeObsoleteRunPlan.preservesCensus] using returned⟩

/-- The last scheduled callback resolves the original cached directory
handle and settles the same namespace reached by the preceding unlinks. -/
theorem syncs (seen : NativeObsoleteRunPass state) :
    SyncPathGroup.run (sync state.session.directory.path seen.openRead seen.fsync)
      #[state.session.directory.path] (state.cache, (seen.issueCensus, seen.atBarrier)) =
        groupedResult state.session.directory seen.outcome
          (state.cache, (seen.returnCensus, directoryImage seen.atBarrier seen.outcome)) := by
  rw [SyncPathGroup.run_single]
  simp only [SyncHandleRouting.sync, Cache.resolve, beq_self_eq_true, ↓reduceIte, seen.cached,
    withCache, issueCensus, returnCensus, seen.synced]
  cases seen.outcome <;> rfl

abbrev run (seen : NativeObsoleteRunPass state) := seen.toNativeObsoleteRunPlan.run

def after (seen : NativeObsoleteRunPass state) : RunUnlinkImage :=
  directoryImage seen.atBarrier seen.outcome

theorem after_eq (seen : NativeObsoleteRunPass state) :
    seen.after = if seen.outcome.effective then seen.atBarrier.syncDirectory else seen.atBarrier := rfl

def next (seen : NativeObsoleteRunPass state) : NativeReadyState :=
  { state with
    writer := state.writer.afterRunCollection seen.after.guaranteed
    census := seen.returnCensus }

theorem returns (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    seen.reports.run = groupedResult state.session.directory seen.outcome seen.after ∧
    seen.run = groupedResult state.session.directory seen.outcome
      (seen.next.session.phase, ⟨(seen.next.cache, seen.after), seen.next.files.owners⟩) ∧
    seen.atBarrier.syncDirectory = seen.initial.finishPass seen.reports.selected := by
  obtain ⟨atBarrier, exactImage⟩ := runUnlinkSchedule_reachesBarrier seen.reports.selected
    seen.reports.perform seen.reports.effects seen.unlinked
  have synced : seen.reports.perform .syncDirectory seen.atBarrier =
      groupedResult state.session.directory seen.outcome seen.after := by
    rw [SegmentedRunCollectionReports.perform, RunCollection.performPaths, seen.syncProjection]
    have projected := congrArg (fun result => match result with
      | .ok value (_, (_, reached)) => EStateM.Result.ok value reached
      | .error cause (_, (_, reached)) => EStateM.Result.error cause reached) seen.syncs
    cases status : seen.outcome <;> simpa only [status, groupedResult, after, issueCensus] using projected
  have completed := atBarrier.trans synced
  refine ⟨(seen.reports.run_eq_schedule valid.retained).trans completed, ?_, exactImage⟩
  simp only [run, NativeObsoleteRunPlan.run, seen.toNativeObsoleteRunPlan.plans valid, completed]
  cases seen.outcome <;> rfl

private theorem reached (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    seen.reports.reached = seen.after := by
  rw [SegmentedRunCollectionReports.reached, (seen.returns valid).1]
  cases seen.outcome <;> rfl

theorem preservesReady (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    seen.next.Valid ∧
    ∀ survived ∈ seen.after.crashImages,
      SelectedIntegrityCheckpoint survived state.writer.target.pair.manifest state.writer.checkpoint := by
  have preserved := seen.reports.preservesRetained valid.retained
  rw [seen.reached valid] at preserved
  exact ⟨{ valid with ownerLive := by simpa only [next, seen.barrierCensus.2] using valid.ownerLive,
                      directoryLive := by simpa only [next, seen.barrierCensus.2] using valid.directoryLive,
                      retained := preserved.1 }, preserved.2⟩

/-- A directory sync that takes effect after the reached unlink prefix
settles all eligible old absences, including names hidden at entry. -/
theorem settlesOldRuns (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    ∀ generation index, generation < state.writer.installed.generation → generation ∉ seen.reports.held →
      seen.atBarrier.syncDirectory.DurablyAbsent (generation, index) := by
  rw [(seen.returns valid).2.2]
  have checked := (validateObservedRunGeneration_ok_iff.mp (seen.reports.preflight valid.retained)).2
  exact seen.reports.inventory.finishOlderPass_absent seen.initial seen.reports.held checked
    (fun generation index bytes present older unheld =>
      let known := seen.complete generation index bytes present older unheld
      ⟨seen.toNativeObsoleteRunPlan.checkedNames.mem_iff.mpr known.1, known.2⟩)

theorem retainsNamedBytes (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    ∀ generation index bytes, state.writer.installed.generation ≤ generation ∨ generation ∈ seen.reports.held →
      seen.initial.guaranteed generation index = some bytes →
      seen.after.guaranteed generation index = some bytes := by
  have retry := seen.reports.extendsRetry valid.retained (.start seen.initial) (fun _ member => member)
  rw [seen.reached valid] at retry
  intro generation index bytes keep original
  apply retry.keepsKnown (name := (generation, index)) original
  intro selected
  have eligible := (seen.reports.selected_eligible valid.retained).mp selected
  exact keep.elim (fun current => UInt64.not_lt.mpr current eligible.2.1) eligible.2.2.1

/-- The reached slot intervals feed the actual barrier call and its
return. The original cached directory and lock objects agree with the
path reports at both points. -/
theorem custody (seen : NativeObsoleteRunPass state) (valid : state.Valid) :
    seen.listing.Custody ∧ seen.issueCensus = state.census ∧ seen.returnCensus = state.census ∧
    state.directorySlot ∈ seen.issueCensus.slots ∧ state.owner ∈ seen.issueCensus.slots ∧
    state.directorySlot ∈ seen.returnCensus.slots ∧ state.owner ∈ seen.returnCensus.slots ∧
    seen.lifetime.namespaceView.modelObject seen.lifetime.root = seen.capture.inode state.directorySlot.description ∧
    seen.capture.inode state.directorySlot.description = seen.issueCensus.inode state.directorySlot.description ∧
    seen.lifetime.namespaceView.modelObject seen.lifetime.lock = seen.issueCensus.inode state.owner.description ∧
    seen.pathObject (seen.issueCensus, seen.atBarrier) state.session.directory.path = some seen.lifetime.root ∧
    seen.pathObject (seen.issueCensus, seen.atBarrier) (state.session.directory.file .lock) = some seen.lifetime.lock ∧
    seen.pathObject (seen.returnCensus, seen.after) state.session.directory.path = some seen.lifetime.root ∧
    seen.pathObject (seen.returnCensus, seen.after) (state.session.directory.file .lock) =
      some seen.lifetime.lock := by
  obtain ⟨issue, returned⟩ := seen.barrierCensus
  have directory := seen.keepsBindings state.session.directory.path (by simp)
  have lock := seen.keepsBindings (state.session.directory.file .lock) (by simp)
  refine ⟨seen.listing.custody, issue, returned, issue.symm ▸ valid.directoryLive, issue.symm ▸ valid.ownerLive,
    returned.symm ▸ valid.directoryLive, returned.symm ▸ valid.ownerLive, ?_, issue.symm ▸ seen.capturedInode,
    issue.symm ▸ seen.lifetime.identifiesLock, seen.atPath, seen.atLock,
    directory.trans seen.atPath, lock.trans seen.atLock⟩
  rw [seen.capturedInode, ← seen.cachedSlot]
  exact seen.lifetime.identifiesDirectory

end NativeObsoleteRunPass

/-- A completed obsolete-run collector is a pass whose final barrier
reported success. -/
structure NativeObsoleteRunCollection (state : NativeReadyState) extends NativeObsoleteRunPass state where
  completed : outcome = .completed

namespace NativeObsoleteRunCollection

variable {state : NativeReadyState}

abbrev run (seen : NativeObsoleteRunCollection state) := seen.toNativeObsoleteRunPass.run

abbrev next (seen : NativeObsoleteRunCollection state) := seen.toNativeObsoleteRunPass.next

theorem after_eq (seen : NativeObsoleteRunCollection state) :
    seen.toNativeObsoleteRunPass.after = seen.atBarrier.syncDirectory := by
  simp [NativeObsoleteRunPass.after, directoryImage, seen.completed, DelayedDirectorySyncOutcome.effective]

theorem returns (seen : NativeObsoleteRunCollection state) (valid : state.Valid) :
    seen.reports.run = .ok () seen.atBarrier.syncDirectory ∧
    seen.run = .ok () (seen.next.session.phase,
      ⟨(seen.next.cache, seen.atBarrier.syncDirectory), seen.next.files.owners⟩) ∧
    seen.atBarrier.syncDirectory = seen.initial.finishPass seen.reports.selected := by
  simpa only [seen.completed, groupedResult, seen.after_eq] using seen.toNativeObsoleteRunPass.returns valid

theorem reclaims (seen : NativeObsoleteRunCollection state) (valid : state.Valid) :
    (∀ generation index, (generation, index) ∈ seen.reports.selected ↔
      renderRunFileName generation index ∈ seen.lifetime.namespaceView.names seen.lifetime.root ∧
      generation < state.writer.installed.generation ∧ generation ∉ seen.reports.held ∧
      seen.reports.inventory.kindAt (state.session.directory.file (.run generation index)) = .ok .file) ∧
    (∀ generation index, generation < state.writer.installed.generation → generation ∉ seen.reports.held →
      seen.atBarrier.syncDirectory.DurablyAbsent (generation, index)) ∧
    (∀ generation index bytes, state.writer.installed.generation ≤ generation ∨ generation ∈ seen.reports.held →
      seen.initial.guaranteed generation index = some bytes →
      seen.atBarrier.syncDirectory.guaranteed generation index = some bytes) ∧
    SelectedIntegrityCheckpoint seen.atBarrier.syncDirectory.visible state.writer.target.pair.manifest state.writer.checkpoint ∧
    seen.next.Valid := by
  have sameNames (name : String) :
      name ∈ seen.reports.inventory.names ↔ name ∈ seen.lifetime.namespaceView.names seen.lifetime.root :=
    seen.toNativeObsoleteRunPass.toNativeObsoleteRunPlan.checkedNames.mem_iff
  have preserved := seen.toNativeObsoleteRunPass.preservesReady valid
  refine ⟨fun generation index => ?_, seen.toNativeObsoleteRunPass.settlesOldRuns valid, ?_,
    ?_, preserved.1⟩
  · rw [seen.reports.selected_eligible valid.retained, sameNames]
  · simpa only [seen.after_eq] using seen.toNativeObsoleteRunPass.retainsNamedBytes valid
  · have choices := preserved.2
    rw [seen.after_eq] at choices
    exact choices _ List.mem_cons_self

end NativeObsoleteRunCollection

/-- A healthy obsolete-run pass supplies the next ready position.
Only the reported run map changes. Its exact installed table and pins
continue to use the same committed WAL and recorded replay. -/
structure NativeObsoleteRunCollectionStep (current : NativeReadPosition history log)
    (seen : NativeObsoleteRunCollection current.state) (next : NativeReadPosition history log) : Prop where
  state : next.state = seen.next
  reads : next.reads = current.reads
  returned : seen.run = .ok () (next.state.session.phase,
    ⟨(next.state.cache, seen.atBarrier.syncDirectory), next.state.files.owners⟩)
  session : next.state.session = current.state.session
  installed : next.state.writer.installed = current.state.writer.installed
  files : next.state.files = current.state.files
  directory : next.state.directorySlot = current.state.directorySlot
  owner : next.state.owner = current.state.owner
  cache : next.state.cache = current.state.cache
  census : next.state.census = current.state.census
  durable : next.state.writer.published.durable = seen.atBarrier.syncDirectory.guaranteed
  settled : seen.atBarrier.syncDirectory.crashImages = [seen.atBarrier.syncDirectory.visible]
  selected : SelectedIntegrityCheckpoint seen.atBarrier.syncDirectory.visible current.state.writer.target.pair.manifest
    current.state.writer.checkpoint
  obsolete : ∀ generation index, generation < current.state.writer.installed.generation → generation ∉ seen.reports.held →
    seen.atBarrier.syncDirectory.DurablyAbsent (generation, index)
  retainedNames : ∀ generation index bytes,
    current.state.writer.installed.generation ≤ generation ∨ generation ∈ seen.reports.held →
    seen.initial.guaranteed generation index = some bytes →
    seen.atBarrier.syncDirectory.guaranteed generation index = some bytes
  replay : InstalledClientReplay log next.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.collectsObsoleteRuns (current : NativeReadPosition history log)
    (seen : NativeObsoleteRunCollection current.state) :
    ∃ next, NativeObsoleteRunCollectionStep current seen next := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨_, obsolete, retainedNames, selected, ready⟩ := seen.reclaims valid
  let state := seen.next
  let next : NativeReadPosition history log := ⟨.ok state.session (state.census, state.files), state, state, current.reads,
    .installed rfl ready sameHistory pending current.readPrefix.readsBounded⟩
  exact ⟨next, rfl, rfl, (seen.returns valid).2.1, rfl, rfl, rfl, rfl, rfl, rfl, seen.toNativeObsoleteRunPass.barrierCensus.2, congrArg RunUnlinkImage.guaranteed seen.after_eq,
    rfl, selected, obsolete, retainedNames, next.readPrefix.guardedReplay⟩

/-- The same collector reaches the final barrier and returns its
diagnostic. The reported error may follow the durability effect. -/
structure NativeObsoleteRunBarrierError (state : NativeReadyState) extends NativeObsoleteRunPass state where
  cause : IO.Error
  failed : outcome = .errorBeforeEffect cause ∨ outcome = .errorAfterEffect cause

def NativeObsoleteRunBarrierError.diagnostic {state : NativeReadyState} (seen : NativeObsoleteRunBarrierError state) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.path}': {seen.cause}"

theorem NativeObsoleteRunBarrierError.returns {state : NativeReadyState}
    (seen : NativeObsoleteRunBarrierError state) (valid : state.Valid) :
    seen.toNativeObsoleteRunPass.run =
      .error seen.diagnostic (state.session.phase, ⟨(state.cache, seen.toNativeObsoleteRunPass.after), state.files.owners⟩) := by
  have returned := (seen.toNativeObsoleteRunPass.returns valid).2.1
  rcases seen.failed with failed | failed <;>
    simpa only [failed, NativeObsoleteRunBarrierError.diagnostic, groupedResult, NativeObsoleteRunPass.next,
      NativeReadyState.files, SegmentedWriterState.afterRunCollection] using returned

end Alvoki.Storage.DiskSession
