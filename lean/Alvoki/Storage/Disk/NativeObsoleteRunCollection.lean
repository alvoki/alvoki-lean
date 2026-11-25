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

/-- One successful pass from the reached ready writer. The checked
listing and no-follow probes enumerate the older unheld run names.
The final barrier uses the cached directory handle, after the ordered
canonical unlinks have returned. -/
structure NativeObsoleteRunCollection (state : NativeReadyState) where
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
  complete : ∀ generation index bytes, initial.visible generation index = some bytes →
    generation < state.writer.installed.generation → generation ∉ reports.held →
    renderRunFileName generation index ∈ lifetime.namespaceView.names lifetime.root ∧
      reports.inventory.kindAt (state.session.directory.file (.run generation index)) = .ok .file
  atBarrier : RunUnlinkImage
  unlinked : ((reports.selected.map RunCollection.Step.unlink).forM reports.perform) initial = .ok () atBarrier
  capture : DescriptorInventory
  cached : state.cache.directory = some (capture, state.directorySlot, 0)
  capturedInode : capture.inode state.directorySlot.description = state.census.inode state.directorySlot.description
  pathObject : FilePath → Option DeviceInode
  atPath : pathObject state.session.directory.path = some lifetime.root
  atLock : pathObject (state.session.directory.file .lock) = some lifetime.lock
  openRead : FilePath → EStateM IO.Error RunUnlinkImage CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM IO.Error RunUnlinkImage Unit
  synced : fsync (capture, state.directorySlot, 0) atBarrier = .ok () atBarrier.syncDirectory
  syncProjection : reports.syncDirectory state.session.directory.path atBarrier =
    match SyncPathGroup.run (sync state.session.directory.path openRead fsync)
      #[state.session.directory.path] (state.cache, atBarrier) with
    | .ok value (_, reached) => .ok value reached
    | .error cause (_, reached) => .error cause reached

namespace NativeObsoleteRunCollection

variable {state : NativeReadyState}

theorem checkedNames (seen : NativeObsoleteRunCollection state) :
    seen.reports.inventory.names.Perm (seen.lifetime.namespaceView.names seen.lifetime.root) := by
  obtain ⟨returned, names⟩ := CheckedDirectoryReadReport.scan_complete state.session.directory.path
    seen.listing.eof seen.listing.closed seen.listing.complete
  have listed := Except.ok.inj (seen.reports.listed.symm.trans (seen.listCallback.trans returned))
  rw [← seen.reports.names, listed]
  simpa only [seen.listing.sameRoot] using names

theorem preservesCensus (seen : NativeObsoleteRunCollection state) : seen.listing.afterClose = state.census := by
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

private theorem selectsFromLstat (seen : NativeObsoleteRunCollection state) :
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
def plan (seen : NativeObsoleteRunCollection state) : Except IO.Error (List RunAddress) := do
  let installed ← state.session.phase.installed
  let manifest ← seen.reports.manifest.result (state.session.directory.file .manifest)
  let current ← (validateIntegrityRunCollectionGeneration installed.generation manifest).mapError IO.userError
  let entries ← seen.reports.list state.session.directory.path
  selectRunFilesWith state.session.directory current (retainRunGeneration installed.generation seen.reports.held)
    (runKindAt seen.stat) (entries.toList.map (·.fileName))

theorem plans (seen : NativeObsoleteRunCollection state) (valid : state.Valid) :
    seen.plan = .ok seen.reports.selected := by
  simp only [plan, valid.phase, Phase.installed, Pure.pure, Except.pure, Bind.bind, Except.bind,
    seen.reports.manifestRead, seen.reports.preflight valid.retained, Except.mapError, seen.reports.listed,
    seen.reports.names]
  exact seen.selectsFromLstat

/-- The last scheduled callback resolves the original cached directory
handle and settles the same namespace reached by the preceding unlinks. -/
theorem syncs (seen : NativeObsoleteRunCollection state) :
    SyncPathGroup.run (sync state.session.directory.path seen.openRead seen.fsync)
      #[state.session.directory.path] (state.cache, seen.atBarrier) =
        .ok () (state.cache, seen.atBarrier.syncDirectory) := by
  rw [SyncPathGroup.run_single]
  simp [SyncHandleRouting.sync, Cache.resolve, seen.cached, seen.synced, withCache]

def run (seen : NativeObsoleteRunCollection state) :
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

def next (seen : NativeObsoleteRunCollection state) : NativeReadyState :=
  { state with writer := state.writer.afterRunCollection seen.atBarrier.syncDirectory.guaranteed }

theorem returns (seen : NativeObsoleteRunCollection state) (valid : state.Valid) :
    seen.reports.run = .ok () seen.atBarrier.syncDirectory ∧
    seen.run = .ok () (seen.next.session.phase,
      ⟨(seen.next.cache, seen.atBarrier.syncDirectory), seen.next.files.owners⟩) ∧
    seen.atBarrier.syncDirectory = seen.initial.finishPass seen.reports.selected := by
  obtain ⟨atBarrier, exactImage⟩ := runUnlinkSchedule_reachesBarrier seen.reports.selected
    seen.reports.perform seen.reports.effects seen.unlinked
  have synced : seen.reports.perform .syncDirectory seen.atBarrier = .ok () seen.atBarrier.syncDirectory := by
    rw [SegmentedRunCollectionReports.perform, RunCollection.performPaths, seen.syncProjection, seen.syncs]
  have completed := atBarrier.trans synced
  refine ⟨(seen.reports.run_eq_schedule valid.retained).trans completed, ?_, exactImage⟩
  simp only [run, seen.plans valid, completed]
  rfl

/-- The reached stream is closed before the final callback. Its cached
directory object and held lock survive, and the exact original slots
are available when the barrier is issued. -/
theorem custody (seen : NativeObsoleteRunCollection state) (valid : state.Valid) :
    seen.listing.Custody ∧ seen.listing.afterClose = state.census ∧
    state.directorySlot ∈ seen.listing.afterClose.slots ∧ state.owner ∈ seen.listing.afterClose.slots ∧
    seen.pathObject state.session.directory.path = some seen.lifetime.root ∧
    seen.lifetime.namespaceView.modelObject seen.lifetime.root = seen.capture.inode state.directorySlot.description ∧
    seen.pathObject (state.session.directory.file .lock) = some seen.lifetime.lock ∧
    seen.lifetime.namespaceView.modelObject seen.lifetime.lock = seen.listing.afterClose.inode state.owner.description := by
  have census := seen.preservesCensus
  refine ⟨seen.listing.custody, census, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    seen.atPath, ?_, seen.atLock, census.symm ▸ seen.lifetime.identifiesLock⟩
  rw [seen.capturedInode, ← seen.cachedSlot]
  exact seen.lifetime.identifiesDirectory

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
    seen.checkedNames.mem_iff
  obtain ⟨returned, _, exactImage⟩ := seen.returns valid
  have reached : seen.reports.reached = seen.atBarrier.syncDirectory := by
    simp only [SegmentedRunCollectionReports.reached, returned]
  have preserved := seen.reports.preservesRetained valid.retained
  have retry := seen.reports.extendsRetry valid.retained (.start seen.initial) (fun _ member => member)
  rw [reached] at preserved retry
  have checked := (validateObservedRunGeneration_ok_iff.mp (seen.reports.preflight valid.retained)).2
  refine ⟨fun generation index => ?_, ?_, ?_, preserved.2 _ List.mem_cons_self,
    { valid with retained := preserved.1 }⟩
  · rw [seen.reports.selected_eligible valid.retained, sameNames]
  · rw [exactImage]
    exact seen.reports.inventory.finishOlderPass_absent seen.initial seen.reports.held checked
      (fun generation index bytes present older unheld =>
        let known := seen.complete generation index bytes present older unheld
        ⟨(sameNames _).mpr known.1, known.2⟩)
  · intro generation index bytes keep original
    apply retry.keepsKnown (name := (generation, index)) original
    intro selected
    have eligible := (seen.reports.selected_eligible valid.retained).mp selected
    exact keep.elim (fun current => UInt64.not_lt.mpr current eligible.2.1) eligible.2.2.1

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
  exact ⟨next, rfl, rfl, (seen.returns valid).2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, selected, obsolete, retainedNames, next.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
