import Alvoki.Storage.Disk.ObservedBootstrapCache
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev markerBytes := WAL.Boundary.encode 0

private def markerInput (before : WalSegmentRotation.State) : WalSegmentRotation.State :=
  ⟨before.metadata.syncDirectory, .durable⟩

private def markerNext (state : WalSegmentRotation.State) (step : Publication.Step) : WalSegmentRotation.State :=
  (bootstrapMarkerStep state step).getD state

private abbrev written (before : WalSegmentRotation.State) := markerNext (markerInput before) .writeStaged
private abbrev synced (before : WalSegmentRotation.State) := markerNext (written before) .syncStaged
private abbrev renamed (before : WalSegmentRotation.State) := markerNext (synced before) .renameStaged
private abbrev settled (before : WalSegmentRotation.State) := markerNext (renamed before) .syncDirectory

def bootstrapMarkerProjection : EStateM.Result IO.Error (Cache Handle × Files) Unit →
    EStateM.Result IO.Error WalSegmentRotation.State Unit
  | .ok () (_, image, _) => .ok () image
  | .error cause (_, image, _) => .error cause image

private theorem stagePath_ne_directory (directory : DiskDirectory) :
    directory.file .stagedWalBoundary ≠ directory.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ "WAL.commit.next").length = directory.path.toString.length at length
  simp only [String.length_append] at length
  have slash : "/".length = 1 := rfl
  omega

/-- Only a reported EEXIST makes the native stage detach a stale name
before it creates the fresh description. -/
inductive BootstrapMarkerStageOpen
    (tryCreate : FilePath → EStateM IO.Error Files (Except IO.Error Handle))
    (detach : FilePath → EStateM IO.Error Files Unit) (create : FilePath → EStateM IO.Error Files Handle)
    (path : FilePath) (initial : Files) (handle : Handle) (opened : Files) : Prop where
  | fresh (returned : tryCreate path initial = .ok (.ok handle) opened)
  | replaced {name message : String} {existing cleared : Files}
      (conflict : tryCreate path initial = .ok (.error (.alreadyExists name 17 message)) existing)
      (detached : detach path existing = .ok () cleared)
      (returned : create path cleared = .ok handle opened)

private theorem BootstrapMarkerStageOpen.uses {tryCreate detach create path initial handle opened}
    (opening : BootstrapMarkerStageOpen tryCreate detach create path initial handle opened)
    (use : Handle → EStateM IO.Error Files α) :
    withFreshStaging tryCreate detach create path use initial = use handle opened := by
  cases opening with
  | fresh returned => simp [withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, returned]
  | replaced conflict detached returned =>
    simp [withFreshStaging, Bind.bind, EStateM.bind, conflict, detached, returned]

/-- After the reported exclusive open and write, the staged writer
propagates a flush error on that same issued description. -/
theorem BootstrapMarkerStageOpen.flushError {tryCreate detach create path initial handle opened}
    (opening : BootstrapMarkerStageOpen tryCreate detach create path initial handle opened)
    {write : Handle → ByteArray → EStateM IO.Error Files Unit}
    {flush : Handle → EStateM IO.Error Files Unit} {bytes : ByteArray} {written reached : Files} {cause : IO.Error}
    (wrote : write handle bytes opened = .ok () written)
    (failed : flush handle written = .error cause reached) :
    writeFreshStagedWith tryCreate detach create write flush path bytes initial = .error cause reached := by
  unfold writeFreshStagedWith
  rw [opening.uses]
  simp only [Bind.bind, EStateM.bind, wrote, failed]

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

/-- Staging opens, writes, and flushes a fresh zero-marker inode after
segment zero has settled. Its pending handle supplies the file barrier. -/
structure BootstrapMarkerStaging (listed : BootstrapCheckedListing captured) where
  initial : WalInodeImage
  tryCreate : FilePath → EStateM IO.Error Files (Except IO.Error Handle)
  statStale : FilePath → EStateM IO.Error Files (Except IO.Error IO.FS.Metadata)
  unlinkStale : FilePath → EStateM IO.Error Files (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error Files Handle
  write : Handle → ByteArray → EStateM IO.Error Files Unit
  flush : Handle → EStateM IO.Error Files Unit
  read : FilePath → EStateM IO.Error Files Handle
  fsync : Handle → EStateM IO.Error Files Unit
  beforeStage : List LockReferenceDrop
  lockBeforeStage : calls.slot ∈ (listed.scan.afterClose.afterDrops beforeStage).slots
  directoryBeforeStage : captured.cached ∈ (listed.scan.afterClose.afterDrops beforeStage).slots
  slot : DescriptorSlot
  free : ∀ old ∈ (listed.scan.afterClose.afterDrops beforeStage).slots, old.address ≠ slot.address
  fresh : (listed.scan.afterClose.afterDrops beforeStage).references slot.description = []
  afterOpen : Files
  opening : BootstrapMarkerStageOpen tryCreate (removeStaleStagingWith statStale unlinkStale) create
    (directory.file .stagedWalBoundary) (markerInput before.image, initial)
    ((listed.scan.afterClose.afterDrops beforeStage).insert slot free, slot, 0) afterOpen
  afterWrite : Files
  writeReturned : write ((listed.scan.afterClose.afterDrops beforeStage).insert slot free, slot, 0)
    markerBytes afterOpen = .ok () afterWrite
  inodeState : WalInodeImage
  flushReturned : flush ((listed.scan.afterClose.afterDrops beforeStage).insert slot free, slot, 0) afterWrite =
    .ok () (written before.image, inodeState)
  stageView : DirectoryReadNamespace
  stageChild : RunChildLookup captured.root "WAL.commit.next" stageView
  stageObject : stageView.modelObject stageChild.child = (listed.scan.afterClose.afterDrops beforeStage).inode slot.description
  stageInode : inodeState.active = stageView.modelObject stageChild.child
  stageBytes : inodeState.visible inodeState.active = markerBytes
  beforeFile : List LockReferenceDrop
  fileLive : slot ∈ (((listed.scan.afterClose.afterDrops beforeStage).insert slot free).afterDrops beforeFile).slots
  projectWrite :
    calls.write captured.cache (directory.file .stagedWalBoundary) markerBytes (markerInput before.image) =
      bootstrapMarkerProjection (stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes
        (writeFreshStagedWith tryCreate (removeStaleStagingWith statStale unlinkStale) create write flush)
        (captured.cache, markerInput before.image, initial))
  projectFile :
    calls.sync captured.cache #[directory.file .stagedWalBoundary] (written before.image) =
      bootstrapMarkerProjection (SyncPathGroup.run (sync directory.path read fsync) #[directory.file .stagedWalBoundary]
        (captured.cache.remember (directory.file .stagedWalBoundary)
          ((listed.scan.afterClose.afterDrops beforeStage).insert slot free, slot, 0), written before.image, inodeState))

/-- A reported successful grouped barrier consumes the pending entry
and syncs exactly the staged marker's inode. -/
structure BootstrapMarkerSynced (listed : BootstrapCheckedListing captured) extends BootstrapMarkerStaging listed where
  fileSynced : fsync ((listed.scan.afterClose.afterDrops beforeStage).insert slot free, slot, 0)
    (written before.image, inodeState) = .ok () (synced before.image, inodeState.completeFileSync inodeState.active)

/-- The observed rename publishes the synced staged inode under the
canonical marker name. -/
structure BootstrapMarkerRenamed (listed : BootstrapCheckedListing captured) extends BootstrapMarkerSynced listed where
  rename : FilePath → FilePath → EStateM IO.Error Files Unit
  renamedView : DirectoryReadNamespace
  liveChild : RunChildLookup captured.root "WAL.commit" renamedView
  sameChild : liveChild.child = stageChild.child
  stageGone : renamedView.child captured.root "WAL.commit.next" = none
  renameReturned : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
    (synced before.image, inodeState.completeFileSync inodeState.active) =
    .ok () (renamed before.image, inodeState.completeFileSync inodeState.active)
  afterFile : List LockReferenceDrop
  lockLive : calls.slot ∈ (((listed.scan.afterClose.afterDrops beforeStage).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  directoryLive : captured.cached ∈ (((listed.scan.afterClose.afterDrops beforeStage).insert slot free).afterDrops
    (beforeFile ++ afterFile)).slots
  projectRename :
    calls.renameFile (directory.file .stagedWalBoundary) (directory.file .walBoundary) (synced before.image) =
      bootstrapMarkerProjection (withCache (captured.cache.consume (directory.file .stagedWalBoundary))
        (rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
          (synced before.image, inodeState.completeFileSync inodeState.active)))
  projectDirectory :
    calls.sync captured.cache #[directory.path] (renamed before.image) =
      bootstrapMarkerProjection (SyncPathGroup.run (sync directory.path read fsync) #[directory.path]
        (captured.cache.consume (directory.file .stagedWalBoundary), renamed before.image,
          inodeState.completeFileSync inodeState.active))

/-- Successful publication includes the final barrier on the captured
directory and settles the renamed marker. -/
structure BootstrapMarkerCustody (listed : BootstrapCheckedListing captured) extends BootstrapMarkerRenamed listed where
  directorySynced : fsync (captured.reached, captured.cached, 0)
    (renamed before.image, inodeState.completeFileSync inodeState.active) =
    .ok () (settled before.image, (inodeState.completeFileSync inodeState.active).settleBinding)

variable {listed : BootstrapCheckedListing captured}

namespace BootstrapMarkerStaging

abbrev inputState (_ : BootstrapMarkerStaging listed) : WalSegmentRotation.State :=
  markerInput before.image

abbrev writtenState (_ : BootstrapMarkerStaging listed) : WalSegmentRotation.State :=
  written before.image

abbrev syncedState (_ : BootstrapMarkerStaging listed) : WalSegmentRotation.State :=
  synced before.image

abbrev inventory (observed : BootstrapMarkerStaging listed) : DescriptorInventory :=
  (listed.scan.afterClose.afterDrops observed.beforeStage).insert observed.slot observed.free

abbrev handle (observed : BootstrapMarkerStaging listed) : Handle :=
  (observed.inventory, observed.slot, 0)

noncomputable abbrev stage (observed : BootstrapMarkerStaging listed) :=
  writeFreshStagedWith observed.tryCreate (removeStaleStagingWith observed.statStale observed.unlinkStale)
    observed.create observed.write observed.flush

abbrev grouped (observed : BootstrapMarkerStaging listed) :=
  SyncPathGroup.run (sync directory.path observed.read observed.fsync)

theorem stageReturns (observed : BootstrapMarkerStaging listed) :
    observed.stage (directory.file .stagedWalBoundary) markerBytes (observed.inputState, observed.initial) =
      .ok observed.handle (observed.writtenState, observed.inodeState) := by
  unfold stage writeFreshStagedWith
  rw [observed.opening.uses]
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, observed.writeReturned, observed.flushReturned]

theorem staged (observed : BootstrapMarkerStaging listed) :
    let path := directory.file .stagedWalBoundary
    stageFreshWithCache path markerBytes observed.stage (captured.cache, observed.inputState, observed.initial) =
      .ok () (captured.cache.remember path observed.handle, observed.writtenState, observed.inodeState) := by
  intro path
  have wrote : observed.stage path markerBytes (observed.inputState, observed.initial) =
      .ok observed.handle (observed.writtenState, observed.inodeState) := observed.stageReturns
  simp [stageFreshWithCache, wrote]

theorem writeProjected (observed : BootstrapMarkerStaging listed) :
    calls.write captured.cache (directory.file .stagedWalBoundary) markerBytes observed.inputState =
      .ok () observed.writtenState :=
  observed.projectWrite.trans (congrArg bootstrapMarkerProjection observed.staged)

theorem syncPending (observed : BootstrapMarkerStaging listed) :
    let path := directory.file .stagedWalBoundary
    observed.grouped #[path] (captured.cache.remember path observed.handle, observed.writtenState, observed.inodeState) =
      match observed.fsync observed.handle (observed.writtenState, observed.inodeState) with
      | .ok () after => .ok () (captured.cache.consume path, after)
      | .error cause after => .error (IO.userError s!"sync failed for '{path}': {cause}") (captured.cache.consume path, after) := by
  intro path
  change SyncPathGroup.run (sync directory.path observed.read observed.fsync) #[path]
    (captured.cache.remember path observed.handle, observed.writtenState, observed.inodeState) = _
  rw [SyncPathGroup.run_single, syncRemembered (stagePath_ne_directory directory)]
  cases observed.fsync observed.handle (observed.writtenState, observed.inodeState) <;> rfl

end BootstrapMarkerStaging

namespace BootstrapMarkerSynced

abbrev renamedState (_ : BootstrapMarkerSynced listed) : WalSegmentRotation.State :=
  renamed before.image

abbrev inodeSynced (observed : BootstrapMarkerSynced listed) : WalInodeImage :=
  observed.inodeState.completeFileSync observed.inodeState.active

theorem fileCallback (observed : BootstrapMarkerSynced listed) :
    let path := directory.file .stagedWalBoundary
    observed.grouped #[path]
      (captured.cache.remember path observed.toBootstrapMarkerStaging.handle, observed.toBootstrapMarkerStaging.writtenState, observed.inodeState) =
      .ok () (captured.cache.consume path, observed.toBootstrapMarkerStaging.syncedState, observed.inodeSynced) := by
  simpa only [observed.fileSynced] using observed.toBootstrapMarkerStaging.syncPending

theorem fileProjected (observed : BootstrapMarkerSynced listed) :
    calls.sync captured.cache #[directory.file .stagedWalBoundary] observed.toBootstrapMarkerStaging.writtenState =
      .ok () observed.toBootstrapMarkerStaging.syncedState :=
  observed.projectFile.trans (congrArg bootstrapMarkerProjection observed.fileCallback)

end BootstrapMarkerSynced

namespace BootstrapMarkerRenamed

abbrev publishedState (_ : BootstrapMarkerRenamed listed) : WalSegmentRotation.State := settled before.image

theorem renameProjected (observed : BootstrapMarkerRenamed listed) :
    calls.renameFile (directory.file .stagedWalBoundary) (directory.file .walBoundary)
      observed.toBootstrapMarkerStaging.syncedState = .ok () observed.toBootstrapMarkerSynced.renamedState := by
  rw [observed.projectRename, observed.renameReturned]
  rfl

/-- The singleton final barrier uses the original cached descriptor. The
native grouping adds the directory path to a returned error. -/
theorem directoryCallback (observed : BootstrapMarkerRenamed listed) :
    let consumed := captured.cache.consume (directory.file .stagedWalBoundary)
    let input := (observed.toBootstrapMarkerSynced.renamedState, observed.toBootstrapMarkerSynced.inodeSynced)
    observed.grouped #[directory.path] (consumed, input) =
      match observed.fsync (captured.reached, captured.cached, 0) input with
      | .ok () after => .ok () (consumed, after)
      | .error cause after => .error (IO.userError s!"sync failed for '{directory.path}': {cause}") (consumed, after) := by
  intro consumed input
  change SyncPathGroup.run (sync directory.path observed.read observed.fsync) #[directory.path] (consumed, input) = _
  rw [SyncPathGroup.run_single]
  have cache : consumed.directory = some (captured.reached, captured.cached, 0) := rfl
  cases result : observed.fsync (captured.reached, captured.cached, 0) input <;>
    simp [sync, Cache.resolve, cache, withCache, result] <;> rfl

end BootstrapMarkerRenamed

namespace BootstrapMarkerCustody

abbrev publishedState (observed : BootstrapMarkerCustody listed) : WalSegmentRotation.State :=
  observed.toBootstrapMarkerRenamed.publishedState

/-- The stage remembers its actual returned slot. The file sync consumes
that entry and the final sync uses the captured directory description. -/
theorem callbacks (observed : BootstrapMarkerCustody listed) :
    let path := directory.file .stagedWalBoundary
    let handle : Handle := ((listed.scan.afterClose.afterDrops observed.beforeStage).insert observed.slot observed.free,
      observed.slot, 0)
    let stage := writeFreshStagedWith observed.tryCreate
      (removeStaleStagingWith observed.statStale observed.unlinkStale) observed.create observed.write observed.flush
    let grouped := SyncPathGroup.run (sync directory.path observed.read observed.fsync)
    let consumed := captured.cache.consume path
    let durable := observed.inodeState.completeFileSync observed.inodeState.active
    stageFreshWithCache path markerBytes stage (captured.cache, markerInput before.image, observed.initial) =
      .ok () (captured.cache.remember path handle, written before.image, observed.inodeState) ∧
    grouped #[path] (captured.cache.remember path handle, written before.image, observed.inodeState) =
      .ok () (consumed, synced before.image, durable) ∧
    grouped #[directory.path] (consumed, renamed before.image, durable) =
      .ok () (consumed, settled before.image, durable.settleBinding) := by
  intro path handle stage grouped consumed durable
  refine ⟨?_, ?_, ?_⟩
  · exact observed.toBootstrapMarkerStaging.staged
  · exact observed.toBootstrapMarkerSynced.fileCallback
  · simpa only [observed.directorySynced] using observed.toBootstrapMarkerRenamed.directoryCallback

/-- The staged and published children resolve to the same native inode.
Only its synced zero marker bytes survive the reported final effect. -/
theorem settledInode (observed : BootstrapMarkerCustody listed) :
    let inventory := (listed.scan.afterClose.afterDrops observed.beforeStage).insert observed.slot observed.free
    let durable := (observed.inodeState.completeFileSync observed.inodeState.active).settleBinding
    observed.slot ∈ (inventory.afterDrops observed.beforeFile).slots ∧
    calls.slot ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    captured.cached ∈ (inventory.afterDrops (observed.beforeFile ++ observed.afterFile)).slots ∧
    observed.slot.description ≠ calls.slot.description ∧ observed.slot.description ≠ captured.cached.description ∧
    observed.stageView.child captured.root "WAL.commit.next" = some observed.stageChild.child ∧
    observed.renamedView.child captured.root "WAL.commit" = some observed.stageChild.child ∧
    observed.renamedView.child captured.root "WAL.commit.next" = none ∧
    observed.inodeState.active = inventory.inode observed.slot.description ∧
    durable.crashBindings = [observed.inodeState.active] ∧
    durable.crashBytes observed.inodeState.active = [markerBytes] := by
  intro inventory durable
  have staged := observed.stageChild.binds
  rw [observed.stageChild.atRoot, observed.stageChild.atName] at staged
  have live := observed.liveChild.binds
  rw [observed.liveChild.atRoot, observed.liveChild.atName, observed.sameChild] at live
  have freshDescription (old : DescriptorSlot)
      (present : old ∈ (listed.scan.afterClose.afterDrops observed.beforeStage).slots) :
      observed.slot.description ≠ old.description := by
    intro alias
    have used := (listed.scan.afterClose.afterDrops observed.beforeStage).mem_references.mpr
      ⟨old, present, rfl, alias.symm⟩
    rw [observed.fresh] at used
    exact List.not_mem_nil used
  refine ⟨observed.fileLive, observed.lockLive, observed.directoryLive,
    freshDescription calls.slot observed.lockBeforeStage, freshDescription captured.cached observed.directoryBeforeStage,
    staged, live, observed.stageGone, observed.stageInode.trans observed.stageObject, rfl, ?_⟩
  simp [durable, WalInodeImage.settleBinding, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, observed.stageBytes]

/-- The projected primitive returns supply the marker contract for the
ordered native replacement schedule. No result of the whole worker is
assumed. -/
theorem markerHealthy (observed : BootstrapMarkerCustody listed) : calls.MarkerHealthy captured.cache := by
  obtain ⟨rawWrite, rawFile, rawDirectory⟩ := observed.callbacks
  have write := observed.projectWrite
  have file := observed.projectFile
  have rename := observed.projectRename
  have directorySync := observed.projectDirectory
  rw [rawWrite] at write
  rw [rawFile] at file
  rw [observed.renameReturned] at rename
  rw [rawDirectory] at directorySync
  have staged : bootstrapMarkerStep (markerInput before.image) .writeStaged = some (written before.image) := rfl
  have syncedFile : bootstrapMarkerStep (written before.image) .syncStaged = some (synced before.image) := rfl
  have published : bootstrapMarkerStep (synced before.image) .renameStaged = some (renamed before.image) := rfl
  have finished : bootstrapMarkerStep (renamed before.image) .syncDirectory = some (settled before.image) := rfl
  intro done step todo prior next order
  show done.foldlM bootstrapMarkerStep (markerInput before.image) = some prior → _
  intro reached effect
  change done.foldlM bootstrapMarkerStep (markerInput before.image) = some prior at reached
  unfold Publication.steps at order
  rcases done with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, rest⟩⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, _⟩ := order
    cases reached
    rw [staged] at effect
    cases effect
    exact write
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, rfl, _⟩ := order
    simp [List.foldlM_cons, staged, Bind.bind, Option.bind] at reached
    cases reached
    rw [syncedFile] at effect
    cases effect
    exact file
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, rfl, rfl, _⟩ := order
    simp [List.foldlM_cons, staged, syncedFile, Bind.bind, Option.bind] at reached
    cases reached
    rw [published] at effect
    cases effect
    exact rename
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at order
    obtain ⟨rfl, rfl, rfl, rfl, _⟩ := order
    simp [List.foldlM_cons, staged, syncedFile, published, Bind.bind, Option.bind] at reached
    cases reached
    rw [finished] at effect
    cases effect
    exact directorySync
  · simp at order

/-- The admitted ready result carries exactly the image produced by the
reported marker callbacks. Allocation of session references leaves it intact. -/
theorem publishedImage {input : FilePath} (observed : BootstrapMarkerCustody listed)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (rotation : calls.RotationHealthy captured.cache) {session : SegmentedSession}
    {after : LockedFileState WalSegmentRotation.State}
    (returned : calls.run admission = .ok session after) : after.image = observed.publishedState := by
  have complete := (bootstrapEmptyWith_completesAt directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    rotation observed.markerHealthy observed.publishedState rfl).1
  rw [calls.runMarkerless admission captured.captures.1, runOpenWithInstallation_outcome, runOpenWithImage_acquired,
    calls.reachesPublication captured.cache listed.entries.1 listed.entries.2, complete] at returned
  exact congrArg LockedFileState.image (EStateM.Result.ok.inj returned).2.symm

/-- The captured marker publication extends either healthy zero-segment
route and installs the exact empty writer through the admitted opener. -/
theorem installs {input : FilePath} (observed : BootstrapMarkerCustody listed)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (rotation : calls.RotationHealthy captured.cache) (allowCollection : Bool) :
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      calls.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer :=
  (SegmentedBatchDatabaseTrace.fromBootstrapWithCapturedCache captured listed admission valid
    rotation observed.markerHealthy allowCollection).2.2.2

end BootstrapMarkerCustody

end Alvoki.Storage.DiskSession
