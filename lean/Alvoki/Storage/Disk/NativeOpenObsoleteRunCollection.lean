import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeOpenClose
import Alvoki.Storage.Disk.NativeFileEffectProjection

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting CheckpointPublication

private def collectObsoleteRunsWith [Monad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (held : List UInt64) (load : m Installed)
    (readManifest : FilePath → m (Option ByteArray)) (check : Except String (Option UInt64) → m (Option UInt64))
    (list : FilePath → m (Array IO.FS.DirEntry))
    (kind : FilePath → m (Except String IO.FS.FileType))
    (remove : FilePath → m (Except IO.Error Unit)) (sync : FilePath → m Unit) : m Unit := do
  let installed ← load
  let manifest ← readManifest (directory.file .manifest)
  let generation ← check (validateIntegrityRunCollectionGeneration installed.generation manifest)
  let entries ← list directory.path
  let selected ← selectRunFilesWith directory generation (retainRunGeneration installed.generation held)
    kind (entries.toList.map (·.fileName))
  RunCollection.run selected (RunCollection.performPaths remove sync throw
    (fun address => directory.file (.run address.1 address.2)) directory.path)

/-- The original table supplies both the phase getter and the cache cells
for the final singleton directory sync. The caller's holds reach the
selector unchanged. -/
def UsesObsoleteRunCollectionSchedule (db : DiskTable) (directory : DiskDirectory)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (held : List UInt64) : Prop :=
  ∃ (list : FilePath → IO (Array IO.FS.DirEntry)) (fsync : IO.FS.Handle → IO Unit),
    db.collectObsoleteRuns held = collectObsoleteRunsWith (m := IO) directory held (do (← phase.get).installed)
      (fun path => readOptionalDatabaseFile path.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile path)
        (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw)
      IO.ofExcept list
      (fun path => do
        match ← path.symlinkMetadata.toBaseIO with
        | .ok metadata => return .ok metadata.type
        | .error (.noFileOrDirectory _ 2 _) => return .error "run file is absent"
        | .error cause => throw cause)
      (fun path => (IO.FS.removeFile path).toBaseIO)
      (fun path => SyncPathGroup.run (fun name =>
        syncWithHandles directory.path name cachedDirectory.get pending.get pending.set active.get
          (fun path => IO.FS.Handle.mk path .read) fsync) #[path])

private theorem obsoleteRunCollectionSchedule {db : DiskTable}
    {directory lock files phase token active pending cachedDirectory}
    (uses : db.UsesOpenReferences directory lock files phase token)
    (references : files.UsesCacheReferences active pending cachedDirectory)
    (cachePath : files.AtDirectory directory.path) (held : List UInt64) :
    UsesObsoleteRunCollectionSchedule db directory phase active pending cachedDirectory held := by
  obtain ⟨rfl, _, rfl, rfl, _⟩ := uses
  obtain ⟨rfl, rfl, rfl⟩ := references
  unfold DiskTable.OpenSyncFiles.AtDirectory at cachePath
  refine ⟨_, _, by
    simp only [db.collectObsoleteRuns_fileEffects, collectObsoleteRunsWith, syncFilesSyncPaths_schedule, cachePath]
    rfl⟩

/-- Callback results on the reached heap, using the production selector
and unlink dispatcher. -/
structure OpenObsoleteRunCallbacks (heap : Type) where
  manifest : FilePath → EStateM IO.Error heap (Option ByteArray)
  list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)
  stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  readDirectory : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  readPending : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  setPending : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  readActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  fsync : IO.FS.Handle → EStateM IO.Error heap Unit

def OpenObsoleteRunCallbacks.sync (calls : OpenObsoleteRunCallbacks heap) (directory : DiskDirectory)
    (cacheDirectory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun name => syncWithHandles directory.path name (calls.readDirectory cacheDirectory)
    (calls.readPending pending) (calls.setPending pending) (calls.readActive active) calls.openRead calls.fsync) #[path]

def OpenObsoleteRunCallbacks.kind (calls : OpenObsoleteRunCallbacks heap) (path : FilePath) :
    EStateM IO.Error heap (Except String IO.FS.FileType) := do
  let result ← calls.stat path
  liftExcept (runKindAt (fun _ => result) path)

def OpenObsoleteRunCallbacks.run (calls : OpenObsoleteRunCallbacks heap)
    (opened : NativeOpenedHandle heap) (held : List UInt64) (cacheDirectory : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle))) (pending : IO.Ref (List (FilePath × IO.FS.Handle))) :
    EStateM IO.Error heap Unit :=
  collectObsoleteRunsWith opened.directory held (do (← opened.get opened.phase).installed)
    calls.manifest (liftExcept ∘ Except.mapError IO.userError) calls.list calls.kind calls.remove
    (calls.sync opened.directory cacheDirectory active pending)

/-- The table's projected phase, raw cache entries and resolved handles,
cached directory and lock identities, census and held writer remain
fixed while the collector mutates only its run namespace projection. -/
structure OpenObsoleteRunFrame where
  phase : Option (Phase Installed)
  active : Option (FilePath × IO.FS.Handle)
  pending : List (FilePath × IO.FS.Handle)
  directory : Option IO.FS.Handle
  cache : CensusDirectoryCache
  census : DescriptorInventory
  owner : DescriptorSlot
  owners : LockOwners

def OpenCloseHeapView.obsoleteRunFrame (view : OpenCloseHeapView heap RunUnlinkImage)
    (opened : NativeOpenedHandle heap) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle))
    (reached : heap) : OpenObsoleteRunFrame :=
  ⟨opened.contents reached opened.phase,
    view.active reached active, view.pending reached pending, view.directory reached directory,
    view.cacheAt reached directory active pending, view.descriptors reached,
    (view.handle reached opened.lock).2.1, (view.files reached).owners⟩

structure OpenObsoleteRunObservation {heap : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened) (held : List UInt64)
    (pass : NativeObsoleteRunPass current.current.ready.state) where
  view : OpenCloseHeapView heap RunUnlinkImage
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  directory : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences active pending directory
  cachePath : opened.files.AtDirectory opened.directory.path
  calls : OpenObsoleteRunCallbacks heap
  holds : pass.reports.held = held
  initial : (view.files current.reached).image = pass.initial
  cache : view.cacheAt current.reached directory active pending = current.current.ready.state.cache
  census : view.descriptors current.reached = current.current.ready.state.census
  owner : (view.handle current.reached opened.lock).2.1 = current.current.ready.state.owner
  locked : (view.files current.reached).owners = current.current.ready.state.files.owners
  manifest : ∀ path, NativeFileEffectProjection (fun reached => (view.files reached).image)
    (view.obsoleteRunFrame opened active pending directory) (calls.manifest path) (liftExcept (pass.reports.manifest.result path))
  listed : ∀ path, NativeFileEffectProjection (fun reached => (view.files reached).image)
    (view.obsoleteRunFrame opened active pending directory) (calls.list path) (liftExcept (pass.reports.list path))
  stat : ∀ path, NativeFileEffectProjection (fun reached => (view.files reached).image)
    (view.obsoleteRunFrame opened active pending directory) (calls.stat path) (pure (pass.stat path))
  removes : ∀ path, NativeFileEffectProjection (fun reached => (view.files reached).image)
    (view.obsoleteRunFrame opened active pending directory) (calls.remove path) (pass.reports.removeFile path)
  readsDirectory : ∀ reached,
    calls.readDirectory directory reached = .ok (view.directory reached directory) reached
  syncs : ∀ reached file,
    view.directory reached directory = some file →
    NativeFileEffectProjection.result (fun after => (view.descriptors after, (view.files after).image))
      (calls.fsync file reached) =
      pass.fsync (view.handle reached file) (view.descriptors reached, (view.files reached).image) ∧
    view.obsoleteRunFrame opened active pending directory (NativeFileEffectProjection.reached (calls.fsync file reached)) =
      view.obsoleteRunFrame opened active pending directory reached

private theorem projectsUnlinkPrefix {heap frame : Type} {project : heap → RunUnlinkImage} {retain : heap → frame}
    (directory : DiskDirectory) (selected : List RunAddress)
    (rawRemove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (rawSync : FilePath → EStateM IO.Error heap Unit)
    (remove : FilePath → EStateM IO.Error RunUnlinkImage (Except IO.Error Unit))
    (sync : FilePath → EStateM IO.Error RunUnlinkImage Unit)
    (removes : ∀ path, NativeFileEffectProjection project retain (rawRemove path) (remove path)) :
    NativeFileEffectProjection project retain
      ((selected.map RunCollection.Step.unlink).forM (RunCollection.performPaths rawRemove rawSync throw
        (fun address => directory.file (.run address.1 address.2)) directory.path))
      ((selected.map RunCollection.Step.unlink).forM (RunCollection.performPaths remove sync throw
        (fun address => directory.file (.run address.1 address.2)) directory.path)) := by
  apply NativeFileEffectProjection.forM
  intro step member
  obtain ⟨address, _, rfl⟩ := List.mem_map.mp member
  apply NativeFileEffectProjection.bind (removes _)
  intro result
  cases RunCollection.ownedUnlinkResult result with
  | ok value => cases value; exact NativeFileEffectProjection.pure _ _ _
  | error cause => exact NativeFileEffectProjection.failure _ _ cause

private theorem projectsKind {heap frame files : Type} {project : heap → files} {retain : heap → frame}
    (calls : OpenObsoleteRunCallbacks heap) (stat : FilePath → Except IO.Error IO.FS.Metadata) {path : FilePath}
    (reported : NativeFileEffectProjection project retain (calls.stat path) (pure (stat path))) :
    NativeFileEffectProjection project retain (calls.kind path) (liftExcept (runKindAt stat path)) := by
  change NativeFileEffectProjection project retain
    (calls.stat path >>= fun result => liftExcept (runKindAt (fun _ => result) path))
    (pure (stat path) >>= fun result => liftExcept (runKindAt (fun _ => result) path))
  apply NativeFileEffectProjection.bind reported
  intro result
  cases runKindAt (fun _ => result) path with
  | ok value => exact NativeFileEffectProjection.pure _ _ _
  | error cause => exact NativeFileEffectProjection.failure _ _ _

variable {heap : Type} {opened : NativeOpenedHandle heap} {start : NativeOpenedPosition opened}
  {held : List UInt64} {pass : NativeObsoleteRunPass start.current.ready.state}

private theorem OpenObsoleteRunObservation.projectsSelector (seen : OpenObsoleteRunObservation start held pass) :
    let installed := start.current.ready.state.writer.installed
    let current := pass.reports.observed.map fun _ => installed.generation
    NativeFileEffectProjection (fun reached => (seen.view.files reached).image)
      (seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory)
      (selectRunFilesWith opened.directory current (retainRunGeneration installed.generation held)
        seen.calls.kind pass.reports.inventory.names)
      (pure pass.reports.selected) := by
  dsimp only
  rw [← congrArg (retainRunGeneration start.current.ready.state.writer.installed.generation) seen.holds,
    ← start.directory, SegmentedRunCollectionReports.selected, ← selectRunFilesWith_pure]
  unfold selectRunFilesWith
  apply NativeFileEffectProjection.filterMapM
  intro name listed
  unfold selectRunFileWith
  cases parsed : parseRunFileName name with
  | none => exact NativeFileEffectProjection.pure _ _ _
  | some address =>
    obtain ⟨generation, index⟩ := address
    dsimp only
    split
    · rename_i eligible
      obtain ⟨older, unheld⟩ := retainRunGeneration_false_iff.mp eligible.2
      rw [parseRunFileName_sound parsed] at listed
      apply NativeFileEffectProjection.bind
      · have probe := projectsKind seen.calls pass.stat
          (seen.stat (start.current.ready.state.session.directory.file (.run generation index)))
        rw [pass.kind generation index listed older unheld] at probe
        exact probe
      · intro _
        exact NativeFileEffectProjection.pure _ _ _
    · exact NativeFileEffectProjection.pure _ _ _

/-- The singleton group reads the original directory reference and syncs
the exact corresponding raw handle from the reached unlink prefix. -/
def OpenObsoleteRunObservation.Barrier (seen : OpenObsoleteRunObservation start held pass)
    (issued reached : heap) : Prop :=
  ∃ file : IO.FS.Handle,
    seen.calls.readDirectory seen.directory issued = .ok (some file) issued ∧
    seen.view.handle issued file = (pass.capture, start.current.ready.state.directorySlot, 0) ∧
    seen.view.descriptors issued = pass.issueCensus ∧
    (seen.view.files issued).image = pass.atBarrier ∧
    seen.calls.fsync file issued = pass.fsyncResult reached

private theorem OpenObsoleteRunObservation.syncsReached (seen : OpenObsoleteRunObservation start held pass)
    (issued : heap) (atBarrier : (seen.view.files issued).image = pass.atBarrier)
    (kept : seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory issued =
      seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory start.reached) :
    ∃ reached,
      seen.calls.sync opened.directory seen.directory seen.active seen.pending opened.directory.path issued =
        pass.collectorResult reached ∧ seen.Barrier issued reached ∧ (seen.view.files reached).image = pass.after ∧
      seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory reached =
        seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory issued := by
  have cache := (congrArg OpenObsoleteRunFrame.cache kept).trans seen.cache
  have census := ((congrArg OpenObsoleteRunFrame.census kept).trans seen.census).trans
    pass.barrierCensus.1.symm
  change seen.view.descriptors issued = pass.issueCensus at census
  have captured := (congrArg Cache.directory cache).trans pass.cached
  change (seen.view.directory issued seen.directory).map (seen.view.handle issued) =
    some (pass.capture, start.current.ready.state.directorySlot, 0) at captured
  obtain ⟨file, raw, handle⟩ := Option.map_eq_some_iff.mp captured
  have lookup := seen.readsDirectory issued
  rw [raw] at lookup
  obtain ⟨projection, frame⟩ := seen.syncs issued file raw
  have expected : pass.fsync (pass.capture, start.current.ready.state.directorySlot, 0) (pass.issueCensus, pass.atBarrier) =
      pass.fsyncResult (pass.returnCensus, pass.after) := pass.synced
  rw [handle, census, atBarrier, expected] at projection
  let actual := seen.calls.fsync file issued
  let reached := NativeFileEffectProjection.reached actual
  have sameStatus : actual = pass.fsyncResult reached := by
    calc
      actual = NativeFileEffectProjection.result (fun _ => reached)
          (NativeFileEffectProjection.result (fun after => (seen.view.descriptors after, (seen.view.files after).image)) actual) := by
        dsimp only [reached]
        cases actual <;> rfl
      _ = NativeFileEffectProjection.result (fun _ => reached) (pass.fsyncResult (pass.returnCensus, pass.after)) :=
        congrArg (NativeFileEffectProjection.result (fun _ => reached)) projection
      _ = pass.fsyncResult reached := by
        unfold NativeObsoleteRunPass.fsyncResult
        cases pass.outcome <;> rfl
  have sameImage : (seen.view.files reached).image = pass.after := by
    calc
      _ = (NativeFileEffectProjection.reached
          (NativeFileEffectProjection.result (fun after => (seen.view.descriptors after, (seen.view.files after).image)) actual)).2 := by
        dsimp only [reached]
        cases actual <;> rfl
      _ = (NativeFileEffectProjection.reached (pass.fsyncResult (pass.returnCensus, pass.after))).2 :=
        congrArg (fun result => (NativeFileEffectProjection.reached result).2) projection
      _ = _ := by
        unfold NativeObsoleteRunPass.fsyncResult
        cases pass.outcome <;> rfl
  refine ⟨reached, ?_, ⟨file, lookup, handle, census, atBarrier, sameStatus⟩, sameImage, frame⟩
  rw [OpenObsoleteRunCallbacks.sync, SyncPathGroup.run_single]
  simp only [syncWithHandles, beq_self_eq_true, ↓reduceIte, Bind.bind, EStateM.bind,
    lookup, Pure.pure, EStateM.pure]
  change seen.calls.fsync file issued = pass.fsyncResult reached at sameStatus
  rw [sameStatus]
  cases effect : pass.outcome <;>
    simp only [NativeObsoleteRunPass.fsyncResult, NativeObsoleteRunPass.collectorResult, effect,
      ← congrArg DiskDirectory.path start.directory] <;> rfl

/-- The reached preflight succeeded, then the common ordered unlink
dispatcher reached the exact directory barrier on the original cache. -/
def OpenObsoleteRunObservation.Entered (seen : OpenObsoleteRunObservation start held pass)
    (reached : heap) : Prop :=
  let directory := opened.directory
  let state := start.current.ready.state
  ∃ listed probed selected issued,
    seen.calls.manifest (directory.file .manifest) start.reached = .ok pass.reports.observed listed ∧
    seen.calls.list directory.path listed = .ok pass.reports.entries probed ∧
    selectRunFilesWith directory (pass.reports.observed.map fun _ => state.writer.installed.generation)
      (retainRunGeneration state.writer.installed.generation held) seen.calls.kind
      (pass.reports.entries.toList.map (·.fileName)) probed = .ok pass.reports.selected selected ∧
    ((pass.reports.selected.map RunCollection.Step.unlink).forM
      (RunCollection.performPaths seen.calls.remove (seen.calls.sync directory seen.directory seen.active seen.pending)
        throw (fun address => directory.file (.run address.1 address.2)) directory.path)) selected = .ok () issued ∧
    seen.Barrier issued reached

/-- One reached public call and its raw custody. The original phase
cell is read and no phase setter is issued. -/
structure OpenObsoleteRunObservation.Reached (seen : OpenObsoleteRunObservation start held pass)
    (next : NativeOpenedPosition opened) : Prop where
  source : UsesObsoleteRunCollectionSchedule opened.table opened.directory opened.phase
    seen.active seen.pending seen.directory held
  returned : seen.calls.run opened held seen.directory seen.active seen.pending start.reached = pass.collectorResult next.reached
  entered : seen.Entered next.reached
  physical : (seen.view.files next.reached).image = pass.after
  frame : seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory next.reached =
    seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory start.reached
  cache : seen.view.cacheAt next.reached seen.directory seen.active seen.pending = next.current.ready.state.cache
  census : seen.view.descriptors next.reached = next.current.ready.state.census
  owner : (seen.view.handle next.reached opened.lock).2.1 = next.current.ready.state.owner
  locked : (seen.view.files next.reached).owners = next.current.ready.state.files.owners
  preserved : next.current.ready.state = pass.next
  reads : next.current.ready.reads = start.current.ready.reads
  history : next.current.history = start.current.history
  submissions : next.current.submissions = start.current.submissions
  pins : next.pins = start.pins

private theorem OpenObsoleteRunObservation.returns (seen : OpenObsoleteRunObservation start held pass) :
    ∃ reached, seen.calls.run opened held seen.directory seen.active seen.pending start.reached = pass.collectorResult reached ∧
      seen.Entered reached ∧ (seen.view.files reached).image = pass.after ∧
      seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory reached =
        seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory start.reached := by
  have valid := start.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads start.reached opened.phase _ start.stored
  rw [valid.phase] at loaded
  have manifest := seen.manifest (opened.directory.file .manifest)
  have listed := seen.listed opened.directory.path
  have manifestPath := congrArg (·.file DiskFile.manifest) start.directory
  have directoryPath := congrArg DiskDirectory.path start.directory
  rw [← manifestPath, pass.reports.manifestRead] at manifest
  rw [← directoryPath, pass.reports.listed] at listed
  obtain ⟨atList, readManifest, imageListed, frameListed⟩ := manifest.returnsOk start.reached rfl
  obtain ⟨atProbes, readList, imageProbes, frameProbes⟩ := listed.returnsOk atList rfl
  obtain ⟨atUnlink, selected, imageUnlink, frameUnlink⟩ := seen.projectsSelector.returnsOk atProbes rfl
  let sync := seen.calls.sync opened.directory seen.directory seen.active seen.pending
  have dispatch := projectsUnlinkPrefix opened.directory pass.reports.selected seen.calls.remove sync
    pass.reports.removeFile pass.reports.syncDirectory seen.removes
  have unlinked := pass.unlinked
  unfold SegmentedRunCollectionReports.perform at unlinked
  have runPath := congrArg (fun directory (address : RunAddress) => directory.file (.run address.1 address.2))
    start.directory
  rw [runPath, directoryPath] at unlinked
  obtain ⟨issued, unlinks, atBarrier, beforeSync⟩ := dispatch.returnsOk atUnlink
    (by rw [imageUnlink, imageProbes, imageListed, seen.initial]; exact unlinked)
  have kept := beforeSync.trans (frameUnlink.trans (frameProbes.trans frameListed))
  obtain ⟨reached, synced, barrier, physical, frame⟩ := seen.syncsReached issued atBarrier kept
  rw [← pass.reports.names] at selected
  rw [manifestPath] at readManifest
  rw [directoryPath] at readList
  refine ⟨reached, ?_, ⟨atList, atProbes, atUnlink, issued, readManifest, readList, selected, unlinks, barrier⟩,
    physical, frame.trans kept⟩
  have generation := pass.reports.preflight valid.retained
  unfold OpenObsoleteRunCallbacks.run collectObsoleteRunsWith
  simp only [Bind.bind, EStateM.bind, loaded, Phase.installed, Pure.pure, EStateM.pure,
    readManifest, Function.comp_apply, generation, Except.mapError, liftExcept, readList, selected]
  rw [RunCollection.run, RunCollection.steps, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  dsimp only [sync] at unlinks
  simp only [Bind.bind, EStateM.bind, unlinks]
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, RunCollection.performPaths, Bind.bind, EStateM.bind,
    synced, Pure.pure, EStateM.pure]
  cases pass.collectorResult reached <;> rfl

private theorem OpenObsoleteRunObservation.continues (seen : OpenObsoleteRunObservation start held pass)
    (ready : NativeReadPosition start.current.history start.current.submissions)
    (state : ready.state = pass.next) (reads : ready.reads = start.current.ready.reads) :
    ∃ next : NativeOpenedPosition opened,
      next.current = ⟨start.current.history, start.current.submissions, ready⟩ ∧ seen.Reached next := by
  have session : ready.state.session = start.current.ready.state.session := by rw [state]; rfl
  have census : ready.state.census = start.current.ready.state.census := state ▸ pass.barrierCensus.2
  obtain ⟨reached, returned, entered, physical, frame⟩ := seen.returns
  have kept := congrArg OpenObsoleteRunFrame.phase frame
  let next : NativeOpenedPosition opened :=
    ⟨⟨start.current.history, start.current.submissions, ready⟩, reached,
      (congrArg (·.directory) session).trans start.directory,
      by rw [session]; exact kept.trans start.stored, start.pins⟩
  have uses := start.uses
  rw [start.directory] at uses
  refine ⟨next, rfl, obsoleteRunCollectionSchedule uses seen.references seen.cachePath held, returned, entered,
    physical, frame, ?_, ?_, ?_, ?_, state, reads, rfl, rfl, rfl⟩
  · exact ((congrArg OpenObsoleteRunFrame.cache frame).trans seen.cache).trans (congrArg NativeReadyState.cache state).symm
  · exact ((congrArg OpenObsoleteRunFrame.census frame).trans seen.census).trans census.symm
  · exact ((congrArg OpenObsoleteRunFrame.owner frame).trans seen.owner).trans (congrArg NativeReadyState.owner state).symm
  · apply ((congrArg OpenObsoleteRunFrame.owners frame).trans seen.locked).trans
    rw [show next.current.ready.state = ready.state from rfl, state]
    rfl

/-- Successful collection uses the submitted holds at the selector
and the common collector edge at the very same returned writer. -/
theorem NativeOpenedPosition.collectsObsoleteRuns
    (completed : NativeObsoleteRunCollection start.current.ready.state)
    (seen : OpenObsoleteRunObservation start held completed.toNativeObsoleteRunPass) :
    ∃ next : NativeOpenedPosition opened,
      seen.Reached next ∧ NativeExecutionStep start.current (.collectedObsoleteRuns held) next.current := by
  obtain ⟨ready, step⟩ := start.current.ready.collectsObsoleteRuns completed
  obtain ⟨next, reached, returned⟩ := seen.continues ready step.state step.reads
  refine ⟨next, returned, ?_⟩
  rw [reached, ← seen.holds]
  exact .collectObsoleteRuns start.current completed ready step

/-- Both ordinary directory fsync errors return the exact diagnostic.
The reached namespace, its crash choices and the previous read ledger
stay with the original ready handle. -/
theorem NativeOpenedPosition.reachesObsoleteRunBarrierError
    (failed : NativeObsoleteRunBarrierError start.current.ready.state)
    (seen : OpenObsoleteRunObservation start held failed.toNativeObsoleteRunPass) :
    ∃ next : NativeOpenedPosition opened,
      seen.Reached next ∧
      seen.calls.run opened held seen.directory seen.active seen.pending start.reached = .error failed.diagnostic next.reached ∧
      NativeExecutionStep start.current (.obsoleteRunCollectionError held failed.diagnostic) next.current := by
  obtain ⟨ready, step⟩ := start.current.ready.reachesObsoleteRunBarrierError failed
  obtain ⟨next, reached, returned⟩ := seen.continues ready step.state step.reads
  refine ⟨next, returned, ?_, ?_⟩
  · have actual := returned.returned
    unfold NativeObsoleteRunPass.collectorResult at actual
    rcases failed.failed with effect | effect <;> rw [effect] at actual <;> exact actual
  · rw [reached, ← seen.holds]
    exact .obsoleteRunCollectionError start.current failed ready step

/-- A subsequent report using the same raw heap view and input holds
starts from the exact namespace returned by the earlier pass. -/
theorem OpenObsoleteRunObservation.Reached.startsNextPass
    {seen : OpenObsoleteRunObservation start held pass} {next : NativeOpenedPosition opened}
    (returned : seen.Reached next) {retry : NativeObsoleteRunPass next.current.ready.state}
    (later : OpenObsoleteRunObservation next held retry) (sameView : later.view = seen.view) :
    retry.initial = pass.after ∧ retry.reports.held = pass.reports.held := by
  have input := later.initial
  rw [sameView] at input
  exact ⟨input.symm.trans returned.physical, later.holds.trans seen.holds.symm⟩

end Alvoki.Storage.DiskSession
