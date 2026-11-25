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
  sync : FilePath → EStateM IO.Error heap Unit

def OpenObsoleteRunCallbacks.kind (calls : OpenObsoleteRunCallbacks heap) (path : FilePath) :
    EStateM IO.Error heap (Except String IO.FS.FileType) := do
  let result ← calls.stat path
  liftExcept (runKindAt (fun _ => result) path)

def OpenObsoleteRunCallbacks.run (calls : OpenObsoleteRunCallbacks heap)
    (opened : NativeOpenedHandle heap) (held : List UInt64) : EStateM IO.Error heap Unit :=
  collectObsoleteRunsWith opened.directory held (do (← opened.get opened.phase).installed)
    calls.manifest (liftExcept ∘ Except.mapError IO.userError) calls.list calls.kind calls.remove calls.sync

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
    (pass : NativeObsoleteRunCollection current.current.ready.state) where
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
  syncs : NativeFileEffectProjection (fun reached => (view.files reached).image)
    (view.obsoleteRunFrame opened active pending directory) (calls.sync opened.directory.path)
    (pass.reports.syncDirectory current.current.ready.state.session.directory.path)

private theorem projectsRunDispatch {heap frame : Type} {project : heap → RunUnlinkImage} {retain : heap → frame}
    (directory : DiskDirectory) (selected : List RunAddress)
    (rawRemove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (rawSync : FilePath → EStateM IO.Error heap Unit)
    (remove : FilePath → EStateM IO.Error RunUnlinkImage (Except IO.Error Unit))
    (sync : FilePath → EStateM IO.Error RunUnlinkImage Unit)
    (removes : ∀ path, NativeFileEffectProjection project retain (rawRemove path) (remove path))
    (syncs : NativeFileEffectProjection project retain (rawSync directory.path) (sync directory.path)) :
    NativeFileEffectProjection project retain
      (RunCollection.run selected (RunCollection.performPaths rawRemove rawSync throw
        (fun address => directory.file (.run address.1 address.2)) directory.path))
      (RunCollection.run selected (RunCollection.performPaths remove sync throw
        (fun address => directory.file (.run address.1 address.2)) directory.path)) := by
  apply NativeFileEffectProjection.forM
  intro step
  cases step with
  | syncDirectory => exact syncs
  | unlink address =>
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
  {held : List UInt64} {pass : NativeObsoleteRunCollection start.current.ready.state}

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

/-- One reached public call and its raw custody. There is no phase
setter, and the final directory callback comes from the same ordered pass. -/
structure OpenObsoleteRunObservation.Reached (seen : OpenObsoleteRunObservation start held pass)
    (next : NativeOpenedPosition opened) : Prop where
  source : UsesObsoleteRunCollectionSchedule opened.table opened.directory opened.phase
    seen.active seen.pending seen.directory held
  returned : seen.calls.run opened held start.reached = .ok () next.reached
  physical : (seen.view.files next.reached).image = pass.atBarrier.syncDirectory
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
    ∃ reached, seen.calls.run opened held start.reached = .ok () reached ∧
      (seen.view.files reached).image = pass.atBarrier.syncDirectory ∧
      seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory reached =
        seen.view.obsoleteRunFrame opened seen.active seen.pending seen.directory start.reached := by
  have valid := start.current.ready.readPrefix.refines.1
  let state := start.current.ready.state
  have loaded := opened.phaseEffects.reads start.reached opened.phase _ start.stored
  rw [valid.phase] at loaded
  have manifest := seen.manifest (opened.directory.file .manifest)
  have listed := seen.listed opened.directory.path
  have syncs := seen.syncs
  have probes := seen.projectsSelector
  rw [← start.directory] at manifest listed syncs probes
  rw [pass.reports.manifestRead] at manifest
  rw [pass.reports.listed] at listed
  obtain ⟨atList, readManifest, imageListed, frameListed⟩ := manifest.returnsOk start.reached rfl
  obtain ⟨atProbes, readList, imageProbes, frameProbes⟩ := listed.returnsOk atList rfl
  obtain ⟨atUnlink, selected, imageUnlink, frameUnlink⟩ := probes.returnsOk atProbes rfl
  have dispatch := projectsRunDispatch state.session.directory pass.reports.selected seen.calls.remove seen.calls.sync
    pass.reports.removeFile pass.reports.syncDirectory seen.removes syncs
  have compiled := (pass.reports.run_eq_schedule valid.retained).symm.trans (pass.returns valid).1
  change RunCollection.run pass.reports.selected pass.reports.perform pass.initial =
    .ok () pass.atBarrier.syncDirectory at compiled
  obtain ⟨reached, returned, physical, frame⟩ := dispatch.returnsOk atUnlink
    (by rw [imageUnlink, imageProbes, imageListed, seen.initial]; exact compiled)
  refine ⟨reached, ?_, physical, frame.trans (frameUnlink.trans (frameProbes.trans frameListed))⟩
  have generation := pass.reports.preflight valid.retained
  rw [← pass.reports.names] at selected
  unfold OpenObsoleteRunCallbacks.run collectObsoleteRunsWith
  rw [← start.directory]
  simp only [Bind.bind, EStateM.bind, loaded, Phase.installed, Pure.pure, EStateM.pure,
    readManifest, Function.comp_apply, generation, Except.mapError, liftExcept, readList, selected]
  exact returned

/-- Successful collection uses the submitted holds at the selector
and the common collector edge at the very same returned writer. -/
theorem NativeOpenedPosition.collectsObsoleteRuns
    (seen : OpenObsoleteRunObservation start held pass) :
    ∃ next : NativeOpenedPosition opened,
      seen.Reached next ∧ NativeExecutionStep start.current (.collectedObsoleteRuns held) next.current := by
  obtain ⟨reached, returned, physical, frame⟩ := seen.returns
  obtain ⟨ready, step⟩ := start.current.ready.collectsObsoleteRuns pass
  have kept := congrArg OpenObsoleteRunFrame.phase frame
  let next : NativeOpenedPosition opened :=
    ⟨⟨start.current.history, start.current.submissions, ready⟩, reached,
      (congrArg (·.directory) step.session).trans start.directory,
      by rw [step.session]; exact kept.trans start.stored, start.pins⟩
  have uses := start.uses
  rw [start.directory] at uses
  have cache := ((congrArg OpenObsoleteRunFrame.cache frame).trans seen.cache).trans step.cache.symm
  have census := ((congrArg OpenObsoleteRunFrame.census frame).trans seen.census).trans step.census.symm
  have owner := ((congrArg OpenObsoleteRunFrame.owner frame).trans seen.owner).trans step.owner.symm
  have locked := ((congrArg OpenObsoleteRunFrame.owners frame).trans seen.locked).trans
    (congrArg LockedFileState.owners step.files).symm
  refine ⟨next, ⟨obsoleteRunCollectionSchedule uses seen.references seen.cachePath held, returned, physical, frame,
    cache, census, owner, locked, step.state, step.reads, rfl, rfl, rfl⟩, ?_⟩
  rw [← seen.holds]
  exact .collectObsoleteRuns start.current pass ready step

end Alvoki.Storage.DiskSession
