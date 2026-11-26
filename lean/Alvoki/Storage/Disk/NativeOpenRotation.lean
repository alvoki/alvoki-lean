import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeOpenClose
import Alvoki.Storage.Disk.NativeFileEffectProjection

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap : Type}

/-- The raw rotation callbacks use the same names as the modeled
successor probe, creation and singleton sync groups. -/
structure OpenRotationCallbacks (heap : Type) where
  read : FilePath → EStateM IO.Error heap (Option ByteArray)
  create : FilePath → EStateM IO.Error heap Unit
  sync : FilePath → EStateM IO.Error heap Unit
  setActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → Option (FilePath × IO.FS.Handle) →
    EStateM IO.Error heap Unit

/-- The public rotation uses the same phase reference, with no-follow
successor lookup, exclusive creation into the pending cell, singleton
groups on the original cache and the exact active-cell reset. -/
def UsesRotationSchedule (db : DiskTable) (directory : DiskDirectory) (phase : IO.Ref (Phase Installed))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle))) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (cachedDirectory : IO.Ref (Option IO.FS.Handle)) : Prop :=
  ∃ fsync : IO.FS.Handle → IO Unit,
    db.rotateWal = rotateWalSchedule (m := IO) (do (← phase.get).installed)
      (fun state => checkActiveSegmentWith directory state FilePath.symlinkMetadata) phase.set
      (fun first => WalSegmentRotation.runAt directory first
        (fun path => WalSegmentRotation.readEmptyWith path.symlinkMetadata.toBaseIO path "WAL segment successor is not empty")
        (fun path => IO.FS.Handle.mk path .writeNew >>= fun file => pending.modify (pushPending path file))
        (fun path => SyncPathGroup.run (fun name =>
          syncWithHandles directory.path name cachedDirectory.get pending.get pending.set active.get
            (fun path => IO.FS.Handle.mk path .read) fsync) #[path]))
      (active.set none)

theorem rotationSchedule {db : DiskTable} {directory lock files phase token active pending cachedDirectory}
    (uses : db.UsesOpenReferences directory lock files phase token)
    (references : files.UsesCacheReferences active pending cachedDirectory)
    (cachePath : files.AtDirectory directory.path) :
    UsesRotationSchedule db directory phase active pending cachedDirectory := by
  obtain ⟨rfl, _, rfl, rfl, _⟩ := uses
  obtain ⟨rfl, rfl, rfl⟩ := references
  unfold DiskTable.OpenSyncFiles.AtDirectory at cachePath
  refine ⟨_, by
    simp only [db.rotateWal_schedule, readEmptyWalSegment_schedule, syncFilesSyncPaths_schedule, cachePath]
    rfl⟩

def OpenRotationCallbacks.run (calls : OpenRotationCallbacks heap) (opened : NativeOpenedHandle heap)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) (active : IO.Ref (Option (FilePath × IO.FS.Handle))) :
    EStateM IO.Error heap Unit :=
  rotateWalSchedule (do (← opened.get opened.phase).installed)
    (fun installed => checkActiveSegmentWith opened.directory installed (fun path => liftExcept (lookup path)))
    (opened.set opened.phase)
    (fun first => WalSegmentRotation.runAt opened.directory first calls.read calls.create calls.sync)
    (calls.setActive active none)

namespace RotationProjects

/-- Projection composes through the actual successor branch and its
ordered syncs, so no completed raw publication result is a premise. -/
theorem rotateFiles {files frame : Type} {project : heap → files} {retain : heap → frame}
    (calls : OpenRotationCallbacks heap)
    (directory : DiskDirectory) (first : Nat)
    (read : FilePath → EStateM IO.Error files (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error files Unit)
    (reads : ∀ path, NativeFileEffectProjection project retain (calls.read path) (read path))
    (creates : ∀ path, NativeFileEffectProjection project retain (calls.create path) (create path))
    (syncs : ∀ path, NativeFileEffectProjection project retain (calls.sync path) (sync path)) :
    NativeFileEffectProjection project retain (WalSegmentRotation.runAt directory first calls.read calls.create calls.sync)
      (WalSegmentRotation.runAt directory first read create sync) := by
  rw [WalSegmentRotation.runAt_fileEffects, WalSegmentRotation.runAt_fileEffects]
  apply NativeFileEffectProjection.bind
  · unfold WalSegmentRotation.observeSuccessorWith
    apply NativeFileEffectProjection.bind (reads _)
    intro bytes
    cases bytes with
    | none => exact NativeFileEffectProjection.pure _ _ _
    | some bytes =>
      by_cases empty : bytes.size = 0
      · simp only [empty, ↓reduceIte]
        exact NativeFileEffectProjection.pure _ _ _
      · simp only [empty, ↓reduceIte]
        exact NativeFileEffectProjection.failure _ _ _
  · intro present
    cases present
    · exact NativeFileEffectProjection.bind (creates _) fun _ =>
        NativeFileEffectProjection.bind (syncs _) fun _ =>
          NativeFileEffectProjection.bind (syncs _) fun _ => NativeFileEffectProjection.pure _ _ _
    · exact NativeFileEffectProjection.bind (syncs _) fun _ =>
        NativeFileEffectProjection.bind (syncs _) fun _ => NativeFileEffectProjection.pure _ _ _

end RotationProjects


abbrev OpenRotationFiles := CensusDirectoryCache × DescriptorInventory × RotationCreateFiles

def OpenCloseHeapView.rotationFiles (view : OpenCloseHeapView heap RotationCreateFiles)
    (active : IO.Ref (Option (FilePath × IO.FS.Handle))) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (cachedDirectory : IO.Ref (Option IO.FS.Handle)) (reached : heap) : OpenRotationFiles :=
  (view.cacheAt reached cachedDirectory active pending, view.descriptors reached, (view.files reached).image)

/-- The concrete directory handle in the original cache and the
original opened lock's slot survive the rotation's local operations. -/
def OpenCloseHeapView.rotationCustody (view : OpenCloseHeapView heap RotationCreateFiles)
    (cachedDirectory : IO.Ref (Option IO.FS.Handle)) (lock : IO.FS.Handle) (reached : heap) :
    Option IO.FS.Handle × DescriptorSlot × LockOwners :=
  (view.directory reached cachedDirectory, (view.handle reached lock).2.1, (view.files reached).owners)

/-- Primitive observations for rotation on the opened synchronization
record. File calls may change the raw heap and their individual
projections follow the same ordered callbacks as the ready proof. The
reported active-cell clear starts only after both barriers returned. -/
structure OpenRotationObservation {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (read : FilePath → EStateM IO.Error OpenRotationFiles (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error OpenRotationFiles Unit)
    (entry settled reset : OpenRotationFiles) where
  view : OpenCloseHeapView heap RotationCreateFiles
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  directory : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences active pending directory
  cachePath : opened.files.AtDirectory opened.directory.path
  calls : OpenRotationCallbacks heap
  initial : view.rotationFiles active pending directory current.reached = entry
  owner : (view.handle current.reached opened.lock).2.1 = current.current.ready.state.owner
  held : (view.files current.reached).owners = current.current.ready.state.files.owners
  reads : ∀ path, NativeFileEffectProjection (view.rotationFiles active pending directory)
    (fun reached => (opened.contents reached opened.phase, view.rotationCustody directory opened.lock reached))
    (calls.read path) (read path)
  creates : ∀ path, NativeFileEffectProjection (view.rotationFiles active pending directory)
    (fun reached => (opened.contents reached opened.phase, view.rotationCustody directory opened.lock reached))
    (calls.create path) (create path)
  syncs : ∀ path, NativeFileEffectProjection (view.rotationFiles active pending directory)
    (fun reached => (opened.contents reached opened.phase, view.rotationCustody directory opened.lock reached))
    (calls.sync path) (sync path)
  phaseFrame : ∀ {before after} {phase : Phase Installed},
    opened.set opened.phase phase before = .ok () after →
      view.rotationFiles active pending directory after = view.rotationFiles active pending directory before ∧
      view.rotationCustody directory opened.lock after = view.rotationCustody directory opened.lock before
  clears : ∀ before, view.rotationFiles active pending directory before = settled →
    opened.contents before opened.phase = some .poisoned →
    ∃ after, calls.setActive active none before = .ok () after ∧
      view.rotationFiles active pending directory after = reset ∧ opened.contents after opened.phase = some .poisoned ∧
      view.rotationCustody directory opened.lock after = view.rotationCustody directory opened.lock before

private theorem rotationGuardOnHeap {files : Type} (directory : DiskDirectory) (installed : Installed)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) (entryValue : files) (before : heap)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error files) directory installed (fun path => liftExcept (lookup path)) entryValue =
      .ok () entryValue) :
    checkActiveSegmentWith (m := EStateM IO.Error heap) directory installed (fun path => liftExcept (lookup path)) before =
      .ok () before := by
  unfold checkActiveSegmentWith at checked ⊢
  cases observed : lookup (directory.file (.walSegment installed.activeFirst)) with
  | error cause =>
    simp [observed, liftExcept, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at checked
  | ok metadata =>
    by_cases regular : metadata.type == .file <;>
      by_cases single : metadata.numLinks == 1 <;>
      by_cases size : metadata.byteSize.toNat == installed.walBytes - installed.activeFirst * WAL.frameSize <;>
      simp [observed, liftExcept, checkPrivateRegularWith, regular, single, size, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure, EStateM.pure] at checked ⊢

private theorem OpenRotationObservation.completes {opened : NativeOpenedHandle heap}
    {current : NativeOpenedPosition opened} {read create sync entry settled reset}
    (seen : OpenRotationObservation current read create sync entry settled reset)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error OpenRotationFiles)
      opened.directory current.current.ready.state.writer.installed
      (fun path => liftExcept (lookup path)) entry = .ok () entry)
    (published : WalSegmentRotation.runAt opened.directory
      (current.current.ready.state.writer.installed.walBytes / WAL.frameSize) read create sync entry = .ok () settled) :
    let state := current.current.ready.state
    let ready := .ready { state.writer.installed with activeFirst := state.writer.installed.walBytes / WAL.frameSize }
    ∃ poisoned atClear cleared reached,
      seen.calls.run opened lookup seen.active current.reached = .ok () reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      WalSegmentRotation.runAt opened.directory (state.writer.installed.walBytes / WAL.frameSize)
        seen.calls.read seen.calls.create seen.calls.sync poisoned = .ok () atClear ∧
      seen.calls.setActive seen.active none atClear = .ok () cleared ∧
      opened.set opened.phase ready cleared = .ok () reached ∧
      opened.contents reached opened.phase = some ready ∧
      seen.view.rotationFiles seen.active seen.pending seen.directory reached = reset ∧
      seen.view.rotationCustody seen.directory opened.lock reached =
        seen.view.rotationCustody seen.directory opened.lock current.reached := by
  intro state ready
  let project := seen.view.rotationFiles seen.active seen.pending seen.directory
  let successor := state.writer.installed.walBytes / WAL.frameSize
  have phase : state.session.phase = .ready state.writer.installed := current.current.ready.readPrefix.refines.1.phase
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, saved⟩ :=
    opened.phaseEffects.writes current.reached opened.phase state.session.phase .poisoned current.stored
  have fileEntry : project poisoned = entry := (seen.phaseFrame excluded).1.trans seen.initial
  obtain ⟨files, framed⟩ := RotationProjects.rotateFiles seen.calls opened.directory successor read create sync
    seen.reads seen.creates seen.syncs poisoned
  change NativeFileEffectProjection.result project
    (WalSegmentRotation.runAt opened.directory successor seen.calls.read seen.calls.create seen.calls.sync poisoned) =
    WalSegmentRotation.runAt opened.directory successor read create sync (project poisoned) at files
  rw [fileEntry, published] at files
  cases resumed : WalSegmentRotation.runAt opened.directory successor seen.calls.read seen.calls.create seen.calls.sync poisoned with
  | error cause reached =>
    simp only [resumed, NativeFileEffectProjection.result] at files
    cases files
  | ok result atClear =>
    cases result
    have beforeClear : project atClear = settled := by
      simpa only [resumed, NativeFileEffectProjection.result, EStateM.Result.ok.injEq, true_and] using files
    have atBarrier := framed
    rw [resumed] at atBarrier
    obtain ⟨cleared, clearedActive, afterClear, stillPoisoned, retained⟩ :=
      seen.clears atClear beforeClear ((congrArg Prod.fst atBarrier).trans saved)
    obtain ⟨reached, stored, contents⟩ :=
      opened.phaseEffects.writes cleared opened.phase .poisoned ready stillPoisoned
    refine ⟨poisoned, atClear, cleared, reached, ?_, excluded, resumed, clearedActive, stored, contents,
      (seen.phaseFrame stored).1.trans afterClear,
      (seen.phaseFrame stored).2.trans (retained.trans ((congrArg Prod.snd atBarrier).trans (seen.phaseFrame excluded).2))⟩
    have guard := rotationGuardOnHeap opened.directory state.writer.installed lookup entry current.reached checked
    have grows : state.writer.installed.activeFirst < state.writer.installed.walBytes / WAL.frameSize := nonempty
    change WalSegmentRotation.runAt opened.directory (state.writer.installed.walBytes / WAL.frameSize)
      seen.calls.read seen.calls.create seen.calls.sync poisoned = .ok () atClear at resumed
    change opened.set opened.phase (.ready { state.writer.installed with
      activeFirst := state.writer.installed.walBytes / WAL.frameSize }) cleared = .ok () reached at stored
    simp only [OpenRotationCallbacks.run, rotateWalSchedule, Bind.bind, EStateM.bind, loaded, phase,
      Phase.installed, Pure.pure, EStateM.pure, grows, ↓reduceIte, guard, publishPrepared, excluded,
      resumed, clearedActive, stored]



variable {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)

/-- If the reached keeper is empty, the public rotation returns on the
same heap without reaching any filesystem callback or phase setter. -/
theorem NativeOpenedPosition.rotatesEmptyOnOpenPhase
    (calls : OpenRotationCallbacks heap) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    {active pending directory} (references : opened.files.UsesCacheReferences active pending directory)
    (cachePath : opened.files.AtDirectory opened.directory.path)
    (empty : current.current.ready.state.writer.installed.walBytes / WAL.frameSize ≤
      current.current.ready.state.writer.installed.activeFirst) :
    UsesRotationSchedule opened.table opened.directory opened.phase active pending directory ∧
    calls.run opened lookup active current.reached = .ok () current.reached ∧
    NativeExecutionStep current.current .rotatedWal current.current := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase
    current.current.ready.state.session.phase current.stored
  refine ⟨rotationSchedule opened.uses references cachePath, ?_, .rotateEmpty current.current ?_⟩
  · simp [OpenRotationCallbacks.run, rotateWalSchedule, Bind.bind, EStateM.bind, loaded, valid.phase,
      Phase.installed, Pure.pure, EStateM.pure, Nat.not_lt.mpr empty]
  · intro image files lookup read create sync release
    dsimp only
    rw [valid.phase]
    exact runObservedRotationWithReset_empty _ _ _ lookup read create sync release empty

variable {current}

structure OpenRotationObservation.Reached {read create sync entry settled reset}
    (seen : OpenRotationObservation current read create sync entry settled reset)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) (position : NativeOpenedPosition opened) : Prop where
  source : UsesRotationSchedule opened.table opened.directory opened.phase seen.active seen.pending seen.directory
  pins : position.pins = current.pins
  returned : seen.calls.run opened lookup seen.active current.reached = .ok () position.reached
  steps : ∃ poisoned atClear cleared,
    opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
    WalSegmentRotation.runAt opened.directory (current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
      seen.calls.read seen.calls.create seen.calls.sync poisoned = .ok () atClear ∧
    seen.calls.setActive seen.active none atClear = .ok () cleared ∧
    opened.set opened.phase position.current.ready.state.session.phase cleared = .ok () position.reached
  cleared : seen.view.active position.reached seen.active = none
  fileState : seen.view.rotationFiles seen.active seen.pending seen.directory position.reached = reset
  directoryHandle : seen.view.directory position.reached seen.directory =
    seen.view.directory current.reached seen.directory
  lockSlot : (seen.view.handle position.reached opened.lock).2.1 = current.current.ready.state.owner
  held : (seen.view.files position.reached).owners = current.current.ready.state.files.owners

/-- The reached successor probe and file barrier. Creation is issued only
after an absent result. Reusing an empty file leaves the probe heap unchanged. -/
structure OpenRotationCallbacks.SuccessorFilePrefix (calls : OpenRotationCallbacks heap)
    (directory : DiskDirectory) (first : Nat) (entry synced : heap) where
  observed : Option ByteArray
  afterRead : heap
  beforeSync : heap
  read : calls.read (directory.file (.walSegment first)) entry = .ok observed afterRead
  successor : observed.elim
    (calls.create (directory.file (.walSegment first)) afterRead = .ok () beforeSync)
    (fun bytes => bytes.size = 0 ∧ beforeSync = afterRead)
  sync : calls.sync (directory.file (.walSegment first)) beforeSync = .ok () synced

/-- Preserve a local relation through the actual successor file prefix.
An existing empty file reaches the file sync without a create. -/
theorem OpenRotationCallbacks.SuccessorFilePrefix.frames
    {calls : OpenRotationCallbacks heap} {directory : DiskDirectory} {first : Nat} {entry synced : heap}
    (filePrefix : calls.SuccessorFilePrefix directory first entry synced)
    {frame : heap → heap → Prop}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (read : frame entry filePrefix.afterRead)
    (created : filePrefix.observed = none → frame filePrefix.afterRead filePrefix.beforeSync)
    (fileSync : frame filePrefix.beforeSync synced) : frame entry synced := by
  have selected := filePrefix.successor
  cases observed : filePrefix.observed with
  | none => exact trans read (trans (created observed) fileSync)
  | some bytes =>
    simp only [observed, Option.elim] at selected
    exact trans read (selected.2 ▸ fileSync)

private theorem OpenRotationCallbacks.reachesSuccessor (calls : OpenRotationCallbacks heap)
    (directory : DiskDirectory) (first : Nat) {entry reached : heap}
    (returned : WalSegmentRotation.runAt directory first calls.read calls.create calls.sync entry = .ok () reached) :
    ∃ synced, Nonempty (calls.SuccessorFilePrefix directory first entry synced) ∧
      calls.sync directory.path synced = .ok () reached := by
  let path := directory.file (.walSegment first)
  let barriers : EStateM IO.Error heap Unit := do
    calls.sync path
    calls.sync directory.path
    pure ()
  have syncedAt {before : heap} (done : barriers before = .ok () reached) :
      ∃ synced, calls.sync path before = .ok () synced ∧ calls.sync directory.path synced = .ok () reached := by
    cases fileSync : calls.sync path before with
    | error cause failed =>
      simp [barriers, Bind.bind, EStateM.bind, fileSync] at done
    | ok value synced =>
      cases value
      cases dirSync : calls.sync directory.path synced with
      | error cause failed =>
        simp [barriers, Bind.bind, EStateM.bind, fileSync, dirSync] at done
      | ok value after =>
        cases value
        have endpoint : after = reached := by
          simpa [barriers, Bind.bind, EStateM.bind, fileSync, dirSync, Pure.pure, EStateM.pure] using done
        exact ⟨synced, rfl, endpoint ▸ dirSync⟩
  rw [WalSegmentRotation.runAt_fileEffects] at returned
  change (do
    let present ← WalSegmentRotation.observeSuccessorWith (calls.read path)
    if present then barriers else do calls.create path; barriers) entry = .ok () reached at returned
  cases read : calls.read path entry with
  | error cause failed =>
    simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, read] at returned
  | ok observed afterRead =>
    cases observed with
    | none =>
      simp only [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, read, Pure.pure, EStateM.pure,
        Bool.false_eq_true, ↓reduceIte] at returned
      cases made : calls.create path afterRead with
      | error cause failed => simp [made] at returned
      | ok value beforeSync =>
        cases value
        have complete : barriers beforeSync = .ok () reached := by
          simpa only [made] using returned
        obtain ⟨synced, fileSync, directorySync⟩ := syncedAt complete
        exact ⟨synced, ⟨⟨none, afterRead, beforeSync, read, made, fileSync⟩⟩, directorySync⟩
    | some bytes =>
      by_cases empty : bytes.size = 0
      · have complete : barriers afterRead = .ok () reached := by
          simpa only [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, read, empty, ↓reduceIte,
            Pure.pure, EStateM.pure] using returned
        obtain ⟨synced, fileSync, directorySync⟩ := syncedAt complete
        exact ⟨synced, ⟨⟨some bytes, afterRead, afterRead, read, ⟨empty, rfl⟩, fileSync⟩⟩, directorySync⟩
      · simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, read, empty,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned

/-- The actual primitive returns of a successful rotation on the opened table. -/
structure OpenRotationObservation.SuccessfulSteps
    {read create sync entry settled reset} (seen : OpenRotationObservation current read create sync entry settled reset)
    (position : NativeOpenedPosition opened) where
  poisoned : heap
  fileSynced : heap
  beforeClear : heap
  cleared : heap
  poison : opened.set opened.phase .poisoned current.reached = .ok () poisoned
  file : seen.calls.SuccessorFilePrefix opened.directory
    (current.current.ready.state.writer.installed.walBytes / WAL.frameSize) poisoned fileSynced
  directorySync : seen.calls.sync opened.directory.path fileSynced = .ok () beforeClear
  clear : seen.calls.setActive seen.active none beforeClear = .ok () cleared
  restore : opened.set opened.phase position.current.ready.state.session.phase cleared = .ok () position.reached

private theorem OpenRotationObservation.Reached.successfulSteps
    {read create sync entry settled reset} {seen : OpenRotationObservation current read create sync entry settled reset}
    {lookup position} (reached : seen.Reached lookup position) : Nonempty (seen.SuccessfulSteps position) := by
  obtain ⟨poisoned, beforeClear, cleared, poison, ran, clear, restore⟩ := reached.steps
  obtain ⟨synced, ⟨file⟩, directorySync⟩ := seen.calls.reachesSuccessor opened.directory _ ran
  exact ⟨⟨poisoned, synced, beforeClear, cleared, poison, file, directorySync, clear, restore⟩⟩

/-- Frame the primitive edges actually reached by this successful rotation.
The existing successor branch requires no creation effect. -/
def OpenRotationObservation.LocalFrames
    {read create sync entry settled reset} (seen : OpenRotationObservation current read create sync entry settled reset)
    (frame : heap → heap → Prop) : Prop :=
  ∀ {lookup position}, seen.Reached lookup position → ∀ steps : seen.SuccessfulSteps position,
    frame current.reached steps.poisoned ∧
    frame steps.poisoned steps.file.afterRead ∧
    (steps.file.observed = none → frame steps.file.afterRead steps.file.beforeSync) ∧
    frame steps.file.beforeSync steps.fileSynced ∧
    frame steps.fileSynced steps.beforeClear ∧
    frame steps.beforeClear steps.cleared ∧
    frame steps.cleared position.reached

/-- Carry a footprint from the installed phase to the literal rotation return. -/
theorem OpenRotationObservation.Reached.frames
    {read create sync entry settled reset} {seen : OpenRotationObservation current read create sync entry settled reset}
    {lookup position} (reached : seen.Reached lookup position)
    {frame : heap → heap → Prop}
    (trans : ∀ {a b c}, frame a b → frame b c → frame a c) (effects : seen.LocalFrames frame) :
    frame current.reached position.reached := by
  obtain ⟨steps⟩ := reached.successfulSteps
  obtain ⟨poison, read, create, fileSync, directorySync, clear, restore⟩ := effects reached steps
  exact trans poison (trans (steps.file.frames trans read create fileSync) (trans directorySync (trans clear restore)))

private theorem OpenRotationObservation.reachesReady {read create sync entry settled reset}
    (seen : OpenRotationObservation current read create sync entry settled reset)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error OpenRotationFiles)
      current.current.ready.state.session.directory current.current.ready.state.writer.installed
      (fun path => liftExcept (lookup path)) entry = .ok () entry)
    (published : WalSegmentRotation.runAt current.current.ready.state.session.directory
      (current.current.ready.state.writer.installed.walBytes / WAL.frameSize) read create sync entry = .ok () settled)
    (next : NativeReadPosition current.current.history current.current.submissions)
    (directory : next.state.session.directory = opened.directory)
    (phase : next.state.session.phase = .ready { current.current.ready.state.writer.installed with
      activeFirst := current.current.ready.state.writer.installed.walBytes / WAL.frameSize })
    (resetActive : reset.1.active = none) :
    ∃ position : NativeOpenedPosition opened,
      position.current = ⟨current.current.history, current.current.submissions, next⟩ ∧ seen.Reached lookup position := by
  rw [current.directory] at checked published
  obtain ⟨poisoned, atClear, cleared, reached, ran, poison, barriers, active, store, installed, files, custody⟩ :=
    seen.completes lookup nonempty checked published
  let position : NativeOpenedPosition opened := ⟨⟨current.current.history, current.current.submissions, next⟩,
    reached, directory, phase.symm ▸ installed, current.pins⟩
  have clearedActive := (congrArg (fun value : OpenRotationFiles => value.1.active) files).trans resetActive
  change (seen.view.active reached seen.active).map (fun entry => (entry.1, seen.view.handle reached entry.2)) = none
    at clearedActive
  have stored : opened.set opened.phase next.state.session.phase cleared = .ok () reached := by
    rw [phase]
    exact store
  exact ⟨position, rfl, rotationSchedule opened.uses seen.references seen.cachePath, rfl, ran,
    ⟨poisoned, atClear, cleared, poison, barriers, active, stored⟩, Option.map_eq_none_iff.mp clearedActive, files,
    congrArg Prod.fst custody, (congrArg (fun value => value.2.1) custody).trans seen.owner,
    (congrArg (fun value => value.2.2) custody).trans seen.held⟩

variable (current)

abbrev OpenRotationObservation.Created (report : NativeReadyCreatedRotation current.current.ready.state) :=
  OpenRotationObservation current report.readEmpty report.create report.group
    (current.current.ready.state.cache, current.current.ready.state.census, report.parent.files)
    (current.current.ready.state.cache, report.directorySynced)
    ((report.next current.current.ready.readPrefix.refines.1).cache,
      (report.next current.current.ready.readPrefix.refines.1).census, report.settled)

abbrev OpenRotationObservation.Existing (report : NativeReadyExistingRotation current.current.ready.state) :=
  OpenRotationObservation current report.opened.readEmpty report.create report.file.group
    (report.opened.cache, report.opened.inventory, report.opened.files)
    (report.opened.cache, report.directory.after)
    ((report.next current.current.ready.readPrefix.refines.1).cache,
      (report.next current.current.ready.readPrefix.refines.1).census, report.directory.settled)

/-- A successful exclusive-create rotation continues the same opened
table at the new keeper. The exact raw return carries the phase/cache
effects and the existing physical certificate for the settled inode. -/
theorem NativeOpenedPosition.rotatesCreatedOnOpenPhase
    (report : NativeReadyCreatedRotation current.current.ready.state)
    (seen : OpenRotationObservation.Created current report) :
    ∃ (next : NativeReadPosition current.current.history current.current.submissions) (position : NativeOpenedPosition opened),
      NativeCreatedRotationContinuation current.current.ready next report ∧
      NativeExecutionStep current.current .rotatedWal position.current ∧
      position.current = ⟨current.current.history, current.current.submissions, next⟩ ∧ seen.Reached report.lookup position := by
  obtain ⟨next, rotation⟩ := current.current.ready.rotatesCreated report
  have directory : next.state.session.directory = opened.directory := by
    rw [rotation.reached]
    exact current.directory
  have phase : next.state.session.phase = .ready { current.current.ready.state.writer.installed with
      activeFirst := current.current.ready.state.writer.installed.walBytes / WAL.frameSize } := by
    rw [rotation.reached]
    rfl
  obtain ⟨position, reached, returned⟩ :=
    seen.reachesReady report.lookup report.parent.nonempty report.checked report.publishes next directory phase rfl
  exact ⟨next, position, rotation, reached.symm ▸ .rotateCreated current.current report next rotation, reached, returned⟩

/-- Reusing an already present, checked empty successor follows the same
raw interpreter. The observed file and directory barriers publish
that inode and the same active-cell reset precedes the ready setter. -/
theorem NativeOpenedPosition.rotatesExistingOnOpenPhase
    (report : NativeReadyExistingRotation current.current.ready.state)
    (seen : OpenRotationObservation.Existing current report) :
    ∃ (next : NativeReadPosition current.current.history current.current.submissions) (position : NativeOpenedPosition opened),
      NativeExistingRotationContinuation current.current.ready next report ∧
      NativeExecutionStep current.current .rotatedWal position.current ∧
      position.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      seen.Reached report.opened.lookup position := by
  obtain ⟨next, rotation⟩ := current.current.ready.rotatesExisting report
  have directory : next.state.session.directory = opened.directory := by
    rw [rotation.reached]
    exact current.directory
  have phase : next.state.session.phase = .ready { current.current.ready.state.writer.installed with
      activeFirst := current.current.ready.state.writer.installed.walBytes / WAL.frameSize } := by
    rw [rotation.reached]
    rfl
  obtain ⟨position, reached, returned⟩ :=
    seen.reachesReady report.opened.lookup report.opened.nonempty report.opened.checked
      (report.directory.publishes report.create) next directory phase rfl
  exact ⟨next, position, rotation, reached.symm ▸ .rotateExisting current.current report next rotation, reached, returned⟩

end Alvoki.Storage.DiskSession
