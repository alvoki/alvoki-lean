import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeQuietPowerLossRaw

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private theorem stagedManifestUnparsed (directory : DiskDirectory) :
    parseWalSegmentName "MANIFEST.next" = none := by
  cases parsed : parseWalSegmentName "MANIFEST.next" with
  | none => rfl
  | some first =>
    have collision : directory.file .stagedManifest = directory.file (.walSegment first) :=
      (directory.walSegment_path_of_parsed parsed).symm
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive collision
    cases impossible

private theorem extentsIgnoreUnparsedNames [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (names : List String) :
    readWalSegmentExtentsWith directory lstat names =
      readWalSegmentExtentsWith directory lstat (names.filter (fun name => (parseWalSegmentName name).isSome)) := by
  let measure := readWalSegmentExtentWith directory lstat
  have inventory : names.filterMapM measure =
      (names.filter (fun name => (parseWalSegmentName name).isSome)).filterMapM measure := by
    induction names with
    | nil => rfl
    | cons name rest prior =>
      cases parsed : parseWalSegmentName name with
      | none =>
        have skipped : measure name = pure none := by simp [measure, readWalSegmentExtentWith, parsed]
        simp [List.filterMapM_cons, parsed, skipped, prior]
      | some first => simp [List.filterMapM_cons, parsed, prior]
  simp only [readWalSegmentExtentsWith, ← show measure = readWalSegmentExtentWith directory lstat from rfl, inventory]

/-- The actual marked reader may project the returned directory listing
to parsed WAL names. It still executes that same listing once, and every
subsequent callback runs on the same reached heap. -/
theorem readSelectedWithCachedExtents_projectsWalNames {heap : Type}
    (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) (before : heap) :
    readSelectedWithCachedExtents directory watermark length
      (fun path => do
        let entries ← list path
        pure (entries.filter (fun entry => (parseWalSegmentName entry.fileName).isSome)))
      lstat readSeal readKeeper before =
    readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper before := by
  by_cases checked : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize
  · cases listed : list directory.path before with
    | error => simp [readSelectedWithCachedExtents, Bind.bind, EStateM.bind, checked, listed]
    | ok entries reached =>
      have names : (entries.toList.filter (fun entry => (parseWalSegmentName entry.fileName).isSome)).map
          (·.fileName) = (entries.toList.map (·.fileName)).filter (fun name => (parseWalSegmentName name).isSome) := by
        simp [List.filter_map, Function.comp_def]
      simp [readSelectedWithCachedExtents, Bind.bind, EStateM.bind, checked, listed, Pure.pure, EStateM.pure,
        names, ← extentsIgnoreUnparsedNames]
  · simp [readSelectedWithCachedExtents, Bind.bind, EStateM.bind, checked, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

/-- The marked WAL selector ignores MANIFEST.next at any listing position.
Both successful listing observations use the same reached heap. All
selected extent and payload callbacks therefore see the same execution. -/
theorem readSelectedWithCachedExtents_ignoresStagedManifest {heap : Type}
    (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list listWithScratch : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    {before reached : heap} {entries entriesWithScratch : Array IO.FS.DirEntry}
    (listed : list directory.path before = .ok entries reached)
    (listedWithScratch : listWithScratch directory.path before = .ok entriesWithScratch reached)
    (earlier later : List String)
    (names : entries.toList.map (·.fileName) = earlier ++ later)
    (namesWithScratch : entriesWithScratch.toList.map (·.fileName) = earlier ++ "MANIFEST.next" :: later)
    (checked : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize) :
    readSelectedWithCachedExtents directory watermark length listWithScratch lstat readSeal readKeeper before =
      readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper before := by
  have inventory : readWalSegmentExtentsWith directory lstat (entriesWithScratch.toList.map (·.fileName)) =
      readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) := by
    rw [extentsIgnoreUnparsedNames directory lstat (entriesWithScratch.toList.map (·.fileName)),
      extentsIgnoreUnparsedNames directory lstat (entries.toList.map (·.fileName)), namesWithScratch, names]
    simp [List.filter_append, stagedManifestUnparsed directory]
  simp [readSelectedWithCachedExtents, Bind.bind, EStateM.bind, checked, listed, listedWithScratch, inventory, Pure.pure]

/-- The reboot image used by marked recovery projects the selected files.
The reached staging metadata can vary independently of that projection. -/
theorem SegmentedWriterState.powerLossFiles_stagedMetadata (state : SegmentedWriterState)
    (directory : DiskDirectory) (staged : DirectoryPublication.Entry → Option (ByteArray × Bool)) :
    ({ state with files := { state.files with directory := { state.files.directory with staged } } }
      : SegmentedWriterState).powerLossFiles directory = state.powerLossFiles directory := rfl

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {rebooted : heap} {bytes : heap → Nat → ByteArray}

theorem NativeReadyState.crashPath_ne_stagedManifest (state : NativeReadyState) {path : FilePath}
    (selected : state.crashPath path) : path ≠ state.session.directory.file .stagedManifest := by
  let directory := state.session.directory
  have basename (left right : String)
      (equal : directory.path.toString ++ "/" ++ left = directory.path.toString ++ "/" ++ right) :
      left = right := (String.append_right_inj (directory.path.toString ++ "/")).mp equal
  rcases selected with rfl | rfl | rfl | wal | ⟨_, metadata, index, _, _, _, rfl⟩
  · exact (file_ne_directory directory .stagedManifest).symm
  · intro equal
    have bad := basename "LOCK" "MANIFEST.next" (congrArg FilePath.toString equal)
    contradiction
  · intro equal
    have bad := basename "MANIFEST" "MANIFEST.next" (congrArg FilePath.toString equal)
    contradiction
  · have noSegment (first : Nat) : directory.file (.walSegment first) ≠ directory.file .stagedManifest := by
      intro equal
      obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive equal.symm
      cases impossible
    rcases wal with rfl | rfl | ⟨segment, _, rfl⟩
    · intro equal
      have bad := basename "WAL.commit" "MANIFEST.next" (congrArg FilePath.toString equal)
      contradiction
    · exact noSegment _
    · exact noSegment segment.first
  · exact runFile_ne_stagedManifest directory metadata.header.generation index

/-- At a stopped staged-MANIFEST fsync the previous selected checkpoint
and WAL are still durable. The stop is derived from the whole source call.
Removing the pending reference and syncing its still-live descriptor use
separate local observations at their actual heaps. -/
theorem NativeCheckpointSourceStop.manifestSyncPreservesSelected
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncStaged) reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    {atFsync : heap}
    (pending : CheckpointPendingSyncAt calls view cache.pending fsync
      (current.current.ready.state.session.directory.file .stagedManifest) stop.atIssue.2 atFsync)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (stable : NativeReadyStorage current.current.ready.state (observe stop.atIssue.2).storageObservation)
    (consume : (observe stop.atIssue.2).storageObservation.Frames current.current.ready.state.crashPath
      (observe atFsync).storageObservation)
    (effective : Bool)
    (effect : ∀ literal, calls.fsync literal atFsync = .error reason reached.2 →
      let inode := (view.descriptors atFsync).inode (view.handle atFsync literal).2.1.description
      let path := current.current.ready.state.session.directory.file .stagedManifest
      (observe atFsync).visible path = some inode ∧
      (∀ other, (observe atFsync).visible other = some inode → other = path) ∧
      inodes reached.2 = (if effective then (inodes atFsync).completeFileSync inode else inodes atFsync) ∧
      (observe reached.2).visible = (observe atFsync).visible ∧
      (observe reached.2).crashBindings = (observe atFsync).crashBindings) :
    NativeReadyStorage current.current.ready.state (observe reached.2).storageObservation := by
  obtain ⟨literal, _, _, target, _, stopped, _⟩ := stop.manifestSyncIssuesRawSync calls cache projected pending
  have frame := target.stoppedRunFrames calls stopped inodes runs observe _ effective (effect literal)
    (fun _ selected => NativeReadyState.crashPath_ne_stagedManifest current.current.ready.state selected)
  exact stable.frame (consume.trans frame.2)

private theorem preparedGeneration {old next : Installed} {manifest : ByteArray}
    (prepared : CheckpointPreflight (.ready old) (.ok (next, manifest))) :
    next.generation.toNat = old.generation.toNat + 1 := by
  cases prepared with
  | prepared _ fits _ => exact UInt64.toNat_ofNat_of_lt' fits.1

/-- A prepared run belongs to the next generation, disjoint from all
canonical files selected by the installed manifest and WAL. -/
private theorem newRunOffSelected {state : NativeReadyState} (valid : state.Valid)
    {next : Installed} {manifest : ByteArray}
    (prepared : CheckpointPreflight state.session.phase (.ok (next, manifest))) (index : Nat)
    {path : FilePath} (selected : state.crashPath path) :
    path ≠ state.session.directory.file (.run next.generation index) := by
  let directory := state.session.directory
  have reserved (file : DiskFile) (name : String)
      (shape : directory.file file = ⟨directory.path.toString ++ "/" ++ name⟩)
      (distinct : name.toList.take 4 ≠ "run-".toList) :
      directory.file file ≠ directory.file (.run next.generation index) := by
    intro equal
    rw [shape] at equal
    have names := (String.append_right_inj (directory.path.toString ++ "/")).mp
      (congrArg FilePath.toString equal)
    change name = renderRunFileName next.generation index at names
    apply distinct
    rw [names]
    change ("run-" ++ next.generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 = "run-".toList
    simp [String.toList_append]
  have noSegment (first : Nat) :
      directory.file (.walSegment first) ≠ directory.file (.run next.generation index) := by
    intro equal
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive equal.symm
    cases impossible
  rcases selected with rfl | rfl | rfl | wal | ⟨_, metadata, run, binding, decoded, _, rfl⟩
  · exact (file_ne_directory _ _).symm
  · exact reserved .lock "LOCK" rfl (by decide)
  · exact reserved .manifest "MANIFEST" rfl (by decide)
  · rcases wal with rfl | rfl | ⟨segment, _, rfl⟩
    · exact reserved .walBoundary "WAL.commit" rfl (by decide)
    · exact noSegment _
    · exact noSegment segment.first
  · have prior := CheckpointPowerCut.selectedGeneration valid.retained.resumed.selected
    rw [← valid.retained.resumed.generation, binding, Option.mapM, decoded] at prior
    have generation := preparedGeneration (valid.phase ▸ prepared)
    apply runPath_ne directory
    intro same
    have old : metadata.header.generation = state.writer.installed.generation := Except.ok.inj prior
    have new : metadata.header.generation = next.generation := congrArg Prod.fst same
    have conflict := congrArg UInt64.toNat (old.symm.trans new)
    omega

/-- A pending consume and the exact issued file sync leave the prior
checkpoint and WAL footprint unchanged at the source stop. -/
theorem NativeCheckpointSourceStop.runSyncFrames {index : Nat}
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun index) reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    {atFsync : heap}
    (pending : CheckpointPendingSyncAt calls view cache.pending fsync
      (current.current.ready.state.session.directory.file (.run stop.next.generation index)) stop.atIssue.2 atFsync)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (consume : (observe stop.atIssue.2).storageObservation.Frames current.current.ready.state.crashPath
      (observe atFsync).storageObservation)
    (effective : Bool)
    (effect : ∀ literal, calls.fsync literal atFsync = .error reason reached.2 →
      let inode := (view.descriptors atFsync).inode (view.handle atFsync literal).2.1.description
      let path := current.current.ready.state.session.directory.file (.run stop.next.generation index)
      (observe atFsync).visible path = some inode ∧
      (∀ other, (observe atFsync).visible other = some inode → other = path) ∧
      inodes reached.2 = (if effective then (inodes atFsync).completeFileSync inode else inodes atFsync) ∧
      (observe reached.2).visible = (observe atFsync).visible ∧
      (observe reached.2).crashBindings = (observe atFsync).crashBindings) :
    (observe stop.atIssue.2).storageObservation.Frames current.current.ready.state.crashPath
      (observe reached.2).storageObservation := by
  obtain ⟨literal, _, _, target, _, stopped, _⟩ := stop.runFileIssuesRawSync calls cache projected
    pending.loaded pending.stored pending.consumed pending.primitive
  have valid := current.current.ready.readPrefix.refines.1
  have frame := target.stoppedRunFrames calls stopped inodes runs observe _ effective (effect literal)
    (fun _ selected => newRunOffSelected valid stop.prepared index selected)
  exact consume.trans frame.2

/-- The only successful step before the first run fsync is the run
write. Its returned handle and byte buffer supply the physical frame. -/
theorem NativeCheckpointSourceStop.firstRunWriteFrames
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun 0) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (writeEffect : ∀ payload handle,
      let path := current.current.ready.state.session.directory.file (.run stop.next.generation 0)
      primitives.cached.writeRun path payload stop.poisoned = .ok handle stop.atIssue.2 →
      ∃ inode, RunWriteInodeFrame path inode (inodes stop.atIssue.2) (observe stop.poisoned) (observe stop.atIssue.2) ∧
        ∀ other, (observe stop.poisoned).visible other = some inode → other = path) :
    (observe stop.poisoned).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.atIssue.2).storageObservation := by
  obtain ⟨entry, run, handle, earlier, _, wrote, _, _, _⟩ := stop.runFileUsesWrittenHandle
  have sameEntry : entry = (current.current.ready.state.cache, stop.poisoned) := by
    rw [show runSteps 0 = [] from rfl] at earlier
    simpa [List.forM, Pure.pure, ExceptT.pure, ExceptT.run, ExceptT.mk, EStateM.pure] using earlier.symm
  rw [sameEntry] at wrote
  obtain ⟨_, effect, privateBinding⟩ := writeEffect run.run.bytes handle wrote
  have valid := current.current.ready.readPrefix.refines.1
  exact effect.preservesCheckpointFootprint (fun _ _ => rfl) privateBinding
    (fun _ selected => newRunOffSelected valid stop.prepared 0 selected)

/-- Byte and namespace effects of each successful run write and file
sync, indexed by the prior prefix of a source checkpoint stop. -/
structure ReturnedCheckpointRunEffects
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (count : Nat) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes heap) (runs heap)) : Prop where
  write : ∀ index < count, ∀ before after payload handle,
    let path := current.current.ready.state.session.directory.file (.run stop.next.generation index)
    primitives.cached.writeRun path payload before = .ok handle after →
    let inode := handle.1.inode handle.2.1.description
    RunWriteInodeFrame path inode (inodes after) (observe before) (observe after) ∧
      ∀ other, (observe before).visible other = some inode → other = path
  sync : ∀ index < count, ∀ (before after : CheckpointWorld heap) handle issued,
    let state := current.current.ready.state
    let path := state.session.directory.file (.run stop.next.generation index)
    before.1.resolve state.session.directory.path path primitives.openRead before.2 = .ok handle (after.1, issued) →
    fsync handle issued = .ok (.ok ()) after.2 →
    let inode := handle.1.inode handle.2.1.description
    (observe before.2).storageObservation.Frames state.crashPath (observe issued).storageObservation ∧
    (observe issued).visible path = some inode ∧
    (∀ other, (observe issued).visible other = some inode → other = path) ∧
    inodes after.2 = (inodes issued).completeFileSync inode ∧
    (observe after.2).visible = (observe issued).visible ∧
    (observe after.2).crashBindings = (observe issued).crashBindings

/-- Fold the prior checkpoint and WAL frame over the actual returned run
prefix. The write, handle selection and successful file sync each retain
their own reached heap. -/
theorem NativeCheckpointSourceStop.returnedRunFrames
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    {count : Nat} (completedRuns : stop.completed = runSteps count)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (effects : ReturnedCheckpointRunEffects stop count inodes runs observe) :
    (observe stop.poisoned).storageObservation.Frames current.current.ready.state.crashPath
      (observe stop.atIssue.2).storageObservation := by
  let state := current.current.ready.state
  let directory := state.session.directory
  let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
  have valid := current.current.ready.readPrefix.refines.1
  refine successfulCheckpointStepsPreserve perform (fun world => (observe world.2).storageObservation)
    (CheckpointStorageObservation.Frames state.crashPath) (CheckpointStorageObservation.Frames.refl _)
    CheckpointStorageObservation.Frames.trans stop.completed ?_ stop.returnedPrefix
  intro step member before after returned
  rw [completedRuns] at member
  simp only [runSteps, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨index, within, write | sync⟩ := member
  · subst step
    obtain ⟨run, handle, _, wrote, _⟩ := primitives.runWriteReturned directory fsync stop.next stop.manifest index returned
    obtain ⟨effect, privateBinding⟩ := effects.write index within before.2 after.2 run.run.bytes handle wrote
    exact effect.preservesCheckpointFootprint (fun _ _ => rfl) privateBinding
      (fun _ selected => newRunOffSelected valid stop.prepared index selected)
  · subst step
    have completed : (primitives.syncUntilStop directory.path fsync
        #[directory.file (.run stop.next.generation index)]).run before = .ok (.ok ()) after := returned
    obtain ⟨handle, issued, resolved, synced⟩ := primitives.returnedFsync fsync directory.path _ completed
    obtain ⟨selection, _, privateBinding, bytes, visible, surviving⟩ := effects.sync index within before after handle issued
      resolved synced
    have effect := (observe issued).fileSyncEffect (observe after.2) bytes visible surviving
    refine selection.trans (effect.frames ?_)
    intro path selected inode bound same
    exact newRunOffSelected valid stop.prepared index selected (privateBinding path (same ▸ bound))

/-- Cache routing and physical effects at the literal first directory
sync reached by the source checkpoint. -/
structure RunsDirectoryStopObservations
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap)) where
  calls : CheckpointRawSyncCalls heap
  projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1
  load : calls.readDirectory cache.directory stop.atIssue.2 = .ok (view.directory stop.atIssue.2 cache.directory) stop.atIssue.2
  primitive : ∀ literal, view.directory stop.atIssue.2 cache.directory = some literal →
    fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = calls.fsync literal stop.atIssue.2 ∧
      RawFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal
  effective : Bool
  effect : ∀ literal, calls.fsync literal stop.atIssue.2 = .error reason reached.2 →
    let state := current.current.ready.state
    let root := state.session.directory.path
    (observe stop.atIssue.2).visible root =
      some ((view.descriptors stop.atIssue.2).inode (view.handle stop.atIssue.2 literal).2.1.description) ∧
    inodes reached.2 = inodes stop.atIssue.2 ∧
    (observe reached.2).visible = (observe stop.atIssue.2).visible ∧
    ∀ names ∈ (observe reached.2).crashBindings,
      if effective then
        ∃ prior ∈ (observe stop.atIssue.2).crashBindings, names root = prior root ∧
          ∀ child, state.crashPath child → child ≠ root → names child = (observe stop.atIssue.2).visible child
      else names ∈ (observe stop.atIssue.2).crashBindings

/-- The stopped run-directory barrier preserves the already selected
checkpoint. Effective fsync settles the selected child names. The
directory's own binding remains subject to the independent parent frame. -/
theorem NativeCheckpointSourceStop.runsDirectoryPreservesSelected
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
    (stable : NativeReadyStorage current.current.ready.state (observe stop.atIssue.2).storageObservation)
    (seen : RunsDirectoryStopObservations (view := view) stop cache inodes runs observe) :
    NativeReadyStorage current.current.ready.state (observe reached.2).storageObservation := by
  obtain ⟨literal, _, _, _, stopped, _⟩ := stop.runsDirectoryIssuesRawSync seen.calls cache seen.projected seen.load seen.primitive
  obtain ⟨_, bytes, visible, survives⟩ := seen.effect literal stopped
  apply stable.frame
  constructor
  · intro path _
    exact ⟨congrFun visible path, fun inode _ => congrArg (fun state : WalInodeImage => state.crashBytes inode) bytes⟩
  · intro names allowed
    have chosen := survives names allowed
    cases effective : seen.effective
    · simp only [effective, Bool.false_eq_true, ite_false] at chosen
      exact ⟨names, chosen, fun _ _ => rfl⟩
    · simp only [effective, ite_true] at chosen
      obtain ⟨prior, earlier, root, children⟩ := chosen
      refine ⟨prior, earlier, fun path selected => ?_⟩
      by_cases same : path = current.current.ready.state.session.directory.path
      · simpa only [same] using root
      · exact (children path selected same).trans (stable.settled prior earlier path selected).symm

/-- The optional reboot starts at the source stop's exact heap. It chooses
one joint survivor of the reached protected files. The original census,
selected names and bytes are observed on that heap and at the reboot.
Other names, including a staged manifest, have their own crash choices. -/
theorem NativeCheckpointSourceStop.observesReboot
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
    (names : FilePath → Option Nat) (chosen : names ∈ (storage reached.2).crashNames)
    (contents : Nat → ByteArray)
    (durable : ∀ path,
      checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
        current.current.ready.state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → contents inode ∈ (storage reached.2).files.bytes inode)
    (rebootObjects : Nat → Nat)
    (survivorNames : ∀ path, current.current.ready.state.crashPath path →
      (storage rebooted).files.names path = names path)
    (survivorBytes : ∀ path,
      checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
        current.current.ready.state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → bytes rebooted inode = contents inode) :
    let crash := stable.observeCrash names chosen contents durable rebootObjects
    (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .error (stage, reason) reached ∧
    RawQuietRebootEntry crash view (fun atHeap => (storage atHeap).files.names) bytes reached.2 rebooted
      (view.descriptors reached.2) := by
  exact ⟨stop.stoppedCall, ⟨rfl, fun _ _ => rfl, survivorNames, survivorBytes⟩⟩

end Alvoki.Storage.DiskSession
