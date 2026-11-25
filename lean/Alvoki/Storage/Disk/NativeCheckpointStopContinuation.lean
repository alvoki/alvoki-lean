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

private theorem stagedManifestOffSelected (state : NativeReadyState) {path : FilePath}
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
    (fun _ selected => stagedManifestOffSelected current.current.ready.state selected)
  exact stable.frame (consume.trans frame.2)

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
