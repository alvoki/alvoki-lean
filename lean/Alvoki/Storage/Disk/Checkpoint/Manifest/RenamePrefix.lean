import Alvoki.Storage.Disk.CheckpointRunDirectoryCut

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

theorem CheckpointPowerCut.stagedManifest_ne_directory (directory : DiskDirectory) :
    directory.file .stagedManifest ≠ directory.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ "MANIFEST.next").length =
    directory.path.toString.length at length
  simp only [String.length_append] at length
  have slash : "/".length = 1 := rfl
  omega

/-- Read the admitted payloads of a manifest binding, including an absent name. -/
def manifestCrashBytes (files : WalInodeImage) : Option Nat → List (Option ByteArray)
  | none => [none]
  | some inode => (files.crashBytes inode).map some

abbrev CheckpointManifestHandle := DescriptorInventory × DescriptorSlot
abbrev CheckpointManifestState := Cache CheckpointManifestHandle × WalInodeImage

def checkpointManifestInode (handle : CheckpointManifestHandle) : Nat := handle.1.inode handle.2.description

/-- The versioned checkpoint's concrete dispatch with reported callbacks. -/
structure CheckpointManifestDirectoryCalls where
  writeRun : FilePath → ByteArray → EStateM IO.Error CheckpointManifestState Unit
  stage : FilePath → ByteArray → EStateM IO.Error WalInodeImage CheckpointManifestHandle
  openRead : FilePath → EStateM IO.Error WalInodeImage CheckpointManifestHandle
  fsync : CheckpointManifestHandle → EStateM IO.Error WalInodeImage Unit
  rename : FilePath → FilePath → EStateM IO.Error CheckpointManifestState Unit

noncomputable def CheckpointManifestDirectoryCalls.callbacks (calls : CheckpointManifestDirectoryCalls)
    (directory : DiskDirectory) : CheckpointFileCallbacks CheckpointManifestState :=
  ⟨calls.writeRun, fun path bytes => stageFreshWithCache path bytes calls.stage,
    SyncPathGroup.run (sync directory.path calls.openRead calls.fsync), calls.rename⟩

noncomputable def CheckpointManifestDirectoryCalls.perform {directory : DiskDirectory} {before : SegmentedWriterState}
    (calls : CheckpointManifestDirectoryCalls) (cut : CheckpointPowerCut directory before) :
    Step → EStateM IO.Error CheckpointManifestState Unit :=
  (calls.callbacks directory).perform directory cut.checkpoint.prepared cut.checkpoint.manifest

/-- The returned run directory sync, staged manifest write and staged
file sync leave this exact prefix at the issued manifest rename. -/
structure CheckpointManifestRenamePrefix {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (calls : CheckpointManifestDirectoryCalls)
    (runEnd : CheckpointManifestState) (runs : CheckpointManifestState → RunUnlinkImage) where
  directoryHandle : CheckpointManifestHandle
  directoryCaptured : runEnd.1.directory = some directoryHandle
  directorySettled : WalInodeImage
  runSynced : calls.fsync directoryHandle runEnd.2 = .ok () directorySettled
  runNames : runs (runEnd.1, directorySettled) = (runs runEnd).syncDirectory
  stageHandle : CheckpointManifestHandle
  written : WalInodeImage
  staged : calls.stage (directory.file .stagedManifest) cut.checkpoint.manifest directorySettled = .ok stageHandle written
  stageLive : stageHandle.2 ∈ stageHandle.1.slots
  stageBytes : written.visible (checkpointManifestInode stageHandle) = cut.checkpoint.manifest
  synced : calls.fsync stageHandle written = .ok () (written.completeFileSync (checkpointManifestInode stageHandle))
  bindings : WalInodeImage → FilePath → Option Nat
  stageBinding : bindings (written.completeFileSync (checkpointManifestInode stageHandle))
    (directory.file .stagedManifest) = some (checkpointManifestInode stageHandle)
  oldVisible : (bindings (written.completeFileSync (checkpointManifestInode stageHandle))
    (directory.file .manifest)).map written.visible = before.wal.directory.active.manifest
  oldStable : ∀ inode, bindings (written.completeFileSync (checkpointManifestInode stageHandle))
    (directory.file .manifest) = some inode →
    (written.completeFileSync (checkpointManifestInode stageHandle)).crashBytes inode = [written.visible inode]
  stageRunNames : runs (runEnd.1.remember (directory.file .stagedManifest) stageHandle, written) =
    runs (runEnd.1, directorySettled)
  syncRunNames : runs (runEnd.1.consume (directory.file .stagedManifest),
      written.completeFileSync (checkpointManifestInode stageHandle)) =
    runs (runEnd.1.remember (directory.file .stagedManifest) stageHandle, written)

namespace CheckpointManifestRenamePrefix

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}
  {calls : CheckpointManifestDirectoryCalls} {runEnd : CheckpointManifestState} {runs : CheckpointManifestState → RunUnlinkImage}

def inode (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) : Nat := checkpointManifestInode observed.stageHandle

def atRename (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) : CheckpointManifestState :=
  (runEnd.1.consume (directory.file .stagedManifest), observed.written.completeFileSync observed.inode)

def oldBinding (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) : Option Nat :=
  observed.bindings observed.atRename.2 (directory.file .manifest)

/-- The initial run barrier settles the complete run map. The following
stage write and file barrier preserve it up to the reached rename. -/
theorem runNamesSettled (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) :
    runs observed.atRename = (runs runEnd).syncDirectory :=
  observed.syncRunNames.trans (observed.stageRunNames.trans observed.runNames)

/-- The staged inode carries the newly encoded manifest at the issued rename. -/
theorem stagedCrashBytes (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) :
    manifestCrashBytes observed.atRename.2 (some observed.inode) = [some cut.checkpoint.manifest] := by
  simp [atRename, inode, manifestCrashBytes, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, observed.stageBytes]

/-- The untouched prior live name selects its own synced bytes or absence. -/
theorem priorCrashBytes (observed : CheckpointManifestRenamePrefix cut calls runEnd runs) :
    manifestCrashBytes observed.atRename.2 observed.oldBinding = [before.wal.directory.active.manifest] := by
  have visible : observed.oldBinding.map observed.written.visible = before.wal.directory.active.manifest := observed.oldVisible
  cases binding : observed.oldBinding with
  | none =>
    rw [binding] at visible
    exact congrArg (fun bytes => [bytes]) visible
  | some inode =>
    have data : observed.atRename.2.crashBytes inode = [observed.written.visible inode] := observed.oldStable inode binding
    rw [binding] at visible
    change (observed.atRename.2.crashBytes inode).map some = _
    rw [data, List.map_singleton]
    exact congrArg (fun bytes => [bytes]) visible

end CheckpointManifestRenamePrefix

theorem CheckpointManifestDirectoryCalls.syncDirectorySelected (calls : CheckpointManifestDirectoryCalls) (directory : DiskDirectory)
    (state : CheckpointManifestState) (handle : CheckpointManifestHandle) (captured : state.1.directory = some handle) :
    sync directory.path calls.openRead calls.fsync directory.path state = withCache state.1 (calls.fsync handle state.2) := by
  rcases state with ⟨cache, image⟩
  change cache.directory = some handle at captured
  simp [sync, Cache.resolve, captured]

/-- Compose the actual run prefix, retained directory sync, stage write
and exact staged descriptor sync into their shared returned prefix. -/
theorem CheckpointManifestRenamePrefix.returns {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : CheckpointPowerCut directory before} {calls : CheckpointManifestDirectoryCalls}
    {atRun : Nat → CheckpointManifestState} {runs : CheckpointManifestState → RunUnlinkImage}
    (runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs)
    (observed : CheckpointManifestRenamePrefix cut calls (atRun cut.checkpoint.table.runs.length) runs) :
    ((runSteps cut.checkpoint.table.runs.length ++ [Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]).forM
      (calls.perform cut)) (atRun 0) = .ok () observed.atRename := by
  let count := cut.checkpoint.table.runs.length
  let perform := calls.perform cut
  let runEnd := atRun count
  let stagePath := directory.file .stagedManifest
  let cache := runEnd.1.consume stagePath
  let staged := (runEnd.1.remember stagePath observed.stageHandle, observed.written)
  let synced := observed.written.completeFileSync observed.inode
  have runDirectory : perform .syncRunsDirectory runEnd = .ok () (runEnd.1, observed.directorySettled) := by
    change SyncPathGroup.run (sync directory.path calls.openRead calls.fsync) #[directory.path] runEnd = _
    rw [SyncPathGroup.run_single, calls.syncDirectorySelected directory runEnd observed.directoryHandle observed.directoryCaptured,
      observed.runSynced]
    rfl
  have stageWritten : perform (.manifest .writeStaged) (runEnd.1, observed.directorySettled) = .ok () staged := by
    change stageFreshWithCache stagePath cut.checkpoint.manifest calls.stage (runEnd.1, observed.directorySettled) = _
    have wrote : calls.stage stagePath cut.checkpoint.manifest observed.directorySettled =
        .ok observed.stageHandle observed.written := observed.staged
    simp only [stageFreshWithCache, wrote, staged]
  have stageSynced : perform (.manifest .syncStaged) staged = .ok () (cache, synced) := by
    change SyncPathGroup.run (sync directory.path calls.openRead calls.fsync) #[stagePath] staged = _
    rw [SyncPathGroup.run_single, syncRemembered (cache := runEnd.1) (CheckpointPowerCut.stagedManifest_ne_directory directory),
      observed.synced]
    rfl
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  let suffix : List Step := [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]
  change EStateM.bind ((runSteps count).forM perform) (fun _ => suffix.forM perform) (atRun 0) = _
  have finishedRuns : ((runSteps count).forM perform) (atRun 0) = .ok () runEnd := runPrefix.returned
  have finishedSuffix : suffix.forM perform = (perform .syncRunsDirectory >>= fun _ =>
      perform (.manifest .writeStaged) >>= fun _ => perform (.manifest .syncStaged)) := by
    simp [suffix, List.forM_eq_forM, List.forM_cons, List.forM_nil]
  rw [finishedSuffix]
  simp only [Bind.bind, EStateM.bind, finishedRuns, runDirectory, stageWritten, stageSynced]
  rfl

end Alvoki.Storage.DiskSession
