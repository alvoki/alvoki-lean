import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeQuietPowerLossRaw

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

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
  · intro equal
    have names := basename (renderRunFileName metadata.header.generation index) "MANIFEST.next"
      (congrArg FilePath.toString equal)
    have initialChars := congrArg (fun name : String => name.toList.take 4) names
    change ("run-" ++ metadata.header.generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 =
      ("MANIFEST.next" : String).toList.take 4 at initialChars
    simp [String.toList_append] at initialChars

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
one joint survivor of the reached protected files. The normalized file
image frames the old logical checkpoint and WAL. Physical run bindings
can change outside that projection. -/
theorem NativeCheckpointSourceStop.observesReboot
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
    (previous : view.files reached.2 = current.current.ready.state.files)
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
  exact ⟨stop.stoppedCall, ⟨Prod.ext rfl previous, fun _ _ => rfl, survivorNames, survivorBytes⟩⟩

end Alvoki.Storage.DiskSession
