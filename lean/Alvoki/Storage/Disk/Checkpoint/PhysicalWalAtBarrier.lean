import Alvoki.Storage.Disk.Checkpoint.PendingClientReplay
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointCompletionHeldReopen

namespace Alvoki.Storage.DiskSession

open CheckpointPublication System SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The exact live inode, visible bytes and durable inode bytes at a WAL
name. The crash projection tracks available names independently of the
number of candidates for unrelated files. -/
structure CheckpointWalPathView where
  live : Option (Nat × ByteArray × List ByteArray)
  crashBinding : Option Nat → Prop

def checkpointWalPathView (bindings : WalInodeImage → FilePath → Option Nat)
    (crashNames : WalInodeImage → List (FilePath → Option Nat)) (image : WalInodeImage)
    (path : FilePath) : CheckpointWalPathView :=
  ⟨(bindings image path).map (fun inode => (inode, image.visible inode, image.crashBytes inode)),
    fun binding => ∃ names ∈ crashNames image, names path = binding⟩

def CheckpointWalPathView.Retains (view : CheckpointWalPathView) (inode : Nat) (bytes : ByteArray) : Prop :=
  view.live = some (inode, bytes, [bytes]) ∧ ∀ binding, view.crashBinding binding → binding = some inode

/-- The retained WAL identities come from the original held filesystem
observation. The checkpoint can change its own manifest and run names. -/
structure CheckpointWalInodes where
  marker : Nat
  keeper : Nat
  sealedInode : Nat → Nat

def CheckpointWalInodes.Retains (objects : CheckpointWalInodes) (directory : DiskDirectory)
    (before : SegmentedWriterState) (view : FilePath → CheckpointWalPathView) : Prop :=
  (view (directory.file .walBoundary)).Retains objects.marker
    (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
  (view (directory.file (.walSegment before.wal.active.first))).Retains objects.keeper before.wal.active.bytes ∧
  ∀ segment ∈ before.wal.sealed,
    (view (directory.file (.walSegment segment.first))).Retains (objects.sealedInode segment.first) segment.bytes

def checkpointWalPath (directory : DiskDirectory) (before : SegmentedWriterState) (path : FilePath) : Prop :=
  path = directory.file .walBoundary ∨ path = directory.file (.walSegment before.wal.active.first) ∨
    ∃ segment ∈ before.wal.sealed, path = directory.file (.walSegment segment.first)

/-- The input names and inode bytes come from the same namespace as the
physical run and manifest observations. Each returned callback supplies
its local WAL frame. The issued final barrier supplies its own frame for
the reached effect and does not report a return. -/
structure CheckpointManifestDirectoryReached.WalFrame {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : CheckpointPowerCut directory before} {calls : CheckpointManifestDirectoryCalls}
    {atRun : Nat → CheckpointManifestState} {runs : CheckpointManifestState → RunUnlinkImage}
    (reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs) where
  crashNames : WalInodeImage → List (FilePath → Option Nat)
  objects : CheckpointWalInodes
  initial : objects.Retains directory before (checkpointWalPathView reached.bindings crashNames (atRun 0).2)
  frame : ∀ (done : List CheckpointPublication.Step) step todo prior after,
    cut.completed = done ++ step :: todo →
    (done.forM (calls.perform cut)) (atRun 0) = .ok () prior →
    calls.perform cut step prior = .ok () after →
    ∀ path, checkpointWalPath directory before path →
      checkpointWalPathView reached.bindings crashNames after.2 path =
        checkpointWalPathView reached.bindings crashNames prior.2 path
  interruptedLive : ∀ path, checkpointWalPath directory before path →
    (checkpointWalPathView reached.bindings crashNames reached.interrupted path).live =
      (checkpointWalPathView reached.bindings crashNames reached.renamed path).live
  directoryNames : ∀ names ∈ crashNames reached.interrupted,
    if cut.tookEffect then
      ∀ path, checkpointWalPath directory before path → names path = reached.bindings reached.renamed path
    else
      ∃ earlier ∈ crashNames reached.renamed,
        ∀ path, checkpointWalPath directory before path → names path = earlier path
  manifestBindings : (crashNames reached.interrupted).map (fun names => names (directory.file .manifest)) =
    reached.crashBindings

namespace CheckpointManifestDirectoryReached.WalFrame

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {cut : CheckpointPowerCut directory before} {calls : CheckpointManifestDirectoryCalls}
  {atRun : Nat → CheckpointManifestState} {runs : CheckpointManifestState → RunUnlinkImage}
  {reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs}

private theorem retainFrom {objects : CheckpointWalInodes} {previous next : FilePath → CheckpointWalPathView}
    (known : objects.Retains directory before previous)
    (keeps : ∀ path, checkpointWalPath directory before path → ∀ {inode bytes},
      (previous path).Retains inode bytes → (next path).Retains inode bytes) :
    objects.Retains directory before next := by
  obtain ⟨marker, keeper, seals⟩ := known
  exact ⟨keeps _ (.inl rfl) marker, keeps _ (.inr (.inl rfl)) keeper,
    fun segment member => keeps _ (.inr (.inr ⟨segment, member, rfl⟩)) (seals segment member)⟩

private theorem keepsAtInterrupted (observed : reached.WalFrame) (path : FilePath)
    (isWal : checkpointWalPath directory before path) {inode : Nat} {bytes : ByteArray}
    (issuing : (checkpointWalPathView reached.bindings observed.crashNames reached.renamed path).Retains inode bytes) :
    (checkpointWalPathView reached.bindings observed.crashNames reached.interrupted path).Retains inode bytes := by
  refine ⟨(observed.interruptedLive path isWal).trans issuing.1, ?_⟩
  intro binding possible
  obtain ⟨names, survived, rfl⟩ := possible
  have effect := observed.directoryNames names survived
  cases timing : cut.tookEffect with
  | false =>
    simp only [timing, Bool.false_eq_true, ↓reduceIte] at effect
    obtain ⟨earlier, kept, agrees⟩ := effect
    rw [agrees path isWal]
    exact issuing.2 _ ⟨earlier, kept, rfl⟩
  | true =>
    simp only [timing, ↓reduceIte] at effect
    rw [effect path isWal]
    have live := congrArg (Option.map Prod.fst) issuing.1
    cases named : reached.bindings reached.renamed path with
    | none => simp [checkpointWalPathView, named] at live
    | some found => simpa [checkpointWalPathView, named] using live

/-- Every successfully returned prefix retains the actual WAL objects and
bytes from the checkpoint's starting filesystem observation. -/
theorem retainsAfterReturnedPrefix (observed : reached.WalFrame)
    {completedSteps remaining : List CheckpointPublication.Step} {state : CheckpointManifestState}
    (ordered : cut.completed = completedSteps ++ remaining)
    (returned : (completedSteps.forM (calls.perform cut)) (atRun 0) = .ok () state) :
    observed.objects.Retains directory before
      (checkpointWalPathView reached.bindings observed.crashNames state.2) := by
  refine retainFrom observed.initial fun path isWal {_inode _bytes} stable => ?_
  have preserves := successfulFrame (calls.perform cut)
    (fun after => checkpointWalPathView reached.bindings observed.crashNames after.2 path) returned (by
      intro done step todo prior after order earlier next
      apply observed.frame done step (todo ++ remaining) prior after ?_ earlier next path isWal
      rw [ordered, order, List.append_assoc]
      rfl)
  rw [preserves]
  exact stable

/-- The original marker, keeper and each retained seal still have the same
physical inode and bytes at issue and at the observed interruption. This
includes every reported survivor in the same directory crash map. -/
theorem retainsAtCut (observed : reached.WalFrame)
    (returned : (cut.completed.forM (calls.perform cut)) (atRun 0) =
      .ok () ((atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest), reached.renamed)) :
    observed.objects.Retains directory before
      (checkpointWalPathView reached.bindings observed.crashNames reached.renamed) ∧
    observed.objects.Retains directory before
      (checkpointWalPathView reached.bindings observed.crashNames reached.interrupted) := by
  have issuing := observed.retainsAfterReturnedPrefix (remaining := []) (by simp) returned
  exact ⟨issuing, retainFrom issuing observed.keepsAtInterrupted⟩

end CheckpointManifestDirectoryReached.WalFrame

/-- At the issued final checkpoint barrier, the reported joint crash map
selects physical WAL objects and the checkpoint for the same earlier
client replay. The issued callback need not return. -/
theorem CheckpointPowerCut.replaysPhysicalWalAtManifestDirectory {directory : DiskDirectory}
    {before : SegmentedWriterState} {first writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (cut : CheckpointPowerCut directory before)
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (calls : CheckpointManifestDirectoryCalls) (atRun : Nat → CheckpointManifestState)
    (runs : CheckpointManifestState → RunUnlinkImage)
    (runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs)
    (reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs)
    (completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged])
    (wal : reached.WalFrame) :
    let cache := (atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest)
    let atBarrier : CheckpointManifestState := (cache, reached.renamed)
    let interrupted : CheckpointManifestState := (cache, reached.interrupted)
    CheckpointIssue ((calls.callbacks directory).perform directory) (.ready before.installed)
      ⟨atRun 0, before.owners⟩ cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.manifest .syncDirectory) atBarrier ∧
    wal.objects.Retains directory before (checkpointWalPathView reached.bindings wal.crashNames atBarrier.2) ∧
    wal.objects.Retains directory before (checkpointWalPathView reached.bindings wal.crashNames interrupted.2) ∧
    ∀ names ∈ wal.crashNames interrupted.2, ∀ binding ∈ manifestCrashBytes interrupted.2 (names (directory.file .manifest)),
      cut.PendingReplay (runs interrupted) binding log reads := by
  intro cache atBarrier interrupted
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨returned, _, _, _, _, _⟩ := cut.atManifestDirectory ready calls atRun runs runPrefix reached completed
  obtain ⟨issued, replay⟩ := cut.replaysClientAtManifestDirectory start trace calls atRun runs runPrefix reached completed
  obtain ⟨issuedWal, stoppedWal⟩ := wal.retainsAtCut returned
  refine ⟨issued, issuedWal, stoppedWal, ?_⟩
  intro names survived binding bytes
  apply replay binding
  refine List.mem_flatMap.mpr ⟨names (directory.file .manifest), ?_, bytes⟩
  rw [← wal.manifestBindings]
  exact List.mem_map_of_mem survived

end Alvoki.Storage.DiskSession
