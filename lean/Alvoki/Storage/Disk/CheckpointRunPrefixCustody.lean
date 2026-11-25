import Alvoki.Storage.Disk.CheckpointRunWriteCustody
import Alvoki.Storage.Disk.RunUnlinkEffects

namespace Alvoki.Storage.CheckpointPublication

open System DiskSession SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private theorem storedRunExists {indices : List Nat} {read : Nat → Option ByteArray}
    {files : List ByteArray} (stored : indices.mapM read = some files) {index : Nat}
    (named : index ∈ indices) : ∃ bytes, read index = some bytes := by
  induction indices generalizing files with
  | nil => simp at named
  | cons first rest ih =>
    cases firstRead : read first with
    | none => simp [List.mapM_cons, firstRead, Bind.bind, Option.bind] at stored
    | some bytes =>
      rcases List.mem_cons.mp named with same | later
      · exact ⟨bytes, same ▸ firstRead⟩
      · cases tailRead : rest.mapM read with
        | none => simp [List.mapM_cons, firstRead, tailRead, Bind.bind, Option.bind] at stored
        | some tail => exact ih tailRead later

/-- Each run named by a loaded integrity manifest has a durable payload. -/
theorem _root_.Alvoki.Storage.SelectedIntegrityCheckpoint.runExists {runFiles binding checkpoint}
    (selected : SelectedIntegrityCheckpoint runFiles binding checkpoint)
    {bytes : ByteArray} {manifest : Manifest.IntegrityCheckpoint}
    (visible : binding = some bytes) (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok manifest)
    {index : Nat} (within : index < manifest.header.runCount.toNat) :
    ∃ payload, runFiles manifest.header.generation index = some payload := by
  cases selected with
  | absent => contradiction
  | @present actual checked files table accepted stored loaded =>
    cases visible
    cases Except.ok.inj (decoded.symm.trans accepted)
    exact storedRunExists stored (List.mem_range.mpr within)

/-- Canonical names for different run addresses are distinct. -/
theorem runPath_ne (directory : DiskDirectory) {left right : UInt64} {leftIndex rightIndex : Nat}
    (distinct : (left, leftIndex) ≠ (right, rightIndex)) :
    directory.file (.run left leftIndex) ≠ directory.file (.run right rightIndex) := by
  intro same
  have paths := congrArg FilePath.toString same
  change directory.path.toString ++ "/" ++ renderRunFileName left leftIndex =
    directory.path.toString ++ "/" ++ renderRunFileName right rightIndex at paths
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp paths
  have decoded := congrArg parseRunFileName names
  rw [parseRunFileName_render, parseRunFileName_render] at decoded
  exact distinct (Option.some.inj decoded)

/-- Project the visible and surviving canonical run names through the same
inode byte observations. A surviving map uses one reported binding map. -/
structure RunDirectoryInodeView (directory : DiskDirectory) (image : WalInodeImage) (runs : RunUnlinkImage) where
  visible : FilePath → Option Nat
  crashBindings : List (FilePath → Option Nat)
  visibleProjects : ∀ generation index inode,
    visible (directory.file (.run generation index)) = some inode →
    runs.visible generation index = some (image.visible inode)
  crashProjects : ∀ files ∈ runs.crashImages, ∃ bindings ∈ crashBindings,
    ∀ generation index inode, bindings (directory.file (.run generation index)) = some inode →
      files generation index ∈ (image.crashBytes inode).map some

/-- The selected path has one stable inode and one durable payload. -/
structure RunDirectoryInodeView.Stable {directory : DiskDirectory} {image : WalInodeImage}
    {runs : RunUnlinkImage} (view : RunDirectoryInodeView directory image runs)
    (path : FilePath) (inode : Nat) (bytes : ByteArray) : Prop where
  visibleBinding : view.visible path = some inode
  crashBinding : ∀ bindings ∈ view.crashBindings, bindings path = some inode
  visibleBytes : image.visible inode = bytes
  crashBytes : image.crashBytes inode = [bytes]

theorem RunDirectoryInodeView.Stable.guaranteed {directory : DiskDirectory} {image : WalInodeImage}
    {runs : RunUnlinkImage} {view : RunDirectoryInodeView directory image runs}
    {generation : UInt64} {index inode : Nat} {bytes : ByteArray}
    (stable : view.Stable (directory.file (.run generation index)) inode bytes) :
    runs.guaranteed generation index = some bytes := by
  have visible := (view.visibleProjects generation index inode stable.visibleBinding).trans
    (congrArg some stable.visibleBytes)
  have agree : ∀ files ∈ runs.crashImages, files generation index = runs.visible generation index := by
    intro files survives
    obtain ⟨bindings, bound, projects⟩ := view.crashProjects files survives
    have survived := projects generation index inode (stable.crashBinding bindings bound)
    simpa [stable.crashBytes, visible] using survived
  have all : runs.crashImages.all (fun files => decide (files generation index = runs.visible generation index)) = true :=
    List.all_eq_true.mpr (fun files member => decide_eq_true (agree files member))
  unfold RunUnlinkImage.guaranteed
  dsimp only
  rw [all]
  exact visible

/-- The no-follow observation and the descriptor's entry links use the
same inode namespace. For an absent path, the returned inode has no
entry-visible aliases. A present path is among the counted links. The link
census includes paths outside the database directory. -/
structure RunOpenLinkCensus {state : Type} {path : FilePath} {before : state}
    (lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (entry : FilePath → Option Nat) (inode : Nat) where
  links : List FilePath
  complete : ∀ other, other ∈ links ↔ entry other = some inode
  fresh : ∀ name message,
    lookup path before = .ok (.error (.noFileOrDirectory name 2 message)) before → links = []
  counted : ∀ metadata, lookup path before = .ok (.ok metadata) before →
    path ∈ links ∧ links.length = metadata.numLinks.toNat

theorem RunOpenLinkCensus.privateBinding {state : Type} {path : FilePath} {before : state}
    {lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata)}
    {entry : FilePath → Option Nat} {inode : Nat} (observed : RunOpenLinkCensus (path := path) (before := before) lookup entry inode)
    (guard : AcceptedRunGuard lookup path before) :
    ∀ other, entry other = some inode → other = path := by
  intro other bound
  have alias := (observed.complete other).mpr bound
  rcases guard with ⟨name, message, absent⟩ | ⟨metadata, found, _, privateLink⟩
  · rw [observed.fresh name message absent] at alias
    exact False.elim (List.not_mem_nil alias)
  · obtain ⟨canonical, count⟩ := observed.counted metadata found
    have one : observed.links.length = 1 := by rw [count, privateLink]; rfl
    obtain ⟨only, single⟩ := List.length_eq_one_iff.mp one
    rw [single] at alias canonical
    exact (List.mem_singleton.mp alias).trans (List.mem_singleton.mp canonical).symm

abbrev RunOpenLinkReports {handle : Type} {path : FilePath} {bytes : ByteArray}
    {before flushed : WalInodeImage} {descriptor : handle}
    (writes : RunWriteReports path bytes before flushed descriptor)
    (entry : FilePath → Option Nat) (inode : Nat) :=
  RunOpenLinkCensus (path := path) (before := before) writes.lookup entry inode

theorem RunOpenLinkReports.privateBinding {handle : Type} {path : FilePath} {bytes : ByteArray}
    {before flushed : WalInodeImage} {descriptor : handle}
    {writes : RunWriteReports path bytes before flushed descriptor}
    {entry : FilePath → Option Nat} {inode : Nat} (observed : RunOpenLinkReports writes entry inode) :
    ∀ other, entry other = some inode → other = path :=
  RunOpenLinkCensus.privateBinding observed writes.binding

/-- Effects of the run write and completed file sync. Other names retain
their visible binding, and each surviving binding map agrees with a prior
map away from the written path. The write and flush can affect the opened
inode's contents. -/
structure RunWriteInodeFrame {directory : DiskDirectory} {before after : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} (path : FilePath) (inode : Nat) (flushed : WalInodeImage)
    (entry : RunDirectoryInodeView directory before oldRuns)
    (reached : RunDirectoryInodeView directory after newRuns) : Prop where
  visibleNames : ∀ other, other ≠ path → reached.visible other = entry.visible other
  crashNames : ∀ bindings ∈ reached.crashBindings, ∃ prior ∈ entry.crashBindings,
    ∀ other, other ≠ path → bindings other = prior other
  visibleBytes : ∀ other, other ≠ inode → flushed.visible other = before.visible other
  crashBytes : ∀ other, other ≠ inode → flushed.crashBytes other = before.crashBytes other

/-- A write and file sync at a different private path preserve the reached
visible binding and payload. -/
theorem RunWriteInodeFrame.keepsVisible {directory : DiskDirectory} {before after : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {path held : FilePath} {inode oldInode : Nat}
    {bytes : ByteArray} {flushed : WalInodeImage}
    {entry : RunDirectoryInodeView directory before oldRuns}
    {reached : RunDirectoryInodeView directory after newRuns}
    (effect : RunWriteInodeFrame path inode flushed entry reached)
    (synced : after = flushed.completeFileSync inode)
    (privateBinding : ∀ other, entry.visible other = some inode → other = path)
    (different : held ≠ path) (bound : entry.visible held = some oldInode)
    (payload : before.visible oldInode = bytes) :
    oldInode ≠ inode ∧ reached.visible held = some oldInode ∧ after.visible oldInode = bytes := by
  have distinct : oldInode ≠ inode := by
    intro same
    apply different
    exact privateBinding held (same ▸ bound)
  refine ⟨distinct, (effect.visibleNames held different).trans bound, ?_⟩
  rw [synced]
  exact (effect.visibleBytes oldInode distinct).trans payload

/-- The same frame also preserves each durable binding and payload. -/
theorem RunWriteInodeFrame.keepsStable {directory : DiskDirectory} {before after : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {path held : FilePath} {inode oldInode : Nat}
    {bytes : ByteArray} {flushed : WalInodeImage}
    {entry : RunDirectoryInodeView directory before oldRuns}
    {reached : RunDirectoryInodeView directory after newRuns}
    (effect : RunWriteInodeFrame path inode flushed entry reached)
    (synced : after = flushed.completeFileSync inode)
    (privateBinding : ∀ other, entry.visible other = some inode → other = path)
    (different : held ≠ path) (stable : entry.Stable held oldInode bytes) :
    reached.Stable held oldInode bytes := by
  obtain ⟨distinct, binding, bytes⟩ :=
    effect.keepsVisible synced privateBinding different stable.visibleBinding stable.visibleBytes
  refine ⟨binding, ?_, bytes, ?_⟩
  · intro bindings survives
    obtain ⟨prior, possible, preserved⟩ := effect.crashNames bindings survives
    exact (preserved held different).trans (stable.crashBinding prior possible)
  · rw [synced]
    simp [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, distinct,
      effect.crashBytes oldInode distinct, stable.crashBytes]

/-- The same returned pair that records the written bytes also frames the
other names and inodes. Its selected inode has had a complete file sync. -/
structure CheckpointRunPairCustody {handle : Type} (directory : DiskDirectory)
    (generation : UInt64) (table : PackedTable) (perform : Step → EStateM IO.Error (Cache handle × WalInodeImage) Unit)
    (before after : Cache handle × WalInodeImage) {entryRuns reachedRuns : RunUnlinkImage}
    (entry : RunDirectoryInodeView directory before.2 entryRuns)
    (reached : RunDirectoryInodeView directory after.2 reachedRuns) (index : Nat) where
  run : Compaction.CheckedRun
  selected : table.runs.toArray[index]? = some run
  returned : (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) before = .ok () after
  flushed : WalInodeImage
  inode : Nat
  synced : after.2 = flushed.completeFileSync inode
  bound : reached.visible (directory.file (.run generation index)) = some inode
  bytes : flushed.visible inode = run.run.bytes
  privateBinding : ∀ other, entry.visible other = some inode → other = directory.file (.run generation index)
  frame : RunWriteInodeFrame (directory.file (.run generation index)) inode flushed entry reached

/-- Build the prefix report from the no-follow guard and the exact cached
write, flush and file-sync callbacks on the returned descriptor. -/
noncomputable def CheckpointRunPairCustody.ofObservedWrite
    (directory : DiskDirectory) (generation : UInt64) (table : PackedTable) (manifest : ByteArray)
    {index : Nat} {run : Compaction.CheckedRun} (selected : table.runs.toArray[index]? = some run)
    (cache : Cache (DescriptorInventory × DescriptorSlot)) {before flushed : WalInodeImage}
    (inventory : DescriptorInventory) (slot : DescriptorSlot)
    (writes : RunWriteReports (directory.file (.run generation index)) run.run.bytes before flushed (inventory, slot))
    (writeStage : FilePath → ByteArray → EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage) Unit)
    (rename : FilePath → FilePath → EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage) Unit)
    (openRead : FilePath → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot))
    (fsync : (DescriptorInventory × DescriptorSlot) → EStateM IO.Error WalInodeImage Unit)
    (drops : List LockReferenceDrop)
    (issuing : slot.reference ∈ (inventory.afterDrops drops).references slot.description)
    {entryRuns reachedRuns : RunUnlinkImage}
    (entry : RunDirectoryInodeView directory before entryRuns)
    (reached : RunDirectoryInodeView directory (flushed.completeFileSync (inventory.inode slot.description)) reachedRuns)
    (links : RunOpenLinkReports writes entry.visible (inventory.inode slot.description))
    (flushedBindings : FilePath → Option Nat) :
    let path := directory.file (.run generation index)
    let captured := (inventory, slot)
    let inode := inventory.inode slot.description
    let after := (cache.consume path, flushed.completeFileSync inode)
    let writeRun := fun path bytes => stageFreshWithCache path bytes
      (fun path bytes => writeCheckpointRunWith writes.lookup writes.openWrite writes.write writes.flush path bytes pure)
    let perform := performCheckpointFileStep directory generation table.runs.toArray (directory.file .stagedManifest)
      manifest (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    RunWriteInodeFrame path inode flushed entry reached →
    flushedBindings path = some inode → reached.visible = flushedBindings →
    flushed.visible inode = run.run.bytes →
    fsync captured flushed = .ok () after.2 →
    CheckpointRunPairCustody directory generation table perform (cache, before) after entry reached index := by
  intro path captured inode after writeRun perform frame bound unchanged bytes synced
  have effect : FsyncResult flushed (flushed.completeFileSync inode) true (fsync captured flushed) := by
    rw [synced]
    exact .completed
  have observed := performCheckpointRunPair_observed directory generation table manifest selected cache inventory slot
    writes writeStage rename openRead fsync drops issuing flushedBindings bound bytes effect
  exact ⟨run, selected, observed.2.2.2.1 after.2 synced, flushed, inode, rfl, unchanged ▸ bound,
    bytes, links.privateBinding, frame⟩

end Alvoki.Storage.CheckpointPublication
