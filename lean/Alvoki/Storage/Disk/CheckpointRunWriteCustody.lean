import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.StagedHandleCustody
import Alvoki.Storage.Disk.ReplacedWalDescriptor
import Alvoki.Storage.Disk.DescriptorInventory

namespace Alvoki.Storage.CheckpointPublication

open System DiskSession SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- Project bytes known to be synced through one canonical run binding.
An absent result carries no claim of pathname absence. A visible object
whose data has several crash choices also has no known synced payload. -/
def knownSyncedRunBytes (directory : DiskDirectory) (bindings : FilePath → Option Nat)
    (image : WalInodeImage) (generation : UInt64) (index : Nat) : Option ByteArray := do
  let inode ← bindings (directory.file (.run generation index))
  let visible := image.visible inode
  if image.crashBytes inode = [visible] then some visible else none

/-- A complete sync settles the bytes of one inode. A separate observed
pathname binding identifies which run address can use those bytes. -/
theorem knownSyncedRunBytes_ofFileSync {directory : DiskDirectory} {bindings : FilePath → Option Nat}
    {generation : UInt64} {index inode : Nat} {flushed : WalInodeImage} {bytes : ByteArray}
    (bound : bindings (directory.file (.run generation index)) = some inode)
    (visible : flushed.visible inode = bytes) :
    knownSyncedRunBytes directory bindings (flushed.completeFileSync inode) generation index = some bytes := by
  simp [knownSyncedRunBytes, bound, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync,
    visible, Bind.bind, Option.bind]

/-- The no-follow guard leaves the state unchanged and admits either
an absent name or a regular file with exactly one link. -/
def AcceptedRunGuard {state : Type}
    (lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (path : FilePath) (before : state) : Prop :=
  (∃ name message, lookup path before = .ok (.error (.noFileOrDirectory name 2 message)) before) ∨
  ∃ metadata, lookup path before = .ok (.ok metadata) before ∧ metadata.type = .file ∧ metadata.numLinks = 1

/-- The open, write and flush observations for one reached checkpoint run.
The optional no-follow lookup admits an absent or private regular name.
Each subsequent callback uses the description returned by the actual open. -/
structure RunWriteReports {handle state : Type} (path : FilePath) (bytes : ByteArray)
    (before flushed : state) (descriptor : handle) where
  lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata)
  openWrite : FilePath → EStateM IO.Error state handle
  write : handle → ByteArray → EStateM IO.Error state Unit
  flush : handle → EStateM IO.Error state Unit
  binding : AcceptedRunGuard lookup path before
  afterOpen : state
  afterWrite : state
  opened : openWrite path before = .ok descriptor afterOpen
  written : write descriptor bytes afterOpen = .ok () afterWrite
  returned : flush descriptor afterWrite = .ok () flushed

theorem RunWriteReports.captures {handle state : Type} {path : FilePath} {bytes : ByteArray}
    {before flushed : state} {descriptor : handle} (reports : RunWriteReports path bytes before flushed descriptor) :
    writeCheckpointRunWith reports.lookup reports.openWrite reports.write reports.flush path bytes pure before =
      .ok descriptor flushed := by
  rcases reports.binding with ⟨_, _, absent⟩ | ⟨metadata, present, regular, privateFile⟩
  · simp [writeCheckpointRunWith, optionalMetadataWith, absent, reports.opened, reports.written,
      reports.returned, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  · have fileKind : (IO.FS.FileType.file == .file) = true := rfl
    simp [writeCheckpointRunWith, optionalMetadataWith, checkPrivateRegularWith, present, regular,
      privateFile, fileKind, reports.opened, reports.written, reports.returned,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

private theorem runPath_ne_directory (directory : DiskDirectory) (generation : UInt64) (index : Nat) :
    directory.file (.run generation index) ≠ directory.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ _).length = directory.path.toString.length at length
  simp only [String.length_append] at length
  have slash : "/".length = 1 := rfl
  omega

/-- Every selected run reaches its write and file barrier consecutively,
before the directory and manifest steps. -/
theorem steps_split_runPair {count index : Nat} (within : index < count) :
    ∃ prior later, steps count = prior ++ [.writeRun index, .syncRun index] ++ later := by
  obtain ⟨prior, later, order⟩ := List.append_of_mem (List.mem_range.mpr within)
  exact ⟨prior.flatMap (fun i => [.writeRun i, .syncRun i]),
    later.flatMap (fun i => [.writeRun i, .syncRun i]) ++ [.syncRunsDirectory] ++ Publication.steps.map Step.manifest,
    by simp [steps, runSteps, order, List.append_assoc]⟩

/-- Route the adjacent checked run steps to the handle captured by the
same write. A returned fsync error still consumes that pending entry. -/
theorem performCheckpointRunPair_route
    (directory : DiskDirectory) (generation : UInt64) (table : PackedTable) (manifest : ByteArray)
    {index : Nat} {run : Compaction.CheckedRun} (selected : table.runs.toArray[index]? = some run)
    {handle : Type} (cache : Cache handle) {before flushed : WalInodeImage} (captured : handle)
    (writeRun writeStage : FilePath → ByteArray → EStateM IO.Error (Cache handle × WalInodeImage) Unit)
    (rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WalInodeImage) Unit)
    (openRead : FilePath → EStateM IO.Error WalInodeImage handle)
    (fsync : handle → EStateM IO.Error WalInodeImage Unit) :
    let path := directory.file (.run generation index)
    let perform := performCheckpointFileStep directory generation table.runs.toArray (directory.file .stagedManifest)
      manifest (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    writeRun path run.run.bytes (cache, before) = .ok () (cache.remember path captured, flushed) →
    ((perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (cache, before)) =
      match fsync captured flushed with
      | .ok () after => .ok () (cache.consume path, after)
      | .error cause after => .error (IO.userError s!"sync failed for '{path}': {cause}") (cache.consume path, after) := by
  intro path perform staged
  have route := syncRemembered (dir := directory.path) (path := path) (cache := cache)
    (runPath_ne_directory directory generation index) captured openRead fsync flushed
  have wrote : perform (.writeRun index) (cache, before) = .ok () (cache.remember path captured, flushed) := by
    simpa only [perform, performCheckpointFileStep, selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      using staged
  change ((perform (.writeRun index) >>= fun _ => SyncPathGroup.run (sync directory.path openRead fsync) #[path])
    (cache, before)) = _
  simp only [Bind.bind, EStateM.bind, wrote, SyncPathGroup.run_single, route]
  cases fsync captured flushed <;> rfl

/-- At the selected run's two adjacent dispatch steps, use exactly the
checked array bytes and sync the live description used to write and flush
them. The file barrier consumes its pending entry even on error. A
reported complete effect makes just the selected payload durable on that
inode. Its directory binding is settled by the subsequent directory step. -/
theorem performCheckpointRunPair_observed
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
    (bindings : FilePath → Option Nat) :
    let path := directory.file (.run generation index)
    let captured := (inventory, slot)
    let inode := inventory.inode slot.description
    let persist := fun inode (state : WalInodeImage) => state.completeFileSync inode
    let writeRun := fun path bytes => stageFreshWithCache path bytes
      (fun path bytes => writeCheckpointRunWith writes.lookup writes.openWrite writes.write writes.flush path bytes pure)
    let perform := performCheckpointFileStep directory generation table.runs.toArray (directory.file .stagedManifest)
      manifest (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    bindings path = some inode →
    flushed.visible inode = run.run.bytes →
    ∀ {effective : Bool}, FsyncResult flushed (persist inode flushed) effective (fsync captured flushed) →
      (∃ prior later, steps table.runs.length = prior ++ [.writeRun index, .syncRun index] ++ later) ∧
      (∃ observed : FsyncObservation (fun handle => handle.2.description)
          (fun handle => handle.1.inode handle.2.description) captured flushed persist (fsync captured flushed),
        observed.issuer = slot.reference ∧ observed.effective = effective ∧ bindings path = some observed.effectInode) ∧
      FsyncResult (cache.consume path, flushed) (cache.consume path, persist inode flushed) effective
        ((perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (cache, before)) ∧
      (∀ after, fsync captured flushed = .ok () after →
        (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (cache, before) =
          .ok () (cache.consume path, after)) ∧
      (persist inode flushed).crashBytes inode = [run.run.bytes] := by
  intro path captured inode persist writeRun perform bound visible effective effect
  let observed := FsyncObservation.ofInventory inventory drops
    (fun handle => handle.2.description) (fun handle => handle.1.inode handle.2.description)
    captured slot.reference issuing rfl flushed persist (effective := effective) effect
  have within : index < table.runs.length := by
    rw [List.getElem?_toArray] at selected
    by_cases within : index < table.runs.length
    · exact within
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt within)] at selected
      contradiction
  have staged : writeRun path run.run.bytes (cache, before) = .ok () (cache.remember path captured, flushed) := by
    have capturedRun := writes.captures
    change writeCheckpointRunWith writes.lookup writes.openWrite writes.write writes.flush path run.run.bytes
        pure before = .ok captured flushed at capturedRun
    simp only [writeRun, stageFreshWithCache, capturedRun]
  have routed := performCheckpointRunPair_route directory generation table manifest selected cache captured
    writeRun writeStage rename openRead fsync staged
  refine ⟨steps_split_runPair within, ⟨observed, rfl, rfl, bound⟩, ?_, ?_, ?_⟩
  · rw [routed]
    generalize fsync captured flushed = returned at effect ⊢
    cases effect <;> constructor
  · intro after complete
    rw [routed, complete]
  · simp [persist, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, visible]

end Alvoki.Storage.CheckpointPublication
