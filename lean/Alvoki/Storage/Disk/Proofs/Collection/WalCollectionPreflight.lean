import Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Interpret the exact read-only operands of the public planner and of
the collector before poisoning. No run or WAL payload is opened. -/
structure WalCollectionReads where
  paths : OpenPathReadReports
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)

def WalCollectionReads.inspect (calls : WalCollectionReads) (path : FilePath) :
    Except IO.Error (Except IO.Error IO.FS.Metadata) :=
  inspectWalSegmentWith path (.ok (calls.paths.lstat path))

def WalCollectionReads.plan (calls : WalCollectionReads) (directory : DiskDirectory) (state : Installed) :
    Except IO.Error (List Nat) :=
  planWalCollectionWith directory state.generation state.walBytes state.activeFirst
    calls.paths.readOptional calls.list calls.inspect

/-- A successful checked scan yields the exact selected offsets. Reported
nonkeeper extents denote the visible sealed files and their actual sizes.
Soundness of this plan only needs those reached extents. Equality with
the full plan additionally needs coverage of the whole sealed inventory. -/
theorem SegmentedWriterState.RetainedReady.planObservedWalCollection
    {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor)
    (calls : WalCollectionReads)
    (manifest : calls.paths.readOptional (directory.file .manifest) = .ok before.target.pair.manifest)
    (marker : calls.paths.readOptional (directory.file .walBoundary) = .ok before.target.pair.walBoundary)
    {entries : Array IO.FS.DirEntry} (listed : calls.list directory.path = .ok entries)
    {extents : List (Nat × IO.FS.Metadata)}
    (scan : readWalSegmentExtentsWith directory calls.inspect (entries.toList.map (·.fileName)) = .ok extents)
    (checked : checkWalCollectionInventory extents before.installed.activeFirst before.target.range = true)
    (sealedAt : ∀ entry ∈ extents, entry.1 ≠ before.wal.active.first →
      ∃ segment ∈ before.wal.sealed, segment.first = entry.1)
    (physical : ∀ entry ∈ extents, ∀ segment ∈ before.wal.sealed, segment.first = entry.1 →
      entry.2.byteSize.toNat = segment.bytes.size) :
    let offsets := walCollectionOffsetsFromExtents extents before.installed.activeFirst before.target.range
    calls.plan directory before.installed = .ok offsets ∧
      ∀ first ∈ offsets, first ∈ before.wal.collectionOffsets := by
  have generation := SelectedIntegrityCheckpoint.collectionGeneration ready.resumed.selected
  dsimp only at generation
  rw [← ready.resumed.generation] at generation
  have count : before.installed.walBytes = before.target.range.through * WAL.frameSize := by
    rw [ready.resumed.bytes, ready.resumed.through, WAL.encode_size, Nat.mul_comm]
  have pair : DirectoryPublication.Bindings.mk before.target.pair.manifest before.target.pair.walBoundary =
      before.target.pair := by cases before.target.pair; rfl
  have keeper := ready.resumed.keeper.trans ready.active
  have decoded : before.wal.directory.active.walRange = some before.target.range := by
    rw [ready.walPair]
    exact before.target.decoded
  constructor
  · unfold WalCollectionReads.plan planWalCollectionWith
    simp only [Bind.bind, Except.bind, manifest, marker, generation, Except.mapError, liftExcept,
      Pure.pure, Except.pure]
    rw [pair, before.target.decoded]
    simp only [count, ↓reduceIte, listed, scan, checked]
  · intro first member
    have chosen := walCollectionOffsetsFromExtents_approved ready.layout ready.walDirectorySettled decoded
      sealedAt physical ready.spans (by simpa only [keeper] using member)
    obtain ⟨segment, visible, starts⟩ := chosen.1
    exact List.mem_map.mpr ⟨segment,
      List.mem_filter.mpr ⟨visible, WalSegmentImage.canRemove_iff.mpr (chosen.2 segment visible starts)⟩, starts⟩

/-- The native plan reads the phase first, then evaluates the same planner
with the reports above. Its projected phase, files, cache and owner are read-only. -/
def WalCollectionReads.runPlan {image : Type} (calls : WalCollectionReads) (directory : DiskDirectory) :
    EStateM IO.Error (Phase Installed × LockedFileState image) (List Nat) := fun before =>
  let result : Except IO.Error (List Nat) := do
    let state ← before.1.installed
    calls.plan directory state
  match result with
  | .ok offsets => .ok offsets before
  | .error cause => .error cause before

/-- In `DiskTable.collectCoveredWal_fileEffects` the suffix starts with the
poisoned phase write. It is reached only after the shared plan returns. -/
def WalCollectionReads.collectAfterPlan {image : Type} (calls : WalCollectionReads) (directory : DiskDirectory)
    (dispatch : List Nat → EStateM IO.Error (Phase Installed × LockedFileState image) Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit := do
  let offsets ← calls.runPlan directory
  dispatch offsets

theorem WalCollectionReads.runPlan_ready {image : Type} (calls : WalCollectionReads) (directory : DiskDirectory)
    (installed : Installed) (files : LockedFileState image) :
    calls.runPlan directory (.ready installed, files) =
      match calls.plan directory installed with
      | .ok offsets => .ok offsets (.ready installed, files)
      | .error cause => .error cause (.ready installed, files) := rfl

/-- A rejected ready call keeps the same cache, physical files and owned
session. The original read and submission records retain their replay.
The collector's mutating suffix is unreachable for this rejected plan. -/
theorem SegmentedClientReadTrace.walCollectionRejected {cache : Type}
    {initialDescriptor : Nat} {before : SegmentedWriterState} (session : SegmentedSession)
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns session.directory initialDescriptor)
    (trace : SegmentedClientReadTrace session.directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads session.descriptor before)
    (phase : session.phase = .ready before.installed)
    (calls : WalCollectionReads) {cause : IO.Error}
    (rejected : calls.plan session.directory before.installed = .error cause)
    (cached : cache)
    (dispatch : List Nat → EStateM IO.Error (Phase Installed × LockedFileState (cache × FileImage)) Unit) :
    let initial := (session.phase, (⟨(cached, before.files), before.owners⟩ : LockedFileState (cache × FileImage)))
    calls.runPlan session.directory initial = .error cause initial ∧
      calls.collectAfterPlan session.directory dispatch initial = .error cause initial ∧
      GuardedClientReplay log reads before session := by
  dsimp only
  have planner : calls.runPlan session.directory (session.phase, ⟨(cached, before.files), before.owners⟩) =
      .error cause (session.phase, ⟨(cached, before.files), before.owners⟩) := by
    rw [phase, WalCollectionReads.runPlan_ready, rejected]
  exact ⟨planner, by simp only [WalCollectionReads.collectAfterPlan, Bind.bind, EStateM.bind, planner],
    trace.guardedReplay bootstrap held phase⟩

end Alvoki.Storage.DiskSession
