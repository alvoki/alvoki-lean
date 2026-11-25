import Alvoki.Storage.Disk.WalCollectionPreflight
import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System

private def walCollectionFileCall {image result : Type} (call : EStateM IO.Error image result) :
    EStateM IO.Error (Phase Installed × LockedFileState image) result := fun (phase, before) =>
  match call before.image with
  | .ok value reached => .ok value (phase, { before with image := reached })
  | .error cause reached => .error cause (phase, { before with image := reached })

namespace WalCollectionReads

variable {image : Type}

/-- Interpret the mutation suffix of `DiskTable.collectCoveredWal_fileEffects`
using the reached cache and files. The planner runs before the phase change. -/
def collectWithEffects (calls : WalCollectionReads) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error image Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit := fun initial =>
  calls.collectAfterPlan directory (fun offsets =>
    let setPhase := fun phase => modify (fun state : Phase Installed × LockedFileState image => (phase, state.2))
    publishPrepared setPhase
      (RunCollection.run offsets (RunCollection.performPaths (fun path => walCollectionFileCall (removeFile path))
        (fun path => walCollectionFileCall (syncDirectory path)) throw
        (fun first => directory.file (.walSegment first)) directory.path))
      (setPhase initial.1)) initial

/-- With a nonempty successful plan, the production suffix begins by
calling unlink at its first canonical path with the original files and
owner. This equation does not require that unlink to return successfully. -/
theorem collectWithEffects_first (calls : WalCollectionReads) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error image Unit)
    (installed : Installed) (before : LockedFileState image) {first : Nat} {rest : List Nat}
    (planned : calls.plan directory installed = .ok (first :: rest)) :
    calls.collectWithEffects directory removeFile syncDirectory (.ready installed, before) =
      (do
        let result ← walCollectionFileCall (removeFile (directory.file (.walSegment first)))
        liftExcept (RunCollection.ownedUnlinkResult result)
        RunCollection.run rest (RunCollection.performPaths (fun path => walCollectionFileCall (removeFile path))
          (fun path => walCollectionFileCall (syncDirectory path)) throw
          (fun offset => directory.file (.walSegment offset)) directory.path)
        modify (fun state : Phase Installed × LockedFileState image => (.ready installed, state.2)))
      (.poisoned, before) := by
  simp only [collectWithEffects, collectAfterPlan, Bind.bind, EStateM.bind, runPlan_ready, planned,
    publishPrepared, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [RunCollection.run, RunCollection.steps, List.map_cons, List.cons_append,
    List.forM_eq_forM, List.forM_cons, RunCollection.performPaths, Bind.bind, EStateM.bind, liftExcept]
  cases issued : removeFile (directory.file (.walSegment first)) before.image with
  | error cause reached => simp [walCollectionFileCall, issued]
  | ok result reached =>
    cases returned : RunCollection.ownedUnlinkResult result with
    | error cause => simp [walCollectionFileCall, issued, returned, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | ok value =>
      cases value
      simp [walCollectionFileCall, issued, returned, Pure.pure, EStateM.pure]

/-- The result from the first callback either stops before the tail or
starts that exact tail from the reached files, under the original owner. -/
theorem collectWithEffects_afterFirst (calls : WalCollectionReads) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error image Unit)
    (installed : Installed) (before : LockedFileState image) {first : Nat} {rest : List Nat}
    (planned : calls.plan directory installed = .ok (first :: rest))
    {result : Except IO.Error Unit} {reached : image}
    (returned : removeFile (directory.file (.walSegment first)) before.image = .ok result reached) :
    calls.collectWithEffects directory removeFile syncDirectory (.ready installed, before) =
      match RunCollection.ownedUnlinkResult result with
      | .error cause => .error cause (.poisoned, {before with image := reached})
      | .ok () =>
        (do
          RunCollection.run rest (RunCollection.performPaths (fun path => walCollectionFileCall (removeFile path))
            (fun path => walCollectionFileCall (syncDirectory path)) throw
            (fun offset => directory.file (.walSegment offset)) directory.path)
          modify (fun state : Phase Installed × LockedFileState image => (.ready installed, state.2)))
          (.poisoned, {before with image := reached}) := by
  rw [calls.collectWithEffects_first directory removeFile syncDirectory installed before planned]
  cases accepted : RunCollection.ownedUnlinkResult result with
  | error cause =>
    simp [Bind.bind, EStateM.bind, walCollectionFileCall, returned, liftExcept, accepted, throw,
      throwThe, MonadExceptOf.throw, EStateM.throw]
  | ok value =>
    cases value
    simp [Bind.bind, EStateM.bind, walCollectionFileCall, returned, liftExcept, accepted, Pure.pure, EStateM.pure]

end WalCollectionReads

/-- The first selected WAL name resolved at the no-follow probe and at
the issued unlink's own lookup before any effect. Stability concerns
just this binding in the same resolved parent. An unlink rejected before
lookup needs no such report. -/
structure WalSealUnlinkResolution (calls : WalCollectionReads) (directory : DiskDirectory) (first : Nat) where
  root : DeviceInode
  statView : DirectoryReadNamespace
  unlinkView : DirectoryReadNamespace
  statChild : RunChildLookup root (renderWalSegmentName first) statView
  unlinkPath : FilePath
  canonicalUnlink : unlinkPath = directory.file (.walSegment first)
  unlinkChild : RunChildLookup root (renderWalSegmentName first) unlinkView
  stat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  metadata : IO.FS.Metadata
  statReturned : stat (directory.file (.walSegment first)) = .ok (metadata, statChild.child)
  projection : calls.paths.lstat (directory.file (.walSegment first)) =
    (stat (directory.file (.walSegment first))).map Prod.fst
  stable : unlinkView.child root (renderWalSegmentName first) = statView.child root (renderWalSegmentName first)

theorem WalSealUnlinkResolution.sameChild {calls : WalCollectionReads} {directory : DiskDirectory} {first : Nat}
    (resolved : WalSealUnlinkResolution calls directory first) :
    resolved.unlinkChild.child = resolved.statChild.child := by
  have bound := resolved.statChild.binds
  rw [resolved.statChild.atRoot, resolved.statChild.atName] at bound
  exact resolved.unlinkChild.child_eq (resolved.stable.trans bound)

/-- The first issued unlink takes the canonical path of an eligible seal.
When the primitive report describes this invocation's lookup, the
reported child equals the one measured by the planner's no-follow probe.
The invocation can fail before a lookup or effect is observed. -/
theorem SegmentedWriterState.RetainedReady.firstObservedWalUnlink
    {image : Type} {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) (calls : WalCollectionReads)
    (manifest : calls.paths.readOptional (directory.file .manifest) = .ok before.target.pair.manifest)
    (marker : calls.paths.readOptional (directory.file .walBoundary) = .ok before.target.pair.walBoundary)
    {entries : Array IO.FS.DirEntry} (listed : calls.list directory.path = .ok entries)
    {extents : List (Nat × IO.FS.Metadata)}
    (scan : readWalSegmentExtentsWith directory calls.inspect (entries.toList.map (·.fileName)) = .ok extents)
    (checked : checkWalCollectionInventory extents before.installed.activeFirst before.target.range = true)
    (sealedAt : ∀ entry ∈ extents, entry.1 ≠ before.wal.active.first →
      ∃ segment ∈ before.wal.sealed, segment.first = entry.1)
    (physical : ∀ entry ∈ extents, ∀ segment ∈ before.wal.sealed, segment.first = entry.1 →
      entry.2.byteSize.toNat = segment.bytes.size)
    {first : Nat} {rest : List Nat}
    (head : walCollectionOffsetsFromExtents extents before.installed.activeFirst before.target.range = first :: rest)
    (resolved : WalSealUnlinkResolution calls directory first)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error image Unit) (files : image) :
    calls.plan directory before.installed = .ok (first :: rest) ∧
      first ∈ before.wal.collectionOffsets ∧
      (first, resolved.metadata) ∈ extents ∧
      resolved.metadata.type = .file ∧ resolved.metadata.numLinks = 1 ∧
      resolved.unlinkChild.child = resolved.statChild.child ∧
      calls.collectWithEffects directory removeFile syncDirectory (.ready before.installed, ⟨files, before.owners⟩) =
        (do
          let result ← walCollectionFileCall (removeFile resolved.unlinkPath)
          liftExcept (RunCollection.ownedUnlinkResult result)
          RunCollection.run rest (RunCollection.performPaths (fun path => walCollectionFileCall (removeFile path))
            (fun path => walCollectionFileCall (syncDirectory path)) throw
            (fun offset => directory.file (.walSegment offset)) directory.path)
          modify (fun state : Phase Installed × LockedFileState image => (.ready before.installed, state.2)))
        (.poisoned, ⟨files, before.owners⟩) := by
  obtain ⟨planned, approved⟩ := ready.planObservedWalCollection calls manifest marker listed scan checked sealedAt physical
  rw [head] at planned approved
  have selected : first ∈ walCollectionOffsetsFromExtents extents before.installed.activeFirst before.target.range := by
    rw [head]
    exact List.mem_cons_self
  obtain ⟨_, metadata, _, member, accepted⟩ := walCollectionOffsetsFromExtents_observed selected
  have inspected := readWalSegmentExtentsWith_metadata scan member
  have raw : calls.paths.lstat (directory.file (.walSegment first)) = .ok resolved.metadata := by
    rw [resolved.projection, resolved.statReturned]
    rfl
  have same : resolved.metadata = metadata := by
    simp only [WalCollectionReads.inspect, raw, inspectWalSegmentWith, Bind.bind, Except.bind] at inspected
    by_cases kind : (resolved.metadata.type == .file) = true <;> by_cases privateFile : resolved.metadata.numLinks = 1 <;>
      simp_all [checkPrivateRegularWith, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  obtain ⟨kind, links, _⟩ := walCollectionEnd_covered before.target.decoded accepted
  refine ⟨planned, approved first List.mem_cons_self, same.symm ▸ member, same ▸ kind, same ▸ links,
    resolved.sameChild, ?_⟩
  rw [resolved.canonicalUnlink]
  exact calls.collectWithEffects_first directory removeFile syncDirectory before.installed ⟨files, before.owners⟩ planned

end Alvoki.Storage.DiskSession
