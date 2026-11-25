import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeFileEffectProjection

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit

/-- A write can allocate and retire WAL descriptors. The existing lock
and cached directory must keep their slots and object identities. -/
structure RawWriteAuthority where
  directory : Option CheckpointOpenHandle
  ownerLive : Prop
  directoryLive : Prop
  ownerInode : Nat
  directoryInode : Nat

/-- The protected reference and descriptor projection of a raw heap. -/
def OpenCloseHeapView.writeAuthorityAt {heap image : Type} (view : OpenCloseHeapView heap image)
    (state : NativeReadyState) (directory : IO.Ref (Option IO.FS.Handle)) (reached : heap) : RawWriteAuthority :=
  let census := view.descriptors reached
  ⟨(view.directory reached directory).map (view.handle reached), state.owner ∈ census.slots,
    state.directorySlot ∈ census.slots, census.inode state.owner.description,
    census.inode state.directorySlot.description⟩

/-- Preserve the authority observation across the actual append-first
commit. The callback laws cover the reached heap on errors as well as
successes, so a failure requires no report of a later callback. -/
theorem commitBytesAt_keepsAuthority {heap footprint : Type} (observe : heap → footprint)
    (directory : DiskDirectory) (first : Nat) (bytes : ByteArray) (count : Nat)
    (append stage : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (appendKeeps : ∀ before, observe (reachedState (append (directory.file (.walSegment first)) bytes before)) =
      observe before)
    (stageKeeps : ∀ before, observe (reachedState
      (stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64) before)) = observe before)
    (pairedSyncKeeps : ∀ before, observe (reachedState
      (sync #[directory.file (.walSegment first), directory.file .stagedWalBoundary] before)) = observe before)
    (renameKeeps : ∀ before, observe (reachedState
      (rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) before)) = observe before)
    (rootSyncKeeps : ∀ before, observe (reachedState (sync #[directory.path] before)) = observe before)
    (before : heap) :
    observe (reachedState (commitBytesAt directory first bytes count append stage sync rename before)) = observe before := by
  have sameReached (result : EStateM.Result IO.Error heap Unit) :
      NativeFileEffectProjection.reached result = reachedState result := by cases result <;> rfl
  have framed (action : EStateM IO.Error heap Unit)
      (keeps : ∀ atHeap, observe (reachedState (action atHeap)) = observe atHeap) :
      NativeFileEffectProjection id observe action action := by
    intro atHeap
    refine ⟨?_, ?_⟩
    · change NativeFileEffectProjection.result id (action atHeap) = action atHeap
      cases action atHeap <;> rfl
    · simpa only [sameReached] using keeps atHeap
  rw [commitBytesAt_fileEffects, WAL.Boundary.commit]
  have commits := (framed _ appendKeeps).bind fun _ =>
    (framed _ stageKeeps).bind fun _ =>
      (framed _ pairedSyncKeeps).bind fun _ =>
        (framed _ renameKeeps).bind fun _ =>
          (framed _ rootSyncKeeps).bind fun _ => NativeFileEffectProjection.pure id observe ()
  simpa only [sameReached] using (commits before).2

/-- Recover the existing pending-write census from the raw returned
heap. The original literal directory cell supplies the capture. Its
bound root and the prior selected root identify the cached inode. The
local authority and protected-file frames carry these facts through the
write without constraining unrelated slots or requiring an entire report. -/
def NativePendingWriteCensus.ofRawAuthority {heap image : Type} {state : NativeReadyState}
    {files : DiskTable.OpenSyncFiles} (view : OpenCloseHeapView heap image)
    (refs : OpenSyncCacheRefs files state.session.directory.path)
    {entry returned : heap} (valid : state.Valid)
    (entryCensus : view.descriptors entry = state.census)
    (entryCache : view.cacheAt entry refs.directory refs.active refs.pending = state.cache)
    (authority : view.writeAuthorityAt state refs.directory returned = view.writeAuthorityAt state refs.directory entry)
    {initial reached : CheckpointSurvivingFiles} (initialStorage : NativeReadyProtectedStorage state initial)
    (root : ∀ literal, view.directory entry refs.directory = some literal →
      initial.names state.session.directory.path =
        some ((view.handle entry literal).1.inode (view.handle entry literal).2.1.description))
    (kept : initial.Frames state.writeFramePath reached) :
    NativePendingWriteCensus state (view.cacheAt returned refs.directory refs.active refs.pending) := by
  have liveOwner : state.owner ∈ (view.descriptors returned).slots := by
    rw [show (state.owner ∈ (view.descriptors returned).slots) = (state.owner ∈ (view.descriptors entry).slots) from
      congrArg RawWriteAuthority.ownerLive authority, entryCensus]
    exact valid.ownerLive
  have liveDirectory : state.directorySlot ∈ (view.descriptors returned).slots := by
    rw [show (state.directorySlot ∈ (view.descriptors returned).slots) = (state.directorySlot ∈ (view.descriptors entry).slots) from
      congrArg RawWriteAuthority.directoryLive authority, entryCensus]
    exact valid.directoryLive
  have ownerInode : (view.descriptors returned).inode state.owner.description = state.census.inode state.owner.description :=
    (congrArg RawWriteAuthority.ownerInode authority).trans (congrArg (fun census => census.inode state.owner.description) entryCensus)
  have directoryInode :
      (view.descriptors returned).inode state.directorySlot.description = state.census.inode state.directorySlot.description :=
    (congrArg RawWriteAuthority.directoryInode authority).trans
      (congrArg (fun census => census.inode state.directorySlot.description) entryCensus)
  have cached : (view.cacheAt returned refs.directory refs.active refs.pending).directory =
      (view.cacheAt entry refs.directory refs.active refs.pending).directory :=
    congrArg RawWriteAuthority.directory authority
  have protectedAfter := initialStorage.frame kept
  let captured := ((view.directory entry refs.directory).map fun literal => (view.handle entry literal).1).getD state.census
  have capturedRoot :
      (view.cacheAt entry refs.directory refs.active refs.pending).directory = some (captured, state.directorySlot, 0) ∧
      captured.inode state.directorySlot.description = state.census.inode state.directorySlot.description := by
    obtain ⟨atOpen, expected⟩ := valid.captured
    have sameHandle := (congrArg Cache.directory entryCache).trans expected
    cases found : view.directory entry refs.directory with
    | none => simp [OpenCloseHeapView.cacheAt, found] at sameHandle
    | some literal =>
      simp only [OpenCloseHeapView.cacheAt, found, Option.map_some, Option.some.injEq] at sameHandle
      have shape : (view.handle entry literal).2 = (state.directorySlot, 0) := congrArg Prod.snd sameHandle
      have exactHandle : view.handle entry literal = ((view.handle entry literal).1, state.directorySlot, 0) :=
        Prod.ext rfl shape
      refine ⟨?_, ?_⟩
      · simp only [OpenCloseHeapView.cacheAt, found, Option.map_some, captured, Option.getD_some]
        exact congrArg some exactHandle
      change (((view.directory entry refs.directory).map fun literal => (view.handle entry literal).1).getD
        state.census).inode state.directorySlot.description = state.census.inode state.directorySlot.description
      have bound := root literal found
      rw [shape] at bound
      simpa only [found, Option.map_some, Option.getD_some] using
        Option.some.inj (bound.symm.trans initialStorage.directoryBound)
  exact ⟨view.descriptors returned, liveOwner, liveDirectory, ownerInode, captured, cached.trans capturedRoot.1,
    capturedRoot.2.trans directoryInode.symm, directoryInode, reached.names,
    protectedAfter.lockBound.trans (congrArg some ownerInode.symm),
    protectedAfter.directoryBound.trans (congrArg some directoryInode.symm)⟩

end Alvoki.Storage.DiskSession
