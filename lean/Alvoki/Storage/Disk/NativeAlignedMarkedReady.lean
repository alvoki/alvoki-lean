import Alvoki.Storage.Disk.NativeAlignedKeeperStorage
import Alvoki.Storage.Disk.NativeSelectedWriteReopen
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeMarkedKeeperLinks
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeOpenAdmissionStorage
import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

section LiteralRepair

variable {heap image : Type}

private theorem keepsThroughAcceptedWalUnlinks
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {keep : heap → Prop} {before after : heap} (entered : keep before)
    (unlink : ∀ {ordinal issued finished result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) issued = .ok result finished →
      RunCollection.ownedUnlinkResult result = .ok () →
      keep issued → keep finished)
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) before = .ok () after) :
    keep after :=
  foldReturnedWalUnlinks directory plan remove write sync rename (fun (_ : Unit) atHeap => keep atHeap) (fun _ _ => ())
    (initial := ()) entered (fun member called accepted current => unlink member called accepted current) returned

/-- An observed primitive can drop unrelated references. The literal
handle's open slot and description are retained in the reached census. -/
structure ReadSlotDrops (view : OpenCloseHeapView heap image) (file : IO.FS.Handle) (entry reached : heap) : Prop where
  slot : (view.handle reached file).2.1 = (view.handle entry file).2.1
  observed : ∃ drops : List LockReferenceDrop,
    view.descriptors reached = (view.descriptors entry).afterDrops drops ∧
    ∀ event ∈ drops, event.removes (view.handle entry file).2.1.reference = false

theorem ReadSlotDrops.keepsAttachment {view : OpenCloseHeapView heap image}
    {file : IO.FS.Handle} {entry reached : heap} {slot : DescriptorSlot} {inode : Nat}
    (effect : ReadSlotDrops view file entry reached)
    (attached : attachedReadSlot view file slot inode entry) :
    attachedReadSlot view file slot inode reached := by
  obtain ⟨drops, census, retained⟩ := effect.observed
  refine ⟨effect.slot.trans attached.1, ?_, ?_⟩
  · rw [census]
    exact List.mem_filter.mpr ⟨attached.2.1, List.all_eq_true.mpr fun event member => by
      rw [← attached.1, retained event member]
      rfl⟩
  · rw [census]
    exact attached.2.2

/-- For the kernel objects observed by open description, the preserved
slot keeps the complete device and inode pair. -/
theorem ReadSlotDrops.keepsDeviceInode {view : OpenCloseHeapView heap image}
    {file : IO.FS.Handle} {entry reached : heap} (effect : ReadSlotDrops view file entry reached)
    (objectOf : Nat → DeviceInode) :
    objectOf (view.handle reached file).2.1.description =
      objectOf (view.handle entry file).2.1.description :=
  congrArg (fun slot : DescriptorSlot => objectOf slot.description) effect.slot

/-- The pending insertion and cache accesses carry the actual handles
to their issue heaps. Clearing this keeper path may close other matching
references. Its selected handle is still locally retained for fsync. -/
structure AlignedRepairHandleEffects (calls : AlignedKeeperCacheCallbacks heap)
    (view : OpenCloseHeapView heap image) (path : FilePath) (root keeper : IO.FS.Handle) : Prop where
  remember : ∀ {pending readHeap remembered},
    calls.modifyPending pending (SyncHandleRouting.pushPending path keeper) readHeap = .ok () remembered →
    ReadSlotDrops view keeper readHeap remembered
  loadRoot : ∀ {cached remembered issued}, calls.getDirectory cached remembered = .ok (some root) issued →
    ReadSlotDrops view root remembered issued ∧ ReadSlotDrops view keeper remembered issued
  syncRoot : ∀ {issued reached}, calls.sync root issued = .ok () reached → ReadSlotDrops view keeper issued reached
  loadPending : ∀ {pending entries entry loaded}, calls.getPending pending entry = .ok entries loaded →
    ReadSlotDrops view keeper entry loaded
  clearPending : ∀ {pending} {entries : List (FilePath × IO.FS.Handle)} {before loaded consumed},
    calls.getPending pending before = .ok entries loaded →
    entries.find? (fun item => item.1 == path) = some (path, keeper) →
    calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed →
    ReadSlotDrops view keeper loaded consumed

private theorem AlignedRepairHandleEffects.keeperAfterPending
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image}
    {path : FilePath} {root keeper : IO.FS.Handle} (effects : AlignedRepairHandleEffects calls view path root keeper)
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {entries : List (FilePath × IO.FS.Handle)}
    {keeperSlot : DescriptorSlot} {keeperInode : Nat} {before loaded consumed : heap}
    (attached : attachedReadSlot view keeper keeperSlot keeperInode before)
    (readPending : calls.getPending pending before = .ok entries loaded)
    (selected : entries.find? (fun item => item.1 == path) = some (path, keeper))
    (clearPending : calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed) :
    attachedReadSlot view keeper keeperSlot keeperInode consumed :=
  (effects.clearPending readPending selected clearPending).keepsAttachment
    ((effects.loadPending readPending).keepsAttachment attached)

private theorem AlignedRepairHandleEffects.attachmentsAtRootCall
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image}
    {path : FilePath} {root keeper : IO.FS.Handle} (effects : AlignedRepairHandleEffects calls view path root keeper)
    {cached : IO.Ref (Option IO.FS.Handle)}
    {rootSlot keeperSlot : DescriptorSlot} {rootInode keeperInode : Nat} {before issued reached : heap}
    (rootAttached : attachedReadSlot view root rootSlot rootInode before)
    (keeperAttached : attachedReadSlot view keeper keeperSlot keeperInode before)
    (readRoot : calls.getDirectory cached before = .ok (some root) issued)
    (syncRoot : calls.sync root issued = .ok () reached) :
    attachedReadSlot view root rootSlot rootInode issued ∧ attachedReadSlot view keeper keeperSlot keeperInode reached := by
  obtain ⟨rootLoaded, keeperLoaded⟩ := effects.loadRoot readRoot
  exact ⟨rootLoaded.keepsAttachment rootAttached, (effects.syncRoot syncRoot).keepsAttachment
    (keeperLoaded.keepsAttachment keeperAttached)⟩

/-- The root issue heap still has the cached directory's descriptor.
The selected keeper's original read descriptor remains live at its own
issue heap after removing the pending entries for that name. -/
theorem AlignedRepairHandleEffects.issuedAttachments
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image}
    {path : FilePath} {root keeper : IO.FS.Handle} (effects : AlignedRepairHandleEffects calls view path root keeper)
    {cached : IO.Ref (Option IO.FS.Handle)} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {rootSlot keeperSlot : DescriptorSlot} {rootInode keeperInode : Nat} {entries : List (FilePath × IO.FS.Handle)}
    {readHeap remembered rootIssued afterDirectory loaded consumed : heap}
    (rootAtCache : attachedReadSlot view root rootSlot rootInode remembered)
    (keeperAtRead : attachedReadSlot view keeper keeperSlot keeperInode readHeap)
    (rememberedKeeper : calls.modifyPending pending (SyncHandleRouting.pushPending path keeper) readHeap = .ok () remembered)
    (readRoot : calls.getDirectory cached remembered = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () afterDirectory)
    (readPending : calls.getPending pending afterDirectory = .ok entries loaded)
    (selected : entries.find? (fun item => item.1 == path) = some (path, keeper))
    (clearPending : calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed) :
    attachedReadSlot view root rootSlot rootInode rootIssued ∧
    attachedReadSlot view keeper keeperSlot keeperInode consumed := by
  have keeperRemembered := (effects.remember rememberedKeeper).keepsAttachment keeperAtRead
  obtain ⟨rootAtIssue, keeperAfterRoot⟩ := effects.attachmentsAtRootCall rootAtCache keeperRemembered readRoot syncRoot
  exact ⟨rootAtIssue, effects.keeperAfterPending keeperAfterRoot readPending selected clearPending⟩

/-- The same cached root issues both directory barriers. Every accepted
later-name unlink keeps the root and keeper descriptions attached. -/
theorem AlignedRepairHandleEffects.issuedAttachmentsWithPrune
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image}
    {path : FilePath} {root keeper : IO.FS.Handle} (effects : AlignedRepairHandleEffects calls view path root keeper)
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {cached : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {rootSlot keeperSlot : DescriptorSlot} {rootInode keeperInode : Nat} {entries : List (FilePath × IO.FS.Handle)}
    {readHeap remembered rootIssued authorized unlinked suffixIssued suffixSettled loaded consumed : heap}
    (rootAtCache : attachedReadSlot view root rootSlot rootInode remembered)
    (keeperAtRead : attachedReadSlot view keeper keeperSlot keeperInode readHeap)
    (rememberedKeeper : calls.modifyPending pending (SyncHandleRouting.pushPending path keeper) readHeap = .ok () remembered)
    (readRoot : calls.getDirectory cached remembered = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () authorized)
    (syncKeepsRoot : ReadSlotDrops view root rootIssued authorized)
    (unlinkSlots : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      ReadSlotDrops view root before after ∧ ReadSlotDrops view keeper before after)
    (unlinks : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write (calls.syncPaths directory.path cached active pending) rename))
      authorized = .ok () unlinked)
    (readSuffixRoot : calls.getDirectory cached unlinked = .ok (some root) suffixIssued)
    (syncSuffixRoot : calls.sync root suffixIssued = .ok () suffixSettled)
    (readPending : calls.getPending pending suffixSettled = .ok entries loaded)
    (selected : entries.find? (fun item => item.1 == path) = some (path, keeper))
    (clearPending : calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed) :
    attachedReadSlot view root rootSlot rootInode rootIssued ∧
    attachedReadSlot view root rootSlot rootInode suffixIssued ∧
    attachedReadSlot view keeper keeperSlot keeperInode consumed := by
  have keeperRemembered := (effects.remember rememberedKeeper).keepsAttachment keeperAtRead
  obtain ⟨rootAtIssue, keeperAuthorized⟩ := effects.attachmentsAtRootCall rootAtCache keeperRemembered readRoot syncRoot
  let keep atHeap := attachedReadSlot view root rootSlot rootInode atHeap ∧
    attachedReadSlot view keeper keeperSlot keeperInode atHeap
  have carry {ordinal before after result} (member : ordinal ∈ plan.newer)
      (called : remove (directory.file (.walSegment ordinal)) before = .ok result after)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (prior : keep before) : keep after := by
    obtain ⟨rootEffect, keeperEffect⟩ := unlinkSlots member called accepted
    exact ⟨rootEffect.keepsAttachment prior.1, keeperEffect.keepsAttachment prior.2⟩
  obtain ⟨rootUnlinked, keeperUnlinked⟩ :=
    keepsThroughAcceptedWalUnlinks directory plan remove write (calls.syncPaths directory.path cached active pending) rename
      (keep := keep) ⟨syncKeepsRoot.keepsAttachment rootAtIssue, keeperAuthorized⟩ carry unlinks
  obtain ⟨rootAtSuffix, keeperSettled⟩ :=
    effects.attachmentsAtRootCall rootUnlinked keeperUnlinked readSuffixRoot syncSuffixRoot
  exact ⟨rootAtIssue, rootAtSuffix, effects.keeperAfterPending keeperSettled readPending selected clearPending⟩

/-- Report effects only at the actual cache reads, pending update, and
issued fsyncs of the aligned route. The active keeper's visible bytes
pass through the directory barrier, and its own fsync establishes their
durability. -/
structure AlignedRepairStorageEffects (calls : AlignedKeeperCacheCallbacks heap)
    (view : OpenCloseHeapView heap image) (state : NativeReadyState)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) (keeperInode : Nat) : Prop where
  readDirectory : ∀ {cached result entry reached}, calls.getDirectory cached entry = .ok result reached →
    (observe entry).Frames state.crashPath (observe reached) ∧ visible reached keeperInode = visible entry keeperInode
  directorySync : ∀ {root issued reached}, calls.sync root issued = .ok () reached →
    attachedReadSlot view root state.directorySlot (state.census.inode state.directorySlot.description) issued →
    (observe issued).files.names state.session.directory.path = some (state.census.inode state.directorySlot.description) →
    (observe issued).Frames (· = state.session.directory.path) (observe reached) ∧
    (observe issued).files.Frames (fun path => ∃ file, path = state.session.directory.file file) (observe reached).files ∧
    (∀ names ∈ (observe reached).crashNames, ∀ file, names (state.session.directory.file file) =
      (observe reached).files.names (state.session.directory.file file)) ∧
    visible reached keeperInode = visible issued keeperInode
  readPending : ∀ {pending entries entry reached}, calls.getPending pending entry = .ok entries reached →
    (observe entry).Frames state.crashPath (observe reached) ∧ visible reached keeperInode = visible entry keeperInode
  setPending : ∀ {pending entries entry reached}, calls.setPending pending entries entry = .ok () reached →
    (observe entry).Frames state.crashPath (observe reached) ∧ visible reached keeperInode = visible entry keeperInode
  keeperSync : ∀ {keeper slot issued reached}, calls.sync keeper issued = .ok () reached →
    attachedReadSlot view keeper slot keeperInode issued →
    (observe issued).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some keeperInode →
    RegularFileSyncEffect keeperInode [visible issued keeperInode] (observe issued) (observe reached) ∧
    visible reached keeperInode = visible issued keeperInode

private theorem AlignedRepairStorageEffects.atDirectoryBarrier
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image} {state : NativeReadyState}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray} {keeperInode : Nat}
    (effects : AlignedRepairStorageEffects calls view state observe visible keeperInode)
    {cached : IO.Ref (Option IO.FS.Handle)} {root : IO.FS.Handle} {entry issued reached : heap}
    (readRoot : calls.getDirectory cached entry = .ok (some root) issued)
    (syncRoot : calls.sync root issued = .ok () reached)
    (rootIssued : attachedReadSlot view root state.directorySlot
      (state.census.inode state.directorySlot.description) issued)
    (rootBound : (observe entry).files.names state.session.directory.path = some (state.census.inode state.directorySlot.description))
    (rootSettled : ∀ names ∈ (observe entry).crashNames,
      names state.session.directory.path = (observe entry).files.names state.session.directory.path) :
    (observe entry).files.Frames state.crashPath (observe reached).files ∧
    (∀ names ∈ (observe reached).crashNames, ∀ path, state.crashPath path → names path = (observe reached).files.names path) ∧
    visible reached keeperInode = visible entry keeperInode := by
  have keepsRoot : state.crashPath state.session.directory.path :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inr (.inl rfl)))
  obtain ⟨rootLoadFrame, rootLoadKeeper⟩ := effects.readDirectory readRoot
  have rootAtIssue := (rootLoadFrame.visible _ keepsRoot).1.trans rootBound
  have settledRootAtIssue := (rootLoadFrame.weaken (scope := (· = state.session.directory.path))
    (fun _ equal => equal ▸ keepsRoot)).settledFrom (fun names allowed _ equal => equal.symm ▸ rootSettled names allowed)
  obtain ⟨parentFrame, childFrame, childNames, rootSyncKeeper⟩ := effects.directorySync syncRoot rootIssued rootAtIssue
  obtain ⟨directoryFrame, settledDirectory⟩ := NativeReadyState.framesByDirectory rfl parentFrame childFrame
    (fun names member => settledRootAtIssue names member _ rfl) childNames
  exact ⟨rootLoadFrame.visible.trans directoryFrame, settledDirectory, rootSyncKeeper.trans rootLoadKeeper⟩

private theorem AlignedRepairStorageEffects.afterKeeperBarrier
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image} {state : NativeReadyState}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray} {keeperInode : Nat}
    (effects : AlignedRepairStorageEffects calls view state observe visible keeperInode)
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {keeper : IO.FS.Handle} {keeperSlot : DescriptorSlot} {entries : List (FilePath × IO.FS.Handle)}
    {entry keeperEntry loaded consumed repaired : heap}
    (readPending : calls.getPending pending keeperEntry = .ok entries loaded)
    (clearPending : calls.setPending pending
      (entries.filter (fun item => item.1 != state.session.directory.file (.walSegment state.writer.wal.active.first))) loaded =
      .ok () consumed)
    (syncKeeper : calls.sync keeper consumed = .ok () repaired)
    (keeperIssued : attachedReadSlot view keeper keeperSlot keeperInode consumed)
    (directoryFrame : (observe entry).files.Frames state.crashPath (observe keeperEntry).files)
    (directorySettled : ∀ names ∈ (observe keeperEntry).crashNames,
      ∀ path, state.crashPath path → names path = (observe keeperEntry).files.names path)
    (protectedFiles : NativeReadyProtectedStorage state (observe entry).files)
    (marker : (observe entry).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (keeperBound : (observe entry).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some keeperInode)
    (keeperBytes : visible keeperEntry keeperInode = state.writer.wal.active.bytes)
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      (observe entry).files.names path ≠ some keeperInode) :
    NativeReadyStorage state (observe repaired) ∧
    ∀ inode, (observe repaired).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible repaired inode = state.writer.wal.active.bytes := by
  let keeperPath := state.session.directory.file (.walSegment state.writer.wal.active.first)
  have keepsKeeper : state.crashPath keeperPath := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  obtain ⟨pendingFrame, pendingKeeper⟩ := effects.readPending readPending
  obtain ⟨clearFrame, clearKeeper⟩ := effects.setPending clearPending
  have pendingUpdate := pendingFrame.trans clearFrame
  have toIssue := directoryFrame.trans pendingUpdate.visible
  have boundAtIssue := (toIssue keeperPath keepsKeeper).1.trans keeperBound
  have bytesAtIssue := clearKeeper.trans (pendingKeeper.trans keeperBytes)
  obtain ⟨synced, keeperUnchanged⟩ := effects.keeperSync syncKeeper keeperIssued boundAtIssue
  rw [bytesAtIssue] at synced
  refine ⟨NativeReadyStorage.afterAlignedBarriers directoryFrame directorySettled pendingUpdate
    protectedFiles marker apart boundAtIssue synced, ?_⟩
  intro inode named
  have same := Option.some.inj (named.symm.trans ((congrFun synced.names keeperPath).trans boundAtIssue))
  subst inode
  exact keeperUnchanged.trans bytesAtIssue

/-- The reached aligned callbacks settle the selected namespace and
sync the bytes on its remembered keeper. The result supplies the repaired
state for `OpenReferenceAllocations.framesReadyStorage`. -/
theorem AlignedRepairStorageEffects.readyAfterSyncs
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image} {state : NativeReadyState}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray} {keeperInode : Nat}
    (effects : AlignedRepairStorageEffects calls view state observe visible keeperInode)
    {cached : IO.Ref (Option IO.FS.Handle)} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {root keeper : IO.FS.Handle} {keeperSlot : DescriptorSlot} {entries : List (FilePath × IO.FS.Handle)}
    {entry rootIssued afterDirectory loaded consumed repaired : heap}
    (readRoot : calls.getDirectory cached entry = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () afterDirectory)
    (readPending : calls.getPending pending afterDirectory = .ok entries loaded)
    (clearPending : calls.setPending pending
      (entries.filter (fun item => item.1 != state.session.directory.file (.walSegment state.writer.wal.active.first))) loaded =
      .ok () consumed)
    (syncKeeper : calls.sync keeper consumed = .ok () repaired)
    (rootIssuedSlot : attachedReadSlot view root state.directorySlot
      (state.census.inode state.directorySlot.description) rootIssued)
    (keeperIssuedSlot : attachedReadSlot view keeper keeperSlot keeperInode consumed)
    (protectedFiles : NativeReadyProtectedStorage state (observe entry).files)
    (marker : (observe entry).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe entry).crashNames,
      names state.session.directory.path = (observe entry).files.names state.session.directory.path)
    (keeperBound : (observe entry).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some keeperInode)
    (keeperBytes : visible entry keeperInode = state.writer.wal.active.bytes)
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      (observe entry).files.names path ≠ some keeperInode) :
    NativeReadyStorage state (observe repaired) ∧
    ∀ inode, (observe repaired).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible repaired inode = state.writer.wal.active.bytes := by
  obtain ⟨framed, settled, bytes⟩ :=
    effects.atDirectoryBarrier readRoot syncRoot rootIssuedSlot protectedFiles.directoryBound rootSettled
  exact effects.afterKeeperBarrier readPending clearPending syncKeeper keeperIssuedSlot framed settled protectedFiles marker
    keeperBound (bytes.trans keeperBytes) apart

/-- Use both actual rooted barriers, and frame the protected paths
through each accepted later-name unlink. The selected keeper's bytes
are made durable only by its own final fsync. -/
theorem AlignedRepairStorageEffects.readyAfterSyncsWithPrune
    {calls : AlignedKeeperCacheCallbacks heap} {view : OpenCloseHeapView heap image} {state : NativeReadyState}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray} {keeperInode : Nat}
    (effects : AlignedRepairStorageEffects calls view state observe visible keeperInode)
    (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (ready : state.Valid)
    (later : ∀ ordinal ∈ plan.newer, state.writer.wal.active.first < ordinal)
    (unlinkStorage : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (state.session.directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (observe before).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
        some keeperInode →
      (observe before).Frames
        (fun path => state.crashPath path ∧ path ≠ state.session.directory.file (.walSegment ordinal)) (observe after) ∧
      visible after keeperInode = visible before keeperInode)
    {cached : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {root keeper : IO.FS.Handle} {keeperSlot : DescriptorSlot} {entries : List (FilePath × IO.FS.Handle)}
    {entry rootIssued authorized unlinked suffixIssued suffixSettled loaded consumed repaired : heap}
    (readRoot : calls.getDirectory cached entry = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () authorized)
    (unlinks : ((plan.newer.map Step.unlink).forM (performPaths state.session.directory plan remove throw write
      (calls.syncPaths state.session.directory.path cached active pending) rename)) authorized = .ok () unlinked)
    (readSuffixRoot : calls.getDirectory cached unlinked = .ok (some root) suffixIssued)
    (syncSuffixRoot : calls.sync root suffixIssued = .ok () suffixSettled)
    (readPending : calls.getPending pending suffixSettled = .ok entries loaded)
    (clearPending : calls.setPending pending
      (entries.filter (fun item => item.1 != state.session.directory.file (.walSegment state.writer.wal.active.first))) loaded =
      .ok () consumed)
    (syncKeeper : calls.sync keeper consumed = .ok () repaired)
    (rootIssuedSlot : attachedReadSlot view root state.directorySlot
      (state.census.inode state.directorySlot.description) rootIssued)
    (suffixIssuedSlot : attachedReadSlot view root state.directorySlot
      (state.census.inode state.directorySlot.description) suffixIssued)
    (keeperIssuedSlot : attachedReadSlot view keeper keeperSlot keeperInode consumed)
    (protectedFiles : NativeReadyProtectedStorage state (observe entry).files)
    (marker : (observe entry).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe entry).crashNames,
      names state.session.directory.path = (observe entry).files.names state.session.directory.path)
    (keeperBound : (observe entry).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some keeperInode)
    (keeperBytes : visible entry keeperInode = state.writer.wal.active.bytes)
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      (observe entry).files.names path ≠ some keeperInode) :
    NativeReadyStorage state (observe repaired) ∧
    ∀ inode, (observe repaired).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible repaired inode = state.writer.wal.active.bytes := by
  let directory := state.session.directory
  let keeperPath := directory.file (.walSegment state.writer.wal.active.first)
  have keepsKeeper : state.crashPath keeperPath := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  obtain ⟨initialFrame, initialSettled, initialBytes⟩ :=
    effects.atDirectoryBarrier readRoot syncRoot rootIssuedSlot protectedFiles.directoryBound rootSettled
  let keep atHeap := (observe authorized).Frames state.crashPath (observe atHeap) ∧
    visible atHeap keeperInode = visible authorized keeperInode
  have carry {ordinal before after result} (member : ordinal ∈ plan.newer)
      (called : remove (directory.file (.walSegment ordinal)) before = .ok result after)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (prior : keep before) : keep after := by
    have namedKeeper := ((initialFrame.trans prior.1.visible) _ keepsKeeper).1.trans keeperBound
    obtain ⟨framed, live⟩ := unlinkStorage member called accepted namedKeeper
    have elsewhere (path : FilePath) (inside : state.crashPath path) : path ≠ directory.file (.walSegment ordinal) := by
      have activeBefore := later ordinal member
      rcases NativeReadyState.crashPath_iff_write.mp inside with marker | keeper | immutable
      · exact state.protectedPathNeWalFromActive ready (.inl marker) (Nat.le_of_lt activeBefore)
      · rw [keeper]
        exact fun same => (Nat.ne_of_lt activeBefore) (directory.walSegment_path_injective same)
      · exact state.protectedPathNeWalFromActive ready (.inr immutable) (Nat.le_of_lt activeBefore)
    exact ⟨prior.1.trans (framed.weaken fun path inside => ⟨inside, elsewhere path inside⟩),
      live.trans prior.2⟩
  obtain ⟨unlinkFrame, unlinkBytes⟩ :=
    keepsThroughAcceptedWalUnlinks directory plan remove write (calls.syncPaths directory.path cached active pending) rename
      (keep := keep) ⟨.refl _ _, rfl⟩ carry unlinks
  have keepsRoot : state.crashPath directory.path := NativeReadyState.crashPath_iff_write.mpr (.inr (.inr (.inl rfl)))
  have framedUnlinks := initialFrame.trans unlinkFrame.visible
  have rootAfterUnlinks := (framedUnlinks _ keepsRoot).1.trans protectedFiles.directoryBound
  have settledAfterUnlinks : ∀ names ∈ (observe unlinked).crashNames,
      names directory.path = (observe unlinked).files.names directory.path :=
    fun names allowed => unlinkFrame.settledFrom initialSettled names allowed _ keepsRoot
  obtain ⟨suffixFrame, suffixSettledNames, suffixBytes⟩ :=
    effects.atDirectoryBarrier readSuffixRoot syncSuffixRoot suffixIssuedSlot rootAfterUnlinks settledAfterUnlinks
  exact effects.afterKeeperBarrier readPending clearPending syncKeeper keeperIssuedSlot (framedUnlinks.trans suffixFrame)
    suffixSettledNames protectedFiles marker keeperBound (suffixBytes.trans (unlinkBytes.trans (initialBytes.trans keeperBytes))) apart


end LiteralRepair

section CheckpointReturn

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {history modelHistory : List WAL.Write} {log : List DatabaseSubmissions}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {layout : CanonicalKeeperLayout retry.image modelHistory} {published : Image}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {raw : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
    allocatePhase allocateToken stream}
  {next : NativeReadPosition history log}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened}
  {assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

local notation "reopened" => next.state
local notation "keeperPath" => next.state.session.directory.file (DiskFile.walSegment next.state.writer.wal.active.first)
local notation "keeperInode" => opening.reads.wal.keeper.calls.inventory.inode opening.reads.wal.keeper.calls.slot.description

/-- The actual aligned syncs establish the next write entry for the selected
writer. The phase and token allocations frame those facts up to the
returned heap. All protected files refer to the selected checkpoint. -/
theorem RawAlignedCheckpointReopenEffects.ReturnedAt.writeStorageEntry
    (returned : raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (sameFirst : (reopened).writer.wal.active.first = layout.keeper.first)
    (sameBytes : (reopened).writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage reopened (observe raw.keeper.remembered).files)
    (marker : (observe raw.keeper.remembered).files.Stored ((reopened).session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe raw.keeper.remembered).crashNames,
      names (reopened).session.directory.path = (observe raw.keeper.remembered).files.names (reopened).session.directory.path)
    (effects : raw.keeper.StorageEffects observe visible reopened)
    (keeperAtIssue : (observe raw.keeper.consumed).files.names (directory.file (.walSegment layout.keeper.first)) =
      some (keeperInode) ∧ visible raw.keeper.consumed (keeperInode) = layout.keeper.bytes)
    (apart : ∀ path, path = (reopened).session.directory.file .walBoundary ∨ (reopened).writeFramePath path →
      (observe raw.keeper.remembered).files.names path ≠ some (keeperInode))
    (phaseFrames : ∀ ref after, allocatePhase (.ready (reopened).writer.installed) raw.keeper.reached = .ok ref after →
      (observe raw.keeper.reached).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe raw.keeper.reached).files.names (keeperPath) = some inode →
        visible after inode = visible raw.keeper.reached inode)
    (tokenFrames : ∀ before ref after, allocateToken () before = .ok ref after →
      (observe before).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe before).files.names (keeperPath) = some inode → visible after inode = visible before inode) :
    ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      returned.start.WriteStorageEntry view cache (observe returned.start.reached) (visible returned.start.reached) := by
  obtain ⟨_, settled, keeper⟩ := raw.keeper.readyStorage observe visible returned.resolvedDirectory
    returned.repairCensus returned.directorySlot sameFirst sameBytes protectedFiles marker rootSettled effects keeperAtIssue apart
  obtain ⟨allocation, sameAllocation⟩ := returned.allocation
  obtain ⟨phase, phaseKeeper⟩ := phaseFrames _ _ allocation.phaseAllocated
  obtain ⟨token, tokenKeeper⟩ := tokenFrames _ _ _ allocation.tokenAllocated
  obtain ⟨physical, bytes⟩ := allocation.framesReadyStorage observe visible settled keeper phase token phaseKeeper tokenKeeper
  have stateAtReturn := congrArg (fun position : NativeExecutionPosition => position.ready.state) returned.position
  have reached : returned.start.reached = allocation.afterToken := congrArg (fun allocated => allocated.2.2) sameAllocation
  have atPath : returned.handle.files.AtDirectory returned.start.current.ready.state.session.directory.path := by
    rw [stateAtReturn, returned.resolvedDirectory]
    exact returned.directory
  let cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path :=
    ⟨raw.seed.directoryRef, raw.seed.activeRef, raw.seed.pendingRef, returned.references, atPath⟩
  have cached : (reopened).cache.directory = some (opening.admission.reached, (reopened).directorySlot, 0) := by
    rw [returned.capturedCache, returned.directorySlot]
    rfl
  have sameObjects := (congrArg DescriptorInventory.inode returned.repairCensus).trans opening.finish.sameCensusObjects
  refine ⟨cache, rfl, rfl, rfl, ⟨returned.census.trans (congrArg NativeReadyState.census stateAtReturn.symm),
    returned.cache.trans (congrArg NativeReadyState.cache stateAtReturn.symm), ?_, ?_, ?_⟩⟩
  · rw [stateAtReturn, reached]
    exact physical
  · rw [stateAtReturn, reached]
    exact bytes
  · intro literal found
    rw [stateAtReturn]
    exact (reached.symm ▸ physical).bindsOpenCacheDirectory view returned.cache cached (congrFun sameObjects.symm _) found

/-- The reopened writer's own selected map determines which physical
payloads it keeps through a subsequent append. -/
theorem NativeReadyProtectedStorage.ofCheckpointSample {state : NativeReadyState}
    {files : CheckpointSurvivingFiles}
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (physicalFrame : (⟨names, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      state.writeFramePath files)
    (authority : RebootDirectoryBindings state names)
    (manifest : (names (state.session.directory.file .manifest)).map contents = state.writer.target.pair.manifest)
    (sealed : ∀ segment ∈ state.writer.wal.sealed,
      (names (state.session.directory.file (.walSegment segment.first))).map contents = some segment.bytes)
    (runs : ∀ generation index, state.writer.published.durable generation index =
      (names (state.session.directory.file (.run generation index))).map contents) :
    NativeReadyProtectedStorage state files := by
  have stored {path : FilePath} {payload : ByteArray} (inside : state.writeFramePath path)
      (sampled : (names path).map contents = some payload) : files.Stored path payload := by
    obtain ⟨inode, bound, exactPayload⟩ := Option.map_eq_some_iff.mp sampled
    obtain ⟨name, bytes⟩ := physicalFrame path inside
    exact ⟨inode, name.trans bound, (bytes inode bound).trans (congrArg (fun payload => [payload]) exactPayload)⟩
  refine ⟨(physicalFrame _ (.inl rfl)).1.trans authority.directory,
    (physicalFrame _ (.inr (.inl rfl))).1.trans authority.lock, ?_, ?_, ?_⟩
  · cases selected : state.writer.target.pair.manifest with
    | none => exact (physicalFrame _ (.inr (.inr (.inl rfl)))).1.trans (Option.map_eq_none_iff.mp (manifest.trans selected))
    | some bytes => exact stored (.inr (.inr (.inl rfl))) (manifest.trans selected)
  · intro segment included
    exact stored (.inr (.inr (.inr (.inl ⟨segment, included, rfl⟩)))) (sealed segment included)
  · intro bytes metadata selected decoded index within payload storedPayload
    exact stored (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, selected, decoded, within, rfl⟩))))
      ((runs metadata.header.generation index).symm.trans storedPayload)

/-- Scoped laws for the callbacks reached while an aligned checkpoint
reader prepares the returned writer. -/
structure AlignedCheckpointWriteEffects
    (raw : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (state : NativeReadyState) (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop where
  admissionEffects : raw.raw.CacheFrames raw.seed (fun before after =>
      MarkedOpenReadFrame directory state.crashPath (directory.file (.walSegment layout.keeper.first))
        (observe before) (observe after) (visible before) (visible after))
  readEffects :
      let path := directory.file (.walSegment layout.keeper.first)
      let frame before after := MarkedOpenReadFrame directory state.crashPath path
        (observe before) (observe after) (visible before) (visible after)
      raw.fileCalls.ScopeFrames frame ∧ raw.directoryCalls.ScopeFrames directory frame ∧
      ((raw.callbacks.withFileReads raw.fileCalls).modifyPending raw.seed.pendingRef
        (SyncHandleRouting.pushPending path raw.keeper.keeper) raw.keeper.read =
        .ok () raw.keeper.remembered → frame raw.keeper.read raw.keeper.remembered)
  directoryLive :
      (raw.callbacks.withFileReads raw.fileCalls).sync raw.seed.handle raw.keeper.remembered = .ok () raw.keeper.authorized →
      (⟨(observe raw.keeper.remembered).files.names, fun inode => [visible raw.keeper.remembered inode]⟩ :
        CheckpointSurvivingFiles).Frames (· = directory.file (.walSegment layout.keeper.first))
        ⟨(observe raw.keeper.authorized).files.names, fun inode => [visible raw.keeper.authorized inode]⟩
  pendingLive :
      (raw.callbacks.withFileReads raw.fileCalls).setPending raw.seed.pendingRef [] raw.keeper.authorized =
        .ok () raw.keeper.consumed →
      (⟨(observe raw.keeper.authorized).files.names, fun inode => [visible raw.keeper.authorized inode]⟩ :
        CheckpointSurvivingFiles).Frames (· = directory.file (.walSegment layout.keeper.first))
        ⟨(observe raw.keeper.consumed).files.names, fun inode => [visible raw.keeper.consumed inode]⟩
  links : Nonempty (RunOpenLinkCensus (path := directory.file (.walSegment layout.keeper.first))
      (before := raw.listing.reached) raw.fileCalls.stat (observe raw.listing.reached).files.names
      opening.reads.wal.keeper.observesFile.object)
  effects : raw.keeper.StorageEffects observe visible state
  phaseFrames : ∀ ref after, allocatePhase (.ready state.writer.installed) raw.keeper.reached = .ok ref after →
      (observe raw.keeper.reached).Frames state.crashPath (observe after) ∧
      ∀ inode, (observe raw.keeper.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
        visible after inode = visible raw.keeper.reached inode
  tokenFrames : ∀ before ref after, allocateToken () before = .ok ref after →
      (observe before).Frames state.crashPath (observe after) ∧
      ∀ inode, (observe before).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode → visible after inode = visible before inode

/-- The sampled files at the healthy entry survive the exact admission,
listing and reads. The same keeper inode then supplies the write entry. -/
theorem RawAlignedCheckpointReopenEffects.ReturnedAt.writeStorageFromCheckpointSample
    (returned : raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (contents : Nat → ByteArray)
    (sameFirst : (reopened).writer.wal.active.first = layout.keeper.first)
    (sameBytes : (reopened).writer.wal.active.bytes = layout.keeper.bytes)
    (authority : RebootDirectoryBindings reopened bindings)
    (manifest : (bindings ((reopened).session.directory.file .manifest)).map contents =
      (reopened).writer.target.pair.manifest)
    (sealed : ∀ segment ∈ (reopened).writer.wal.sealed,
      (bindings ((reopened).session.directory.file (.walSegment segment.first))).map contents = some segment.bytes)
    (runs : ∀ generation index, (reopened).writer.published.durable generation index =
      (bindings ((reopened).session.directory.file (.run generation index))).map contents)
    (sampled : (⟨bindings, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      (reopened).crashPath (observe entry).files)
    (marker : (bindings ((reopened).session.directory.file .walBoundary)).map contents =
      some (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe entry).crashNames, names (reopened).session.directory.path =
      (observe entry).files.names (reopened).session.directory.path)
    (keeperLive :
      let path := directory.file (.walSegment layout.keeper.first)
      let object := opening.reads.wal.keeper.observesFile.object
      (observe entry).files.names path = some object ∧ visible entry object = layout.keeper.bytes ++ layout.tail)
    (laws : AlignedCheckpointWriteEffects raw reopened observe visible) :
    ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      returned.start.WriteStorageEntry view cache (observe returned.start.reached) (visible returned.start.reached) := by
  let path := directory.file (.walSegment layout.keeper.first)
  let frame before after := MarkedOpenReadFrame directory (reopened).crashPath path
    (observe before) (observe after) (visible before) (visible after)
  have refl : ∀ atHeap, frame atHeap atHeap := fun _ => .refl _ _ _ _ _
  obtain ⟨fileEffects, listingEffects, remembered⟩ := laws.readEffects
  have admission := raw.raw.framesThroughCache raw.seed (frame := frame) MarkedOpenReadFrame.trans laws.admissionEffects
  obtain ⟨toListing, afterListing⟩ := raw.listing.framesThroughSeals selected raw.seals frame refl
    MarkedOpenReadFrame.trans fileEffects listingEffects
  have readKeeper := raw.keeper.framesRemembered refl MarkedOpenReadFrame.trans (fun opened => by
    have effect := fileEffects.openRead path raw.beforeKeeper
    change raw.fileCalls.openRead path raw.beforeKeeper = .ok raw.keeper.keeper raw.keeper.opened at opened
    simpa only [opened, SyncHandleRouting.reachedState] using effect)
    (fileEffects.readChunk raw.keeper.keeper) remembered
  have listedToRemembered := afterListing.trans readKeeper
  have all := admission.trans (toListing.trans listedToRemembered)
  have writtenPath {file} (holds : (reopened).writeFramePath file) :
      (reopened).crashPath file := NativeReadyState.crashPath_iff_write.mpr (.inr (.inr holds))
  have protectedAtSync := (NativeReadyProtectedStorage.ofCheckpointSample bindings contents
    (fun file valid => sampled file (writtenPath valid)) authority manifest sealed runs).frame
      (fun file valid => all.durable.visible file (writtenPath valid))
  let markerPath := (reopened).session.directory.file .walBoundary
  have keepsMarker : (reopened).crashPath markerPath := NativeReadyState.crashPath_iff_write.mpr (.inl rfl)
  have markerAtEntry : (observe entry).files.Stored markerPath
      (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, observed⟩ := Option.map_eq_some_iff.mp marker
    obtain ⟨sameName, kept⟩ := sampled markerPath keepsMarker
    exact ⟨inode, sameName.trans bound, (kept inode bound).trans (congrArg (fun bytes => [bytes]) observed)⟩
  have markerAtSync := all.durable.visible.stored keepsMarker markerAtEntry
  have parent := all.durable.weaken (scope := (· = (reopened).session.directory.path))
    (fun _ same => .inl same)
  have stableRoot := parent.settledFrom (fun names member file same => same.symm ▸ rootSettled names member)
  obtain ⟨keeperName, keeperBytes⟩ := (admission.trans (toListing.trans afterListing)).keeper path rfl
  have keeperAtEntry := keeperName.trans keeperLive.1
  have visibleAtEntry := (List.cons.inj (keeperBytes _ keeperLive.1)).1.trans keeperLive.2
  have keeperAtIssue := raw.keeper.keeperAtIssue (fun atHeap => (observe atHeap).files.names) visible
    keeperAtEntry visibleAtEntry readKeeper.keeper laws.directoryLive laws.pendingLive
  rw [raw.keeper.keeperIssueInode, ← opening.reads.wal.keeper.observesFile.sameObject] at keeperAtIssue
  have valid := next.readPrefix.refines.1
  have apart : ∀ file, file = markerPath ∨ (reopened).writeFramePath file →
      (observe raw.keeper.remembered).files.names file ≠ some (keeperInode) := by
    intro file selectedPath bound
    have crashPath : (reopened).crashPath file := NativeReadyState.crashPath_iff_write.mpr (selectedPath.imp id Or.inr)
    have declared := NativeReadyState.crashPath_rootOrChild crashPath
    rw [returned.resolvedDirectory] at declared
    obtain ⟨links⟩ := laws.links
    have privateAtListing := raw.extents.keeperPrivateBinding (names := fun atHeap => (observe atHeap).files.names) links
    have canonical := privateAtListing file ((listedToRemembered.names file declared).symm.trans
      (bound.trans (congrArg some opening.reads.wal.keeper.observesFile.sameObject)))
    exact NativeReadyState.protectedPathNeWalFromActive valid selectedPath (Nat.le_refl _)
      (by rw [returned.resolvedDirectory, sameFirst]; exact canonical)
  exact returned.writeStorageEntry observe visible sameFirst sameBytes protectedAtSync markerAtSync
    (fun names member => stableRoot names member _ rfl) laws.effects keeperAtIssue apart laws.phaseFrames laws.tokenFrames

end CheckpointReturn

variable {heap stream : Type} {prior : NativeReadyState} {input : FilePath}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {vacant : TryLockObserves retry.owners prior.session.directory (.ok true)}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint prior.writer.published.durable
    retry.image.directory.active.manifest prior.writer.checkpoint}
  {opening : MarkedReadyOpenObservations input prior.session.directory inventory retry layout
    prior.writer.published vacant selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

local notation "dir" => prior.session.directory

/-- An actual returned writer with the physical storage and cache identity
needed at its next append. -/
def RawHealthyMarkedOpenEffects.ReadyWriterReturn
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop :=
    ∃ (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (cache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      execute makeCache = .ok handle.table start.reached ∧
      start.current.history = history ∧ start.current.submissions = log ∧ start.current.ready.reads = reads ∧
      handle.lock = raw.raw.lock ∧ handle.get = get ∧ handle.set = set ∧
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      start.current.ready.state.cache = opening.admission.cache ∧
      start.current.ready.state.session.directory = dir ∧ start.current.ready.state.directorySlot = opening.admission.cached ∧
      start.WriteStorageEntry view cache (observe start.reached) (visible start.reached)

/-- Physical facts for the selected writer arise at the actual repair heap.
The same installation transports them through both reference allocations. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterRepair
    {raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.SelectedReturn log reads execute get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (sameObjects : opening.finish.census.inode = opening.admission.reached.inode)
    (atRepair : ∀ next : NativeReadPosition history log,
      next.state.session.directory = dir → next.state.census = opening.finish.census →
      next.state.owner = opening.admission.owner → next.state.directorySlot = opening.admission.cached →
      next.state.writer.target = layout.target → next.state.files.image.kept = retry.image.kept →
      next.state.writer.published.durable = prior.writer.published.durable →
      next.state.writer.wal.active.first = layout.keeper.first → next.state.writer.wal.active.bytes = layout.keeper.bytes →
      NativeReadyStorage next.state (observe raw.repaired) ∧
      ∀ inode, (observe raw.repaired).files.names (next.state.session.directory.file
        (.walSegment next.state.writer.wal.active.first)) = some inode →
        visible raw.repaired inode = next.state.writer.wal.active.bytes)
    (phaseFrames : ∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired)
    (tokenFrames : ∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) :
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  obtain ⟨_, next, makeCache, handle, start, _, _, ran, position, recorded, _, target, _, _, durable,
    lock, refs, atDirectory, _, sameGet, sameSet, _, _, _, _, _, _, _, census, cache, directory, modeledCensus, owner, slot,
    capturedCache, kept, first, bytes, allocation, returnedAt⟩ := returned
  obtain ⟨ready, issuedKeeper⟩ := atRepair next directory modeledCensus owner slot target kept durable first bytes
  obtain ⟨phaseFrame, phaseKeeps⟩ := phaseFrames next.state allocation.phase allocation.afterPhase allocation.phaseAllocated
  obtain ⟨tokenFrame, tokenKeeps⟩ :=
    tokenFrames next.state allocation.afterPhase allocation.token allocation.afterToken allocation.tokenAllocated
  have final := allocation.framesReadyStorage observe visible ready issuedKeeper
    phaseFrame tokenFrame (fun inode _ => congrFun phaseKeeps inode) (fun inode _ => congrFun tokenKeeps inode)
  have reached : start.reached = allocation.afterToken := congrArg (fun result => result.2.2) returnedAt
  have returnedState : start.current.ready.state = next.state := congrArg (fun position => position.ready.state) position
  have returnedDirectory : start.current.ready.state.session.directory = dir := by
    rw [returnedState]
    exact directory
  let cacheRefs : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path :=
    ⟨raw.seed.directoryRef, raw.seed.activeRef, raw.seed.pendingRef, refs, by rw [returnedDirectory]; exact atDirectory⟩
  refine ⟨makeCache, handle, start, cacheRefs, ran, ?_, ?_, ?_, lock, sameGet, sameSet,
    rfl, rfl, rfl, ?_, returnedDirectory, ?_, ?_⟩
  · rw [position]
  · rw [position]
  · rw [position]
    exact recorded
  · rw [returnedState]
    exact capturedCache
  · rw [returnedState]
    exact slot
  · have physical : NativeReadyStorage start.current.ready.state (observe start.reached) := by
      rw [returnedState, reached]
      exact final.1
    refine ⟨census.trans (congrArg NativeReadyState.census returnedState.symm),
      cache.trans (congrArg NativeReadyState.cache returnedState.symm), physical, ?_, ?_⟩
    · rw [returnedState, reached]
      exact final.2
    · intro literal found
      rw [returnedState]
      have atStart : NativeReadyStorage next.state (observe start.reached) := reached.symm ▸ final.1
      exact atStart.bindsOpenCacheDirectory view cache (by rw [capturedCache, slot]; rfl)
        (congrFun (sameObjects.symm.trans (congrArg DescriptorInventory.inode modeledCensus).symm) _) found

end Alvoki.Storage.DiskSession
