import Alvoki.Storage.Disk.Proofs.Keeper.NativeLongKeeperReadHeap
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeStagingAcquisition

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {reader : MarkedTemporaryReadCalls heap} {before : heap}
  {read : NativeLongKeeperReadHeap finish seed reader before} {sync : AlignedKeeperCacheCallbacks heap}
  {authorization : NativeLongKeeperAuthorizationHeap read sync}

private abbrev Remove := FilePath → EStateM IO.Error heap (Except IO.Error Unit)

/-- A successful prune reaches the directory barrier after applying the
accepted unlink results in the plan's order. The caller's invariant can
track the cumulative effect as well as any unchanged observations. -/
theorem foldReturnedPrune {model : Type}
    (directory : DiskDirectory) (plan : Plan) (remove : @Remove heap)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (invariant : model → heap → Prop) (applyUnlink : model → Nat → model)
    {initial : model} {first last : heap} (entered : invariant initial first)
    (unlink : ∀ {ordinal start finish result before}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      invariant before start → invariant (applyUnlink before ordinal) finish)
    (returned : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    let run := performPaths directory plan remove throw write sync rename
    ∃ unlinked,
      ((plan.newer.map Step.unlink).forM run) first = .ok () unlinked ∧
      sync #[directory.path] unlinked = .ok () last ∧
      invariant (plan.newer.foldl applyUnlink initial) unlinked := by
  intro run
  obtain ⟨unlinked, accepted, synced⟩ :=
    returnedWalUnlinksAndBarrier directory plan remove write sync rename returned
  exact ⟨unlinked, accepted, synced,
    foldReturnedWalUnlinks directory plan remove write sync rename invariant applyUnlink entered unlink accepted⟩

/-- The actual unlink calls determine the file image at the issued
directory barrier. Its successful return settles that same image. -/
theorem fileImageOfReturnedPrune
    (directory : DiskDirectory) (plan : Plan) (remove : @Remove heap)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (files : heap → FileImage)
    (unlink : ∀ {ordinal start finish result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      files finish = (files start).unlinkLater ordinal)
    (barrier : ∀ {start finish}, sync #[directory.path] start = .ok () finish →
      files finish = (files start).syncDirectory)
    {first last : heap}
    (covers : ∀ name ∈ (files first).later.visible, name ∈ plan.newer)
    (returned : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    ∃ unlinked, sync #[directory.path] unlinked = .ok () last ∧
      files unlinked = plan.newer.foldl FileImage.unlinkLater (files first) ∧
      files last = { (files first).syncDirectory with later := LaterNames.settled [] } := by
  obtain ⟨unlinked, _, synced, image⟩ := foldReturnedPrune directory plan remove write sync rename
    (fun projected reached => files reached = projected) FileImage.unlinkLater rfl
    (fun {ordinal _ _ _ _} member called accepted earlier =>
      (unlink member called accepted).trans (congrArg (fun image => image.unlinkLater ordinal) earlier))
    returned
  refine ⟨unlinked, synced, image, ?_⟩
  rw [barrier synced, image, FileImage.syncAfterCoveringUnlinks _ _ covers]

/-- Reuse the checked ordered unlink callbacks, with an empty pass
when the selected longer-keeper report has no later names. -/
def NativeLongKeeperUnlinks (finish : CapturedLongKeeperFinish calls reads vacant selected)
    (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (remove : @Remove heap) (before after : heap) : Prop :=
  match finish.prune with
  | .empty _ => after = before
  | .listed prune _ _ =>
    PrunedWalUnlinkHeaps view seed.directoryRef seed.activeRef seed.pendingRef remove prune.unlinks before after

/-- The unlink pass starts at the returned authorization heap. The
second directory fsync uses the original directory descriptor and
leaves the exact file state used for subsequent staging. -/
structure NativeLongKeeperSuffixHeap (authorization : NativeLongKeeperAuthorizationHeap read sync)
    (remove : @Remove heap) where
  unlinked : heap
  reached : heap
  unlinks : NativeLongKeeperUnlinks finish seed remove authorization.reached unlinked
  directoryHandle : view.handle unlinked seed.handle = view.handle authorization.reached seed.handle
  loaded : sync.getDirectory seed.directoryRef unlinked = .ok (some seed.handle) unlinked
  synced : sync.sync seed.handle unlinked = .ok () reached
  files : view.files reached = finish.prune.stageInput
  census : view.descriptors reached = view.descriptors unlinked
  cells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef unlinked reached
  handle : view.handle reached seed.handle = view.handle unlinked seed.handle

namespace NativeLongKeeperSuffixHeap

variable {remove : @Remove heap}

private theorem unlinksInOrder (seen : NativeLongKeeperSuffixHeap authorization remove)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    ((layout.boundedPlan.newer.map Step.unlink).forM (performPaths directory layout.boundedPlan remove throw write
      (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename)) authorization.reached =
      .ok () seen.unlinked ∧
    view.files seen.unlinked = { admission.held with image := finish.prune.afterUnlinks } ∧
    view.descriptors seen.unlinked = view.descriptors authorization.reached ∧
    KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef authorization.reached seen.unlinked := by
  have unlinks := seen.unlinks
  unfold NativeLongKeeperUnlinks at unlinks
  cases route : finish.prune with
  | empty report =>
    rw [route] at unlinks
    change seen.unlinked = authorization.reached at unlinks
    have suffix : layout.boundedPlan.newer = [] := report.noLater
    rw [unlinks, suffix]
    exact ⟨rfl, authorization.files, rfl, KeeperCacheCellsFrame.same⟩
  | listed report _ _ =>
    rw [route] at unlinks
    change PrunedWalUnlinkHeaps view seed.directoryRef seed.activeRef seed.pendingRef
      remove report.unlinks authorization.reached seen.unlinked at unlinks
    exact unlinks.returns admission.held authorization.files layout.boundedPlan write
      (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename

theorem returns (seen : NativeLongKeeperSuffixHeap authorization remove)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    let grouped := sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM
      (performPaths directory layout.boundedPlan remove throw write grouped rename)) authorization.reached =
      .ok () seen.reached ∧ view.files seen.reached = finish.prune.stageInput ∧
    view.descriptors seen.reached = view.descriptors authorization.reached ∧
    KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef read.closed seen.reached ∧
    view.handle seen.reached seed.handle = (admission.reached, admission.cached, 0) := by
  intro grouped
  obtain ⟨removed, _, census, framed⟩ := seen.unlinksInOrder write rename
  have unlinked : ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan remove throw write grouped rename)) authorization.reached =
    .ok () seen.unlinked := removed
  have groupedSync : grouped #[directory.path] seen.unlinked = .ok () seen.reached :=
    sync.syncsDirectory seen.loaded seen.synced
  refine ⟨?_, seen.files, seen.census.trans census, (authorization.cells.trans framed).trans seen.cells,
    seen.handle.trans (seen.directoryHandle.trans (authorization.handle.trans read.readsAndReleases.directoryHandle))⟩
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, unlinked, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, groupedSync, Pure.pure, EStateM.pure]

end NativeLongKeeperSuffixHeap

structure LongKeeperStageCallbacks (heap : Type) where
  tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Handle)
  detachStale : FilePath → EStateM IO.Error heap Unit
  create : FilePath → EStateM IO.Error heap IO.FS.Handle
  write : IO.FS.Handle → ByteArray → EStateM IO.Error heap Unit
  flush : IO.FS.Handle → EStateM IO.Error heap Unit

noncomputable def LongKeeperStageCallbacks.acquire (calls : LongKeeperStageCallbacks heap)
    (path : FilePath) : EStateM IO.Error heap IO.FS.Handle :=
  withFreshStaging calls.tryCreate calls.detachStale calls.create path pure

noncomputable def LongKeeperStageCallbacks.stage (calls : LongKeeperStageCallbacks heap)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
      (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error heap Unit := do
  let descriptor ← writeFreshStagedWith calls.tryCreate calls.detachStale calls.create calls.write calls.flush path bytes
  modifyPending pending (pushPending path descriptor)

variable {remove : @Remove heap} {suffix : NativeLongKeeperSuffixHeap authorization remove}

/-- The staging continuation uses the description from the successful
exclusive create, whether it succeeded directly or after detachment. -/
theorem LongKeeperStageCallbacks.stageReturns (calls : LongKeeperStageCallbacks heap)
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
      (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit}
    {path : FilePath} {bytes : ByteArray} {atEntry atOpen atWrite atFlush reached : heap} {file : IO.FS.Handle}
    (acquired : calls.acquire path atEntry = .ok file atOpen)
    (written : calls.write file bytes atOpen = .ok () atWrite)
    (flushed : calls.flush file atWrite = .ok () atFlush)
    (recorded : modifyPending pending (pushPending path file) atFlush = .ok () reached) :
    calls.stage pending modifyPending path bytes atEntry = .ok () reached := by
  unfold stage writeFreshStagedWith
  rw [withFreshStaging_bind]
  change ((calls.acquire path >>= fun file => do
    calls.write file bytes
    calls.flush file
    pure file) >>= fun file => modifyPending pending (pushPending path file)) atEntry = _
  simp only [Bind.bind, EStateM.bind, acquired, written, flushed, Pure.pure, EStateM.pure]
  exact recorded

/-- A successful staging callback exposes the obtained descriptor and
the adjoining write, flush and pending insertion returns. -/
theorem LongKeeperStageCallbacks.reachedStage (calls : LongKeeperStageCallbacks heap)
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
      (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit}
    {path : FilePath} {bytes : ByteArray} {entry reached : heap}
    (returned : calls.stage pending modifyPending path bytes entry = .ok () reached) :
    ∃ (descriptor : IO.FS.Handle) (opened written flushed : heap),
      calls.acquire path entry = .ok descriptor opened ∧
      calls.write descriptor bytes opened = .ok () written ∧
      calls.flush descriptor written = .ok () flushed ∧
      modifyPending pending (pushPending path descriptor) flushed = .ok () reached := by
  unfold stage writeFreshStagedWith at returned
  rw [withFreshStaging_bind] at returned
  change ((calls.acquire path >>= fun file => do
    calls.write file bytes
    calls.flush file
    pure file) >>= fun file => modifyPending pending (pushPending path file)) entry = _ at returned
  cases acquired : calls.acquire path entry with
  | error cause failed => simp [Bind.bind, EStateM.bind, acquired] at returned
  | ok descriptor opened =>
    cases wrote : calls.write descriptor bytes opened with
    | error cause failed => simp [Bind.bind, EStateM.bind, acquired, wrote] at returned
    | ok value written =>
      cases value
      cases didFlush : calls.flush descriptor written with
      | error cause failed => simp [Bind.bind, EStateM.bind, acquired, wrote, didFlush] at returned
      | ok value flushed =>
        cases value
        exact ⟨descriptor, opened, written, flushed, rfl, wrote, didFlush,
          by simpa only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, acquired, wrote, didFlush] using returned⟩

section StageFrames

open NativeFileEffectProjection (reached)

/-- The namespace effects required only when the client actually
tries or retries creation of this staging name. -/
structure LongKeeperStageCallbacks.AcquisitionFrames (calls : LongKeeperStageCallbacks heap)
    (path : FilePath) (atEntry : heap) (frame : heap → heap → Prop) where
  stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  unlink : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  tried : frame atEntry (reached (calls.tryCreate path atEntry))
  detach : ∀ {name details conflict}, calls.tryCreate path atEntry = .ok (.error (.alreadyExists name 17 details)) conflict →
    calls.detachStale path conflict = removeStaleStagingWith stat unlink path conflict
  lookedUp : ∀ {name details conflict}, calls.tryCreate path atEntry = .ok (.error (.alreadyExists name 17 details)) conflict →
    frame conflict (reached (stat path conflict))
  unlinked : ∀ {name details conflict metadata before},
    calls.tryCreate path atEntry = .ok (.error (.alreadyExists name 17 details)) conflict →
    stat path conflict = .ok (.ok metadata) before → (metadata.type == .file) = true →
    frame before (reached (unlink path before))
  created : ∀ {name details conflict before}, calls.tryCreate path atEntry = .ok (.error (.alreadyExists name 17 details)) conflict →
    calls.detachStale path conflict = .ok () before → frame before (reached (calls.create path before))

theorem LongKeeperStageCallbacks.AcquisitionFrames.keeps
    {calls : LongKeeperStageCallbacks heap} {path : FilePath} {atEntry : heap} {frame : heap → heap → Prop}
    (frames : calls.AcquisitionFrames path atEntry frame)
    (identity : ∀ atHeap, frame atHeap atHeap)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c) :
    frame atEntry (reached (calls.acquire path atEntry)) :=
  withFreshStaging_acquireKeeps calls.tryCreate calls.detachStale calls.create path frame
    identity compose atEntry frames.tried (fun {name details conflict} conflictAt => by
      rw [frames.detach conflictAt]
      exact removeStaleStagingWith_keeps frames.stat frames.unlink path frame identity compose conflict
        (frames.lookedUp conflictAt) (frames.unlinked conflictAt)) frames.created

/-- The actual stage preserves any frame established by its reached
callbacks, including an error during detach, creation or data staging. -/
theorem LongKeeperStageCallbacks.stageKeeps (calls : LongKeeperStageCallbacks heap)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
      (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit)
    (path : FilePath) (bytes : ByteArray) (atEntry : heap)
    (frame : heap → heap → Prop) (identity : ∀ atHeap, frame atHeap atHeap)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c)
    (acquisition : calls.AcquisitionFrames path atEntry frame)
    (written : ∀ {file atOpen}, calls.acquire path atEntry = .ok file atOpen →
      frame atOpen (reached (calls.write file bytes atOpen)))
    (flushed : ∀ {file atOpen atWrite}, calls.acquire path atEntry = .ok file atOpen →
      calls.write file bytes atOpen = .ok () atWrite → frame atWrite (reached (calls.flush file atWrite)))
    (recorded : ∀ {file atOpen atWrite atFlush}, calls.acquire path atEntry = .ok file atOpen →
      calls.write file bytes atOpen = .ok () atWrite → calls.flush file atWrite = .ok () atFlush →
      frame atFlush (reached (modifyPending pending (pushPending path file) atFlush))) :
    frame atEntry (reached (calls.stage pending modifyPending path bytes atEntry)) :=
  writeFreshStagedWith_keeps calls.tryCreate calls.detachStale calls.create calls.write calls.flush path bytes
    (fun file => modifyPending pending (pushPending path file)) frame compose atEntry
    (acquisition.keeps identity compose) written flushed recorded

end StageFrames

/-- A successful exclusive create supplies the descriptor subsequently
written, flushed and inserted into the original pending cell. -/
structure NativeLongKeeperFreshStageHeap (suffix : NativeLongKeeperSuffixHeap authorization remove)
    (stage : LongKeeperStageCallbacks heap) where
  descriptor : IO.FS.Handle
  created : heap
  written : heap
  flushed : heap
  recorded : heap
  acquired : stage.acquire (directory.file .stagedWal) suffix.reached = .ok descriptor created
  openedSlot : (view.handle created descriptor).2.1 = finish.stage.slot
  openedCensus : view.descriptors created = finish.stage.inventory
  wrote : stage.write descriptor layout.keeper.bytes created = .ok () written
  flush : stage.flush descriptor written = .ok () flushed
  captured : view.handle flushed descriptor = (finish.stage.inventory, finish.stage.slot, finish.stage.offset)
  record : sync.modifyPending seed.pendingRef (pushPending (directory.file .stagedWal) descriptor) flushed =
    .ok () recorded
  pending : view.pending recorded seed.pendingRef =
    pushPending (directory.file .stagedWal) descriptor (view.pending suffix.reached seed.pendingRef)
  directory : view.directory recorded seed.directoryRef = view.directory suffix.reached seed.directoryRef
  active : view.active recorded seed.activeRef = view.active suffix.reached seed.activeRef
  directoryKept : view.handle recorded seed.handle = view.handle suffix.reached seed.handle
  handleKept : view.handle recorded descriptor = view.handle flushed descriptor
  fileEffect : view.files flushed =
    { finish.prune.stageInput with image := finish.prune.stageInput.image.withScratch (some (layout.keeper.bytes, false)) }
  fileFrame : view.files recorded = view.files flushed
  atSync : view.descriptors recorded = finish.stage.inventory.afterDrops finish.stage.beforeSync

namespace NativeLongKeeperFreshStageHeap

variable {stage : LongKeeperStageCallbacks heap}

theorem returns (seen : NativeLongKeeperFreshStageHeap suffix stage)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    stage.stage seed.pendingRef sync.modifyPending (directory.file .stagedWal) layout.keeper.bytes suffix.reached =
      .ok () seen.recorded ∧
    view.cacheAt seen.recorded seed.directoryRef seed.activeRef seed.pendingRef =
      admission.cache.remember (directory.file .stagedWal) (finish.stage.inventory, finish.stage.slot, finish.stage.offset) ∧
    view.descriptors seen.recorded = finish.stage.inventory.afterDrops finish.stage.beforeSync ∧
    view.files seen.recorded =
      { finish.prune.stageInput with image := finish.prune.stageInput.image.withScratch (some (layout.keeper.bytes, false)) } := by
  obtain ⟨_, _, _, cells, directoryHandle⟩ := suffix.returns (stage.stage seed.pendingRef sync.modifyPending) rename
  have released := read.readsAndReleases
  refine ⟨?_, ?_, seen.atSync, seen.fileFrame.trans seen.fileEffect⟩
  · exact stage.stageReturns seen.acquired seen.wrote seen.flush seen.record
  · simp only [OpenCloseHeapView.cacheAt, seen.directory, cells.directory, released.frame.directoryCell,
      read.entryFrame.directoryCell, seed.directoryKept, seed.directorySet,
      seen.active, cells.active, released.frame.activeCell, read.entryFrame.activeCell, seed.activeKept, seed.activeSet,
      seen.pending, cells.pending, released.frame.pendingCell, read.entryFrame.pendingCell, seed.pendingSet,
      pushPending, seen.directoryKept, directoryHandle, Option.map_some, Option.map_none, List.map_cons, List.map_nil,
      seen.handleKept, seen.captured, CensusOpenAdmissionReports.cache, Cache.remember]

/-- The original authorization heap, ordered suffix and fresh stage
leave the bounded worker immediately before the staged-file fsync. -/
theorem reachesStageSync (seen : NativeLongKeeperFreshStageHeap suffix stage)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    let write := stage.stage seed.pendingRef sync.modifyPending
    let grouped := sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    let perform := performPaths directory layout.boundedPlan remove throw write grouped rename
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write grouped rename read.closed =
      (do
        perform (.replace .syncStaged)
        perform (.replace .renameStaged)
        perform (.replace .syncDirectory)
        pure () : EStateM IO.Error heap Unit) seen.recorded := by
  intro write grouped perform
  have first : grouped #[directory.path] read.closed = .ok () authorization.reached :=
    authorization.returns.1
  have pruned : (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM perform)
      authorization.reached = .ok () suffix.reached :=
    (suffix.returns write rename).1
  have staged := (seen.returns rename).1
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have longer : layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat :=
    bytes ▸ finish.longer
  have valid := layout.boundedPlan_valid finish.prune.later
  have exactBytes := layout.boundedPlan_extractKeeper
  rw [finishBoundedMarkedOpen_long _ _ _ _ _ _ _ valid bytes longer]
  change (do
    grouped #[directory.path]
    (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM perform)
    perform (.replace .writeStaged)
    perform (.replace .syncStaged)
    perform (.replace .renameStaged)
    perform (.replace .syncDirectory)
    pure () : EStateM IO.Error heap Unit) read.closed = _
  simp only [Bind.bind, EStateM.bind, first, pruned]
  have wrote : perform (.replace .writeStaged) suffix.reached = .ok () seen.recorded := by
    simp only [perform, performPaths, Publication.performReplacement, exactBytes, write]
    exact staged
  simp only [wrote]

end NativeLongKeeperFreshStageHeap

end Alvoki.Storage.DiskSession
