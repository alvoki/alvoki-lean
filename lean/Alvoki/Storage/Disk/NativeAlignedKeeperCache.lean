import Alvoki.Storage.Disk.NativeOpenCacheReferences
import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.NativeRawSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- The successful finisher has one authorization barrier. It reaches
the shared checked unlink pass except on the empty aligned fast path.
The measured size then determines the tail of that same execution. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_reachedSuccess {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {entry reached : heap}
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached) :
    let run := performPaths directory plan remove throw write sync rename
    plan.valid = true ∧ plan.keeperBytes.size = plan.keeperSize ∧ plan.keeperSize ≤ physicalSize ∧
    ∃ authorized, sync #[directory.path] entry = .ok () authorized ∧
      if plan.newer.isEmpty && physicalSize == plan.keeperSize then
        sync #[directory.file (.walSegment plan.keeper)] authorized = .ok () reached
      else
        ∃ pruned, ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) authorized = .ok () pruned ∧
          (if plan.keeperSize < physicalSize then (Publication.steps.map Step.replace).forM run
            else sync #[directory.file (.walSegment plan.keeper)]) pruned = .ok () reached := by
  intro run
  have guarded :
      (plan.valid && (plan.keeperBytes.size == plan.keeperSize) && decide (plan.keeperSize ≤ physicalSize)) = true := by
    cases guard : plan.valid && (plan.keeperBytes.size == plan.keeperSize) && decide (plan.keeperSize ≤ physicalSize)
    · simp [finishBoundedMarkedOpen, guard, throw, throwThe, MonadExceptOf.throw, EStateM.throw, Bind.bind, EStateM.bind] at returned
    · rfl
  obtain ⟨valid, size, bounded⟩ : plan.valid = true ∧ plan.keeperBytes.size = plan.keeperSize ∧ plan.keeperSize ≤ physicalSize := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using guarded
  refine ⟨valid, size, bounded, ?_⟩
  let fast := plan.newer.isEmpty && physicalSize == plan.keeperSize
  change ∃ authorized, sync #[directory.path] entry = .ok () authorized ∧ (if fast then _ else _)
  simp only [finishBoundedMarkedOpen, guarded, ite_true, Bind.bind] at returned
  change ((if fast then _ else _) : EStateM IO.Error heap Unit) entry = _ at returned
  by_cases short : fast = true
  · simp only [short, ite_true] at returned ⊢
    cases root : sync #[directory.path] entry with
    | error cause failed => simp [root, EStateM.bind] at returned
    | ok result authorized =>
      cases result
      exact ⟨authorized, rfl, by simpa only [Bind.bind, EStateM.bind, root] using returned⟩
  · have notFast : fast = false := Bool.eq_false_iff.mpr short
    simp only [notFast, Bool.false_eq_true, ite_false, runRepairPlan, Bind.bind, EStateM.bind] at returned ⊢
    cases root : sync #[directory.path] entry with
    | error cause failed => simp [root] at returned
    | ok result authorized =>
      cases result
      have schedule : ((steps plan.newer (decide (plan.keeperSize < physicalSize))).forM run) authorized =
          .ok () reached := by simpa only [root] using returned
      unfold steps at schedule
      rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at schedule
      cases pruneReturn : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) authorized with
      | error cause after => simp [Bind.bind, EStateM.bind, pruneReturn] at schedule
      | ok result pruned =>
        cases result
        refine ⟨authorized, rfl, pruned, pruneReturn, ?_⟩
        by_cases longer : plan.keeperSize < physicalSize
        · simp only [longer, ite_true]
          simpa only [Bind.bind, EStateM.bind, pruneReturn, decide_eq_true longer, ite_true] using schedule
        · simp only [longer, ite_false]
          simp [Bind.bind, EStateM.bind, pruneReturn, longer, run, performPaths, List.forM_eq_forM,
            List.forM_cons, List.forM_nil, Pure.pure, EStateM.pure] at schedule
          cases kept : sync #[directory.file (.walSegment plan.keeper)] pruned with
          | error cause failed => simp [kept] at schedule
          | ok result after =>
            cases result
            simpa only [kept] using schedule

/-- Fold only the accepted removes of the actual WAL unlink loop,
in their original order and at the heap returned by each call. -/
theorem foldReturnedWalUnlinks {heap model : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (invariant : model → heap → Prop) (applyUnlink : model → Nat → model)
    {initial : model} {first last : heap} (entered : invariant initial first)
    (unlink : ∀ {ordinal start finish result before}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      invariant before start → invariant (applyUnlink before ordinal) finish)
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    invariant (plan.newer.foldl applyUnlink initial) last := by
  let run := performPaths directory plan remove throw write sync rename
  have preserve {ordinals : List Nat} (included : ∀ ordinal ∈ ordinals, ordinal ∈ plan.newer)
      {start finish : heap} {before : model} (known : invariant before start)
      (ran : ((ordinals.map Step.unlink).forM run) start = .ok () finish) :
      invariant (ordinals.foldl applyUnlink before) finish := by
    induction ordinals generalizing start before with
    | nil =>
      have same : start = finish := (EStateM.Result.ok.inj ran).2
      exact same ▸ known
    | cons ordinal rest ih =>
      simp only [List.map_cons, List.forM_eq_forM, List.forM_cons, run, performPaths,
        RunCollection.performPaths, Bind.bind, EStateM.bind] at ran
      cases removed : remove (directory.file (.walSegment ordinal)) start with
      | error cause reached => simp [removed] at ran
      | ok result reached =>
        rw [removed] at ran
        cases accepted : RunCollection.ownedUnlinkResult result with
        | error cause =>
          simp [accepted, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at ran
        | ok value =>
          cases value
          simp only [accepted, Pure.pure, EStateM.pure] at ran
          exact ih (fun other member => included other (List.mem_cons_of_mem _ member))
            (unlink (included _ List.mem_cons_self) removed accepted known) ran
  exact preserve (fun _ member => member) entered returned

/-- Each selected name is absent after the actual checked unlink pass.
Only paths in the caller's canonical scope need the off-target frame. -/
theorem namesOfReturnedWalUnlinks {heap : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (names : heap → FilePath → Option Nat) (scope : FilePath → Prop)
    (inScope : ∀ ordinal ∈ plan.newer, scope (directory.file (.walSegment ordinal)))
    (unlink : ∀ {ordinal start finish result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      names finish (directory.file (.walSegment ordinal)) = none ∧
      ∀ path, scope path → path ≠ directory.file (.walSegment ordinal) → names finish path = names start path)
    {first last : heap}
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    (∀ ordinal ∈ plan.newer, names last (directory.file (.walSegment ordinal)) = none) ∧
    ∀ path, scope path → (∀ ordinal ∈ plan.newer, path ≠ directory.file (.walSegment ordinal)) →
      names last path = names first path := by
  let invariant (removed : List Nat) (atHeap : heap) :=
    (∀ ordinal ∈ plan.newer, ordinal ∈ removed → names atHeap (directory.file (.walSegment ordinal)) = none) ∧
    ∀ path, scope path → (∀ ordinal ∈ removed, path ≠ directory.file (.walSegment ordinal)) →
      names atHeap path = names first path
  have start : invariant [] first := ⟨by simp, fun _ _ _ => rfl⟩
  have step {ordinal : Nat} {before after : heap} {result : Except IO.Error Unit} {removed : List Nat}
      (selected : ordinal ∈ plan.newer) (called : remove (directory.file (.walSegment ordinal)) before = .ok result after)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (prior : invariant removed before) :
      invariant (removed ++ [ordinal]) after := by
    obtain ⟨gone, unchanged⟩ := prior
    obtain ⟨absent, keeps⟩ := unlink selected called accepted
    constructor
    · intro other eligible member
      by_cases same : other = ordinal
      · simpa only [same] using absent
      · have earlier : other ∈ removed := by simpa only [List.mem_append, List.mem_singleton, same, or_false] using member
        have apart : directory.file (.walSegment other) ≠ directory.file (.walSegment ordinal) :=
          fun collision => same (directory.walSegment_path_injective collision)
        exact (keeps _ (inScope other eligible) apart).trans (gone other eligible earlier)
    · intro path inside outside
      exact (keeps path inside (outside ordinal (List.mem_append_right _ (List.mem_singleton_self _)))).trans
        (unchanged path inside (fun other member => outside other (List.mem_append_left _ member)))
  have complete : invariant plan.newer last := by
    simpa [← List.flatMap_def] using
      foldReturnedWalUnlinks directory plan remove write sync rename invariant
        (fun done ordinal => done ++ [ordinal]) start step returned
  exact ⟨fun ordinal member => complete.1 ordinal member member, complete.2⟩

/-- A successful aligned finish with no later names uses exactly the
directory barrier followed by the barrier on its existing keeper. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_alignedSyncsReached {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {entry reached : heap}
    (aligned : physicalSize = plan.keeperSize) (noneLater : plan.newer = [])
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached) :
    ∃ afterDirectory, sync #[directory.path] entry = .ok () afterDirectory ∧
      sync #[directory.file (.walSegment plan.keeper)] afterDirectory = .ok () reached := by
  have ⟨_, _, _, authorized⟩ :=
    finishBoundedMarkedOpen_reachedSuccess directory plan physicalSize remove write sync rename returned
  simpa [aligned, noneLater] using authorized

structure AlignedKeeperCacheCallbacks (heap : Type) where
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  readChunk : IO.FS.Handle → USize → EStateM IO.Error heap ByteArray
  modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
    (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit
  getDirectory : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  getPending : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  setPending : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  getActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  sync : IO.FS.Handle → EStateM IO.Error heap Unit

namespace AlignedKeeperCacheCallbacks

variable {heap : Type} (calls : AlignedKeeperCacheCallbacks heap)

/-- Interpret the native keeper reader with a pending cell allocated by
the same opener. -/
def readKeeper (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath)
    (count size : Nat) : EStateM IO.Error heap ByteArray :=
  readKeeperWith calls.openRead
    (fun handle size => readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (calls.readChunk handle) size ByteArray.empty)
    (fun name handle => calls.modifyPending pending (pushPending name handle)) path count size

def syncPaths (directory : FilePath) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (paths : Array FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun path => syncWithHandles directory path (calls.getDirectory cached)
    (calls.getPending pending) (calls.setPending pending) (calls.getActive active) calls.openRead calls.sync) paths

theorem readsAligned {pending path count before opened read remembered keeper bytes}
    (fits : count < USize.size)
    (openedKeeper : calls.openRead path before = .ok keeper opened)
    (readKeeper : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (calls.readChunk keeper)
      count ByteArray.empty opened = .ok bytes read)
    (rememberedKeeper : calls.modifyPending pending (pushPending path keeper) read = .ok () remembered) :
    calls.readKeeper pending path count count before = .ok bytes remembered := by
  simp [AlignedKeeperCacheCallbacks.readKeeper, readKeeperWith, Bind.bind, EStateM.bind, fits, openedKeeper,
    readKeeper, rememberedKeeper, Pure.pure, EStateM.pure]

theorem syncsDirectory {dir cached active pending before after handle}
    (loaded : calls.getDirectory cached before = .ok (some handle) before)
    (synced : calls.sync handle before = .ok () after) :
    calls.syncPaths dir cached active pending #[dir] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, synced, Pure.pure, EStateM.pure]

/-- A pending keeper bypasses the active cell and any fallback open.
The removal from the pending cell precedes fsync. -/
theorem syncsPendingKeeper {dir path cached active pending before consumed after handle}
    (separate : path ≠ dir)
    (loaded : calls.getPending pending before = .ok [(path, handle)] before)
    (cleared : calls.setPending pending [] before = .ok () consumed)
    (synced : calls.sync handle consumed = .ok () after) :
    calls.syncPaths dir cached active pending #[path] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, separate, loaded, cleared, synced, Pure.pure, EStateM.pure]

/-- The actual aligned finisher uses the original cached root and the
keeper surfaced by the preceding read. The root barrier frames the
pending names, and the keeper fsync follows removal of all matches. -/
theorem alignedRepairSyncs {image : Type} (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {readHeap entry reached : heap} {root keeper : IO.FS.Handle}
    (aligned : physicalSize = plan.keeperSize) (noneLater : plan.newer = [])
    (cachedRoot : view.directory entry cached = some root)
    (remembered : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry)
    (recordsKeeper : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry →
      view.pending entry pending = pushPending (directory.file (.walSegment plan.keeper)) keeper (view.pending readHeap pending))
    (readsDirectory : ∀ {result issued}, calls.getDirectory cached entry = .ok result issued →
      result = view.directory entry cached ∧ view.pending issued pending = view.pending entry pending)
    (syncKeepsPending : ∀ {issued after}, calls.sync root issued = .ok () after →
      view.pending after pending = view.pending issued pending)
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write
      (calls.syncPaths directory.path cached active pending) rename entry = .ok () reached) :
    let path := directory.file (.walSegment plan.keeper)
    ∃ (rootIssued afterDirectory : heap) (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getDirectory cached entry = .ok (some root) rootIssued ∧
      calls.sync root rootIssued = .ok () afterDirectory ∧
      calls.getPending pending afterDirectory = .ok entries loaded ∧
      entries.find? (fun item => item.1 == path) = some (path, keeper) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed ∧
      calls.sync keeper consumed = .ok () reached := by
  intro path
  obtain ⟨afterDirectory, rootBarrier, keeperBarrier⟩ :=
    finishBoundedMarkedOpen_alignedSyncsReached directory plan physicalSize remove write
      (calls.syncPaths directory.path cached active pending) rename aligned noneLater returned
  let syncer : RawSyncCalls heap :=
    ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  change syncer.group directory.path cached active pending #[directory.path] entry = .ok () afterDirectory at rootBarrier
  change syncer.group directory.path cached active pending #[path] afterDirectory = .ok () reached at keeperBarrier
  obtain ⟨directoryHandle, issued, loadedRoot, syncedRoot⟩ := syncer.rootGroupReturned rootBarrier
  obtain ⟨sameRoot, pendingFromRead⟩ := readsDirectory loadedRoot
  have sameHandle := Option.some.inj (sameRoot.trans cachedRoot)
  subst directoryHandle
  have pendingFromRemember :=
    (syncKeepsPending syncedRoot).trans (pendingFromRead.trans (recordsKeeper remembered))
  have selects {entries loaded} (read : syncer.readPending pending afterDirectory = .ok entries loaded) :
      entries.find? (fun item => item.1 == path) = some (path, keeper) := by
    rw [readsPending read, pendingFromRemember]
    simp [path, pushPending]
  obtain ⟨entries, loaded, consumed, got, chosen, removed, synced⟩ :=
    syncer.pendingGroupReturned (file_ne_directory directory (.walSegment plan.keeper)) selects keeperBarrier
  exact ⟨issued, afterDirectory, entries, loaded, consumed, loadedRoot, syncedRoot, got, chosen, removed, synced⟩

end AlignedKeeperCacheCallbacks

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type}

private def keeperPath (directory : DiskDirectory) (first : Nat) : FilePath :=
  directory.file (.walSegment first)

/-- The raw keeper callbacks use the cells from the preceding cache
allocation. Earlier checkpoint and WAL reads reach the given entry
census. The directory and keeper fsyncs carry their own file and slot
effects, including the keeper's observed drops after the second fsync. -/
structure AlignedKeeperCacheReport
    (finish : CapturedAlignedFinish calls reads vacant selected)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (cacheEntry : heap)
    (seed : OpenSyncCacheAllocations admission.opened view init cacheEntry)
    (callbacks : AlignedKeeperCacheCallbacks heap) (entry : heap) where
  keeper : IO.FS.Handle
  opened : heap
  read : heap
  remembered : heap
  authorized : heap
  consumed : heap
  reached : heap
  entryDirectory : view.directory entry seed.directoryRef = view.directory seed.afterPending seed.directoryRef
  entryActive : view.active entry seed.activeRef = view.active seed.afterPending seed.activeRef
  entryPending : view.pending entry seed.pendingRef = view.pending seed.afterPending seed.pendingRef
  entryFiles : view.files entry = admission.held
  entryCensus : view.descriptors entry = finish.readCustody.atOpen
  rawOpen : callbacks.openRead (keeperPath directory layout.keeper.first) entry = .ok keeper opened
  rawKeeper : view.handle opened keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
  openedCensus : view.descriptors opened = reads.wal.keeper.calls.inventory
  rawRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (callbacks.readChunk keeper)
    layout.keeper.bytes.size ByteArray.empty opened = .ok layout.keeper.bytes read
  readFiles : view.files read = admission.held
  readCensus : view.descriptors read = finish.readCustody.afterRead
  rawRemember : callbacks.modifyPending seed.pendingRef (pushPending (keeperPath directory layout.keeper.first) keeper)
    read = .ok () remembered
  rememberFrame : view.files remembered = view.files read ∧ view.descriptors remembered = view.descriptors read
  directoryLoad : callbacks.getDirectory seed.directoryRef remembered = .ok (some seed.handle) remembered
  sameDirectory : view.handle remembered seed.handle = (admission.reached, admission.cached, 0)
  directorySync : callbacks.sync seed.handle remembered = .ok () authorized
  authorizedFiles : view.files authorized = { admission.held with image := retry.image.syncDirectory }
  authorizedCensus : view.descriptors authorized = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization
  pendingLoad : callbacks.getPending seed.pendingRef authorized =
    .ok [(keeperPath directory layout.keeper.first, keeper)] authorized
  consume : callbacks.setPending seed.pendingRef [] authorized = .ok () consumed
  consumeFrame : view.files consumed = view.files authorized ∧ view.descriptors consumed = view.descriptors authorized
  sameKeeper : view.handle consumed keeper = view.handle opened keeper
  keeperSync : callbacks.sync keeper consumed = .ok () reached
  reachedFiles : view.files reached = { admission.held with image := retry.image.syncDirectory.syncKeeper }
  reachedCensus : view.descriptors reached = finish.census
  directoryKept : view.directory reached seed.directoryRef = view.directory entry seed.directoryRef
  activeKept : view.active reached seed.activeRef = view.active entry seed.activeRef
  pendingConsumed : view.pending reached seed.pendingRef = []
  directoryHandleKept : view.handle reached seed.handle = view.handle remembered seed.handle

variable {finish : CapturedAlignedFinish calls reads vacant selected}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}

def AlignedKeeperCacheReport.schedule
    (_seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : EStateM IO.Error heap Unit :=
    let path := keeperPath directory layout.keeper.first
    let size := reads.wal.keeper.calls.metadata.byteSize.toNat
    let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    do
      let _ ← callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size
      finishBoundedMarkedOpen directory layout.boundedPlan size remove write sync rename

private theorem alignedExtent (finish : CapturedAlignedFinish calls reads vacant selected) :
    layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat := by
  have exactSize := finish.repair.aligned
  rw [finish.sameKeeper] at exactSize
  exact exactSize

/-- The actual keeper reader returns the selected bytes at the heap
where it has just remembered the original read handle. -/
theorem AlignedKeeperCacheReport.readsKeeper
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry) :
    callbacks.readKeeper seed.pendingRef (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat entry =
      .ok layout.keeper.bytes seen.remembered := by
  rw [← alignedExtent finish]
  exact callbacks.readsAligned reads.wal.keeperFits seen.rawOpen seen.rawRead seen.rawRemember

/-- Both barriers start at the heap returned by the keeper reader.
The bounded finisher uses the pending handle already held there. -/
theorem AlignedKeeperCacheReport.repairsAfterRead
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write (callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename
      seen.remembered = .ok () seen.reached := by
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have sizeEq := (alignedExtent finish).symm.trans bytes
  have noLater : layout.boundedPlan.newer = [] := finish.repair.noLater
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq bytes.symm, by simp [noLater]⟩
  have separate := file_ne_directory directory (.walSegment layout.keeper.first)
  have directorySelected : sync #[directory.path] seen.remembered = .ok () seen.authorized :=
    callbacks.syncsDirectory seen.directoryLoad seen.directorySync
  have selectedKeeper : sync #[directory.file (.walSegment layout.keeper.first)] seen.authorized = .ok () seen.reached :=
    callbacks.syncsPendingKeeper separate seen.pendingLoad seen.consume seen.keeperSync
  change finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write sync rename seen.remembered = _
  simp only [finishBoundedMarkedOpen, sizeEq, valid, bytes, Bind.bind, EStateM.bind,
    beq_self_eq_true, decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, noLater, List.isEmpty_nil,
    directorySelected]
  exact selectedKeeper

/-- Read the marked prefix and execute the two actual aligned barriers.
The sync of the original keeper consumes its remembered reference before
issuing fsync on that same handle. -/
theorem AlignedKeeperCacheReport.returns
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    seen.schedule remove write rename entry = .ok () seen.reached ∧
    view.handle seen.consumed seen.keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0) ∧
    view.files seen.consumed = { admission.held with image := retry.image.syncDirectory } ∧
    view.descriptors seen.consumed = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization ∧
    (view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef,
      view.descriptors seen.reached, view.files seen.reached) =
      (admission.cache, finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  refine ⟨?_, seen.sameKeeper.trans seen.rawKeeper, seen.consumeFrame.1.trans seen.authorizedFiles,
    seen.consumeFrame.2.trans seen.authorizedCensus, ?_⟩
  · simpa only [schedule, keeperPath, Bind.bind, EStateM.bind, seen.readsKeeper] using
      seen.repairsAfterRead remove write rename
  · simp only [OpenCloseHeapView.cacheAt, seen.directoryKept, seen.entryDirectory,
      seed.directoryKept, seed.directorySet, seen.activeKept, seen.entryActive, seed.activeKept, seed.activeSet,
      seen.pendingConsumed, Option.map_some, Option.map_none, List.map_nil, seen.directoryHandleKept, seen.sameDirectory,
      seen.reachedFiles, seen.reachedCensus, CensusOpenAdmissionReports.cache]

end Alvoki.Storage.DiskSession
