import Alvoki.Storage.Disk.NativeRawOpenCacheDisposal
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem openCacheConstructor (path : FilePath) :
    ∃ makeCache : IO.Ref (Option IO.FS.Handle) →
        IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles,
      DiskTable.OpenSyncFiles.IsOpenAction path
        (openSyncFilesWith (m := IO) (IO.FS.Handle.mk path .read)
          (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
          (fun value => liftM (IO.mkRef value)) makeCache) ∧
      ∀ cached active pending, (makeCache cached active pending).UsesCacheReferences active pending cached ∧
        (makeCache cached active pending).AtDirectory path := by
  obtain ⟨_, makeCache, opens, source, references⟩ := DiskTable.openSyncCacheReferences path
  exact ⟨makeCache, source ▸ opens, references⟩

/-- Primitive callbacks of the marked open interpreter, fixed before any
admission. The cache references and lock are allocated by that admission. -/
structure RawMarkedOpenInterpreter (heap stream : Type) where
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  keeperCallbacks : AlignedKeeperCacheCallbacks heap
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  stage : LongKeeperStageCallbacks heap
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  dispose : DiskTable.OpenSyncFiles → EStateM IO.Error heap Unit
  release : IO.FS.Handle → heap → heap

namespace RawMarkedOpenInterpreter

/-- The cache assembler comes from the native initializer for the
resolved directory. Its argument order is the order of allocation. -/
noncomputable def makeCache (directory : DiskDirectory) :=
  Classical.choose (openCacheConstructor directory.path)

theorem cacheReferences (directory : DiskDirectory) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) :
    (makeCache directory cached active pending).UsesCacheReferences active pending cached ∧
    (makeCache directory cached active pending).AtDirectory directory.path :=
  (Classical.choose_spec (openCacheConstructor directory.path)).2 cached active pending

theorem cacheAction (directory : DiskDirectory) :
    DiskTable.OpenSyncFiles.IsOpenAction directory.path
      (openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) (makeCache directory)) :=
  (Classical.choose_spec (openCacheConstructor directory.path)).1

noncomputable def assemble (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) :=
  Classical.choose (show ∃ construct, DiskTable.OpenReferenceAssembly directory lock cache construct from
    ⟨_, DiskTable.openReferenceAssembly directory lock cache⟩)

theorem assembles (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) :
    DiskTable.OpenReferenceAssembly directory lock cache (assemble directory lock cache) :=
  Classical.choose_spec _

variable {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream)

/-- The held continuation uses the refs allocated by the current
initializer. It runs the segmented recovery guard before dispatch. -/
noncomputable def worker (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) :
    EStateM IO.Error heap DiskTable := do
  let opened ← recoverHealthyMarkedWithRefs source.fileCalls source.directoryCalls source.keeperCallbacks
    cached active pending source.remove source.stage source.rename source.calls.lookup directory
    (source.bootstrap directory cache)
  installReady opened.installed source.allocatePhase source.allocateToken fun phase token =>
    pure (assemble directory lock cache phase token)

/-- Keep the cache initialization and the worker in one interpretation
of the open schedule. The cache drop precedes unlock on a worker error,
and the owning handle is released only on error. -/
noncomputable def openTable (input : FilePath) : EStateM IO.Error heap DiskTable :=
  DiskTable.withOpenAdmission input source.calls.realPath source.calls.lookup source.calls.openAppend fun directory lock =>
    finishFailedOpen
      (openWithLock (source.calls.flock lock) (fun _ => IO.userError s!"database already open: {directory.path}")
        (fun _ => source.calls.unlock lock) fun _ => do
          let (cache, cached, active, pending) ← openSyncFilesWith
            (source.init.openDirectory directory.path) source.init.newRef source.init.newRef source.init.newRef
            (fun cached active pending => (makeCache directory cached active pending, cached, active, pending))
          tryCatchThe IO.Error (source.worker cached active pending directory lock cache) fun cause => do
            source.dispose cache
            throw cause)
      source.release lock

/-- Record only actual failed calls of this interpreter. Each caller
starts at the heap returned by the preceding call. -/
inductive FailedCalls (source : RawMarkedOpenInterpreter heap stream) (first : heap) :
    List (FilePath × IO.Error) → heap → Prop where
  | empty : FailedCalls source first [] first
  | next {earlier : List (FilePath × IO.Error)} {entry reached : heap} {diagnostic : IO.Error}
      (prior : FailedCalls source first earlier entry) (input : FilePath)
      (returned : source.openTable input entry = .error diagnostic reached) :
      FailedCalls source first (earlier ++ [(input, diagnostic)]) reached

theorem FailedCalls.append {source : RawMarkedOpenInterpreter heap stream} {first middle last : heap}
    {earlier later : List (FilePath × IO.Error)} (before : FailedCalls source first earlier middle)
    (after : FailedCalls source middle later last) : FailedCalls source first (earlier ++ later) last := by
  induction after with
  | empty => simpa using before
  | next _ input returned ih =>
    rw [← List.append_assoc]
    exact .next ih input returned

end RawMarkedOpenInterpreter

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory inventory retry}

private theorem RawOpenAdmissionReport.markedInterpreterStarts
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock) :
    let cache := RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef
    let worker := source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock cache
    let inner := tryCatchThe IO.Error worker fun cause => do
      source.dispose cache
      throw cause
    source.openTable input entry =
      finishFailedOpen (tryCatchThe IO.Error inner fun cause => do
        source.calls.unlock raw.lock
        throw cause) source.release raw.lock seed.afterPending := by
  unfold RawMarkedOpenInterpreter.openTable
  rw [DiskTable.withOpenAdmission_lockOpen source.calls.realPath source.calls.lookup source.calls.openAppend _
      raw.resolved raw.flat raw.lockProbe admission.safe, raw.appended]
  simp only [finishFailedOpen, openWithLock, Bind.bind, EStateM.bind, raw.acquired, ↓reduceIte, MonadExcept.tryCatch,
    tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, openSyncFilesWith, seed.rawOpened, seed.directoryAllocated,
    seed.activeAllocated, seed.pendingAllocated, Pure.pure, EStateM.pure]

/-- A healthy return transfers the original lock and cache to the
table. No error cleanup runs after this worker result. -/
theorem RawOpenAdmissionReport.returnsHealthyMarkedInterpreter
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    {table : DiskTable} {reached : heap}
    (worker : source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
      (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      seed.afterPending =
      .ok table reached) :
    source.openTable input entry = .ok table reached := by
  rw [raw.markedInterpreterStarts source seed]
  simp only [finishFailedOpen, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker]

variable {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- A returned worker error follows the same fixed interpreter up to
the worker, then uses its cache drop, unlock and lock drop in order. -/
theorem RawOpenCacheDisposal.returnsMarkedInterpreter
    (source : RawMarkedOpenInterpreter heap stream)
    {raw : RawOpenAdmissionReport admission view source.calls entry}
    {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
    {before : heap} (seen : RawOpenCacheDisposal (admitted := raw) seed before)
    (sameDisposal : source.dispose = seen.dispose)
    {cause : IO.Error}
    (worker : source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
      (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      seed.afterPending =
      .error cause before)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner seen.reached) :
    source.openTable input entry = .error (seen.diagnostic cause) finalized.reached := by
  have uses := (RawMarkedOpenInterpreter.cacheReferences directory seed.directoryRef seed.activeRef seed.pendingRef).1
  rw [raw.markedInterpreterStarts source seed]
  simp only [finishFailedOpen, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker,
    EStateM.Backtrackable.restore, EStateM.dummyRestore, Bind.bind, EStateM.bind, sameDisposal, seen.disposed _ uses,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, seen.unlocked]
  cases reported : seen.unlockResult with
  | error diagnostic => simp only [reported, RawOpenCacheDisposal.diagnostic, finalized.finalized]
  | ok value =>
    cases value
    simp only [reported, RawOpenCacheDisposal.diagnostic, finalized.finalized]

/-- The canonical path and three allocated references identify the cache. -/
private theorem sameCacheAtReferences {left right : DiskTable.OpenSyncFiles}
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {directory : IO.Ref (Option IO.FS.Handle)} {path : FilePath}
    (leftUses : left.UsesCacheReferences active pending directory) (leftPath : left.AtDirectory path)
    (rightUses : right.UsesCacheReferences active pending directory) (rightPath : right.AtDirectory path) : left = right := by
  cases left
  cases right
  simp_all [DiskTable.OpenSyncFiles.UsesCacheReferences, DiskTable.OpenSyncFiles.AtDirectory]

section

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}

/-- A returned healthy open whose callbacks and cache are the fixed
interpreter's runs through that interpreter at exactly the same heap. -/
theorem RawHealthyMarkedOpenEffects.returnsFixedInterpreterOfRun
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawHealthyMarkedOpenEffects opening view source.calls source.init entry phaseIdentity tokenIdentity
      source.allocatePhase source.allocateToken stream source.remove source.stage source.rename)
    (files : raw.fileCalls = source.fileCalls) (directoryReads : raw.directoryCalls = source.directoryCalls)
    (keeper : raw.callbacks = source.keeperCallbacks)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ dir lock cache, DiskTable.OpenReferenceAssembly dir lock cache (assemble dir lock cache))
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (cacheUses : let cache := makeCache raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
      cache.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef raw.seed.directoryRef ∧ cache.AtDirectory directory.path)
    {table : DiskTable} {reached : heap}
    (returned : raw.openTable source.bootstrap assemble makeCache = .ok table reached) :
    source.openTable input entry = .ok table reached := by
  let cache := makeCache raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
  let fixed := RawMarkedOpenInterpreter.makeCache directory raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
  have uses := RawMarkedOpenInterpreter.cacheReferences directory raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
  have sameCache : cache = fixed := sameCacheAtReferences cacheUses.1 cacheUses.2 uses.1 uses.2
  have sameTable : assemble directory raw.raw.lock fixed = RawMarkedOpenInterpreter.assemble directory raw.raw.lock fixed :=
    (constructs directory raw.raw.lock fixed).trans (RawMarkedOpenInterpreter.assembles directory raw.raw.lock fixed).symm
  have initialized : openSyncFilesWith (source.init.openDirectory directory.path)
      source.init.newRef source.init.newRef source.init.newRef makeCache raw.raw.afterFlock =
      .ok cache raw.seed.afterPending := by
    simp only [openSyncFilesWith, Bind.bind, EStateM.bind, raw.seed.rawOpened, raw.seed.directoryAllocated,
      raw.seed.activeAllocated, raw.seed.pendingAllocated, Pure.pure, EStateM.pure, cache]
  let recover := fun resolved lock cache => do
    let opened ← recoverHealthyMarkedWithRefs raw.fileCalls raw.directoryCalls raw.callbacks raw.seed.directoryRef
      raw.seed.activeRef raw.seed.pendingRef source.remove source.stage source.rename source.calls.lookup resolved
      (source.bootstrap resolved cache)
    installReady opened.installed source.allocatePhase source.allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))
  change source.calls.runOpen input source.init makeCache recover entry = .ok table reached at returned
  rw [raw.raw.startsHeldWorker source.init raw.seed initialized recover, sameCache] at returned
  apply raw.raw.returnsHealthyMarkedInterpreter source raw.seed
  have fixedWorker : recover directory raw.raw.lock fixed =
      source.worker raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef directory raw.raw.lock fixed := by
    unfold RawMarkedOpenInterpreter.worker
    simp only [recover, files, directoryReads, keeper, sameTable]
  rw [fixedWorker] at returned
  cases worker : source.worker raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef directory raw.raw.lock fixed
      raw.seed.afterPending with
  | ok table heap =>
    simpa only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker] using returned
  | error diagnostic heap =>
    simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
    cases unlocked : source.calls.unlock raw.raw.lock heap <;> simp [unlocked] at returned

end

end Alvoki.Storage.DiskSession
