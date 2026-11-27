import Alvoki.Storage.Disk.NativeLongKeeperRepairPrefix
import Alvoki.Storage.Disk.NativeRawOpenCacheDisposal
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

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


/-- The marked reader returns both the installable replay and the measured
physical extent used to choose the keeper repair. -/
noncomputable abbrev markedPreparation (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (directory : DiskDirectory) :=
  let keeper := source.keeperCallbacks.withFileReads source.fileCalls
  let read := source.fileCalls.readOptional directory
  prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (read (directory.file .manifest))
      source.fileCalls.runSize source.fileCalls.runPrefix) read
    (fun watermark length => readSelectedWithCachedExtents directory watermark length source.directoryCalls.run
      (MarkedWalExtentReports.inspect source.fileCalls) source.fileCalls.seal
      (source.fileCalls.readKeeperWithRelease (fun path handle => keeper.modifyPending pending (pushPending path handle))))

private noncomputable def interpretWorker {state : Type}
    (ordinary : {α : Type} → EStateM IO.Error heap α → EStateM IO.Error state α)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cache : DiskTable.OpenSyncFiles) (repair : Plan → Nat → EStateM IO.Error state Unit) :
    EStateM IO.Error state DiskTable := do
  let reopened ← recoverSegmentedWalWith
    (ordinary (rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))))
    (ordinary (optionalMetadataWith (source.calls.lookup (directory.file .walBoundary))))
    (do
      let (plan, opened, extent) ← ordinary (source.markedPreparation pending directory)
      repair plan extent
      pure opened)
    (ordinary (source.bootstrap directory cache))
  ordinary (installReady reopened.installed source.allocatePhase source.allocateToken
    fun phase token => pure (assemble directory lock cache phase token))

private def outsideRepair (action : EStateM IO.Error heap α) : EStateM IO.Error (heap × Option heap) α :=
  fun (before, _) => match action before with
    | .ok value after => .ok value (after, none)
    | .error error after => .error error (after, none)

/-- Interpret the held worker, retaining a successful replacement rename only
on errors inside repair. Installation can report the same error on the same
heap after a successful repair. It starts outside the observed interval. -/
noncomputable def workerObservingRepairRename (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : DiskDirectory)
    (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) (entry : heap) :=
  let keeper := source.keeperCallbacks.withFileReads source.fileCalls
  source.interpretWorker outsideRepair pending directory lock cache
    (fun plan extent (prepared, _) => LongKeeperRepair.observeRename directory plan extent source.remove
      (source.stage.stage pending keeper.modifyPending) (keeper.syncPaths directory.path cached active pending)
      source.rename prepared) (entry, none)

/-- A rename-tagged worker error identifies the successful preparation and the
failed finisher at its returned heap, before installation can run. -/
theorem worker_observesRepairError_iff (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cache : DiskTable.OpenSyncFiles)
    {entry checked marked : heap} {metadata : IO.FS.Metadata} {cause : IO.Error} {failed renamed : heap}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      entry = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
      .ok (some metadata) marked) :
    let keeper := source.keeperCallbacks.withFileReads source.fileCalls
    source.workerObservingRepairRename cached active pending directory lock cache entry =
        .error cause (failed, some renamed) ↔
      ∃ plan opened extent prepared, source.markedPreparation pending directory marked =
          .ok (plan, opened, extent) prepared ∧
        LongKeeperRepair.observeRename directory plan extent source.remove (source.stage.stage pending keeper.modifyPending)
          (keeper.syncPaths directory.path cached active pending) source.rename prepared =
          .error cause (failed, some renamed) := by
  intro keeper
  simp only [workerObservingRepairRename, interpretWorker, recoverSegmentedWalWith, Bind.bind, EStateM.bind,
    outsideRepair, flat, marker, Option.isSome, ↓reduceIte]
  cases h : source.markedPreparation pending directory marked with
  | error cause reached => simp
  | ok payload prepared =>
    obtain ⟨plan, opened, extent⟩ := payload
    have select {P : Plan → Nat → heap → Prop} :
        (∃ p o n atHeap, (EStateM.Result.ok (plan, opened, extent) prepared :
          EStateM.Result IO.Error heap (Plan × Reopened × Nat)) = .ok (p, o, n) atHeap ∧ P p n atHeap) ↔
          P plan extent prepared := by
      constructor
      · rintro ⟨_, _, _, _, eq, fact⟩
        cases eq
        exact fact
      · exact fun fact => ⟨_, _, _, _, rfl, fact⟩
    rw [select]
    cases observed : LongKeeperRepair.observeRename directory plan extent source.remove
      (source.stage.stage pending keeper.modifyPending) (keeper.syncPaths directory.path cached active pending)
      source.rename prepared with
    | error why reached =>
      simp only [keeper] at observed ⊢
      simp [observed]
    | ok value reached =>
      simp only [keeper] at observed ⊢
      simp only [observed, Pure.pure, EStateM.pure]
      cases installReady opened.installed source.allocatePhase source.allocateToken
        (fun phase token => pure (assemble directory lock cache phase token)) reached.1 <;> simp

/-- Erasing the observation preserves the literal worker's result and heap
even outside the marked branch and through either allocation failure. -/
theorem forget_workerObservingRepairRename (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cache : DiskTable.OpenSyncFiles) (entry : heap) :
    LongKeeperRepair.forgetRename (source.workerObservingRepairRename cached active pending directory lock cache entry) =
      source.worker cached active pending directory lock cache entry := by
  let keeper := source.keeperCallbacks.withFileReads source.fileCalls
  let write := source.stage.stage pending keeper.modifyPending
  let sync := keeper.syncPaths directory.path cached active pending
  have outside {α : Type} (action : EStateM IO.Error heap α) : LongKeeperRepair.Erases (outsideRepair action) action := by
    intro before prior
    cases result : action before <;> simp [outsideRepair, result, LongKeeperRepair.forgetRename]
  change LongKeeperRepair.forgetRename _ =
    source.interpretWorker (fun action => action) pending directory lock cache
      (fun plan extent => finishBoundedMarkedOpen directory plan extent source.remove write sync source.rename) entry
  apply LongKeeperRepair.Erases.bind _ (fun opened => outside _) entry none
  apply LongKeeperRepair.Erases.bind (outside _) (fun _ => ?_)
  apply LongKeeperRepair.Erases.bind (outside _) (fun metadata => ?_)
  cases metadata with
  | none => exact outside _
  | some _ =>
    apply LongKeeperRepair.Erases.bind (outside _) (fun payload => ?_)
    obtain ⟨plan, opened, extent⟩ := payload
    apply LongKeeperRepair.Erases.bind _ (fun _ _ _ => rfl)
    exact fun prepared _ => LongKeeperRepair.forget_observeRename directory plan extent source.remove write sync
      source.rename prepared

/-- Open the directory and allocate the three references used by the held worker. -/
noncomputable abbrev cacheInitialization (directory : DiskDirectory) :=
  openSyncFilesWith (source.init.openDirectory directory.path) source.init.newRef source.init.newRef source.init.newRef
    (fun cached active pending => (makeCache directory cached active pending, cached, active, pending))

/-- Keep the cache initialization and the worker in one interpretation
of the open schedule. The cache drop precedes unlock on a worker error,
and the owning handle is released only on error. -/
noncomputable def openTable (input : FilePath) : EStateM IO.Error heap DiskTable :=
  DiskTable.withOpenAdmission input source.calls.realPath source.calls.lookup source.calls.openAppend fun directory lock =>
    finishFailedOpen
      (openWithLock (source.calls.flock lock) (fun _ => IO.userError s!"database already open: {directory.path}")
        (fun _ => source.calls.unlock lock) fun _ => do
          let (cache, cached, active, pending) ← source.cacheInitialization directory
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

/-- The admissible part of the managed namespace is chosen by the actual
successful calls. The prefix retains the heap of every primitive. -/
theorem _root_.Alvoki.Storage.DiskTable.withOpenAdmission_reachedSuccess
    {heap handle result : Type} {input : FilePath} {entry reached : heap} {value : result}
    (realPath : FilePath → EStateM IO.Error heap FilePath)
    (lookup : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (openAppend : FilePath → EStateM IO.Error heap handle)
    (acquire : DiskDirectory → handle → EStateM IO.Error heap result)
    (returned : DiskTable.withOpenAdmission input realPath lookup openAppend acquire entry = .ok value reached) :
    ∃ (directory : DiskDirectory) (lock : handle) (lockMetadata : Option IO.FS.Metadata)
      (resolved checked probed locked : heap),
      DiskDirectory.openWith realPath input entry = .ok directory resolved ∧
      optionalMetadataWith (lookup (directory.file .wal)) resolved = .ok none checked ∧
      optionalMetadataWith (lookup (directory.file .lock)) checked = .ok lockMetadata probed ∧
      (∀ metadata, lockMetadata = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true) ∧
      openAppend (directory.file .lock) probed = .ok lock locked ∧ acquire directory lock locked = .ok value reached := by
  simp only [DiskTable.withOpenAdmission, Bind.bind, EStateM.bind, rejectFlatWalWith] at returned
  cases resolved : DiskDirectory.openWith realPath input entry with
  | error cause failed => simp [resolved] at returned
  | ok directory afterPath =>
    cases flat : optionalMetadataWith (lookup (directory.file .wal)) afterPath with
    | error cause failed => simp [resolved, flat] at returned
    | ok existing afterFlat =>
      cases existing with
      | some metadata =>
        simp [resolved, flat, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      | none =>
        cases lockProbe : optionalMetadataWith (lookup (directory.file .lock)) afterFlat with
        | error cause failed => simp [resolved, flat, lockProbe, Pure.pure, EStateM.pure] at returned
        | ok lockMetadata afterProbe =>
          have safe : ∀ metadata, lockMetadata = some metadata →
              (metadata.type == .file && metadata.numLinks == 1) = true := by
            intro metadata supplied
            rw [supplied] at lockProbe
            cases checked : (metadata.type == .file && metadata.numLinks == 1)
            · simp [resolved, flat, lockProbe, checkPrivateRegularWith, checked, Pure.pure, EStateM.pure,
                throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at returned
            · rfl
          cases opened : openAppend (directory.file .lock) afterProbe with
          | error cause failed =>
            cases lockMetadata with
            | none => simp [resolved, flat, lockProbe, opened, Pure.pure, EStateM.pure, EStateM.bind] at returned
            | some metadata =>
              have regular := safe metadata rfl
              simp [resolved, flat, lockProbe, opened, checkPrivateRegularWith, regular,
                Pure.pure, EStateM.pure, EStateM.bind] at returned
          | ok lock afterOpen =>
            have ran : acquire directory lock afterOpen = .ok value reached := by
              cases lockMetadata with
              | none =>
                simpa [resolved, flat, lockProbe, opened, Pure.pure, EStateM.pure, EStateM.bind] using returned
              | some metadata =>
                have regular := safe metadata rfl
                simpa [resolved, flat, lockProbe, opened, checkPrivateRegularWith, regular,
                  Pure.pure, EStateM.pure, EStateM.bind] using returned
            exact ⟨directory, lock, lockMetadata, afterPath, afterFlat, afterProbe, afterOpen, rfl, flat, lockProbe,
              safe, opened, ran⟩

/-- A failure of locking or of the held computation always returns an
error. A successful return thus retains both issued heaps. -/
theorem openWithLock_reachedSuccess {heap value : Type}
    (flock : EStateM IO.Error heap Bool) (already : Unit → IO.Error)
    (unlock : Unit → EStateM IO.Error heap Unit) (run : Unit → EStateM IO.Error heap value)
    {entry reached : heap} {answer : value}
    (returned : openWithLock flock already unlock run entry = .ok answer reached) :
    ∃ locked, flock entry = .ok true locked ∧ run () locked = .ok answer reached := by
  simp only [openWithLock, Bind.bind, EStateM.bind] at returned
  cases acquired : flock entry with
  | error cause failed => simp [acquired] at returned
  | ok result locked =>
    cases result with
    | false => simp [acquired, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
    | true =>
      cases held : run () locked with
      | ok table after =>
        exact ⟨locked, rfl, by
          simpa [acquired, Pure.pure, EStateM.pure, EStateM.bind, MonadExcept.tryCatch,
            tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, held]
            using returned⟩
      | error cause failed =>
        cases dropped : unlock () failed <;>
          simp [acquired, EStateM.bind, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
            EStateM.Backtrackable.restore, EStateM.dummyRestore, held, dropped, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw] at returned

/-- A successful initializer gives the exact newly opened directory
handle and the successive three reference allocation receipts. -/
theorem OpenSyncCacheCallbacks.reachedSuccess {heap result : Type}
    (init : OpenSyncCacheCallbacks heap) (directory : DiskDirectory)
    (assemble : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → result)
    {entry reached : heap} {value : result}
    (returned : openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef
      assemble entry = .ok value reached) :
    ∃ (root : IO.FS.Handle) (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
      (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (opened setDirectory setActive : heap),
      init.openDirectory directory.path entry = .ok root opened ∧
      init.newRef (some root) opened = .ok cached setDirectory ∧
      init.newRef none setDirectory = .ok active setActive ∧ init.newRef [] setActive = .ok pending reached ∧
      value = assemble cached active pending := by
  simp only [openSyncFilesWith, Bind.bind, EStateM.bind] at returned
  cases opened : init.openDirectory directory.path entry with
  | error cause failed => simp [opened] at returned
  | ok root afterOpen =>
    cases cached : init.newRef (some root) afterOpen with
    | error cause failed => simp [opened, cached] at returned
    | ok directoryCell afterDirectory =>
      cases active : init.newRef (none : Option (FilePath × IO.FS.Handle)) afterDirectory with
      | error cause failed => simp [opened, cached, active] at returned
      | ok activeCell afterActive =>
        cases pending : init.newRef ([] : List (FilePath × IO.FS.Handle)) afterActive with
        | error cause failed => simp [opened, cached, active, pending] at returned
        | ok pendingCell afterPending =>
          simp only [opened, cached, active, pending, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact ⟨root, directoryCell, activeCell, pendingCell, afterOpen, afterDirectory, afterActive,
            rfl, cached, active, pending, rfl⟩


/-- Follow the actual successful interpreter through admission and cache
allocation. No descriptor census or recovery evidence is needed to find
the issue and return heaps of those calls. -/
theorem RawMarkedOpenInterpreter.reachesHeldCache
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream) (input : FilePath)
    {entry reached : heap} {table : DiskTable}
    (returned : source.openTable input entry = .ok table reached) :
    ∃ (directory : DiskDirectory) (lock : IO.FS.Handle) (lockMetadata : Option IO.FS.Metadata)
      (resolved checked probed appended locked : heap)
      (root : IO.FS.Handle) (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
      (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (opened setDirectory setActive prepared : heap),
      DiskDirectory.openWith source.calls.realPath input entry = .ok directory resolved ∧
      optionalMetadataWith (source.calls.lookup (directory.file .wal)) resolved = .ok none checked ∧
      optionalMetadataWith (source.calls.lookup (directory.file .lock)) checked = .ok lockMetadata probed ∧
      (∀ metadata, lockMetadata = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true) ∧
      source.calls.openAppend (directory.file .lock) probed = .ok lock appended ∧
      source.calls.flock lock appended = .ok true locked ∧
      source.init.openDirectory directory.path locked = .ok root opened ∧
      source.init.newRef (some root) opened = .ok cached setDirectory ∧
      source.init.newRef none setDirectory = .ok active setActive ∧
      source.init.newRef [] setActive = .ok pending prepared ∧
      source.worker cached active pending directory lock
        (RawMarkedOpenInterpreter.makeCache directory cached active pending) prepared = .ok table reached := by
  let initCache := source.cacheInitialization
  let recover (directory : DiskDirectory) (lock : IO.FS.Handle) (_ : Unit) :
      EStateM IO.Error heap DiskTable := do
    let (cache, cached, active, pending) ← initCache directory
    tryCatchThe IO.Error (source.worker cached active pending directory lock cache) fun cause => do
      source.dispose cache
      throw cause
  let acquire (directory : DiskDirectory) (lock : IO.FS.Handle) :=
    openWithLock (source.calls.flock lock) (fun _ => IO.userError s!"database already open: {directory.path}")
      (fun _ => source.calls.unlock lock) (recover directory lock)
  change DiskTable.withOpenAdmission input source.calls.realPath source.calls.lookup source.calls.openAppend
    (fun directory lock => finishFailedOpen (acquire directory lock) source.release lock) entry = .ok table reached at returned
  obtain ⟨directory, lock, lockMetadata, resolved, checked, probed, appended, path, flat, probe, safe, lockOpen, held⟩ :=
    DiskTable.withOpenAdmission_reachedSuccess _ _ _ _ returned
  have locked : acquire directory lock appended = .ok table reached := by
    cases observed : acquire directory lock appended with
    | ok value after => simpa only [finishFailedOpen, observed] using held
    | error cause failed => simp [finishFailedOpen, observed] at held
  obtain ⟨lockedAt, flock, initialized⟩ := openWithLock_reachedSuccess _ _ _ _ locked
  change recover directory lock () lockedAt = .ok table reached at initialized
  unfold recover at initialized
  cases initializedCache : initCache directory lockedAt with
  | error cause failed => simp [Bind.bind, EStateM.bind, initializedCache] at initialized
  | ok references prepared =>
    obtain ⟨cache, cached, active, pending⟩ := references
    have physicalCache : openSyncFilesWith (source.init.openDirectory directory.path) source.init.newRef source.init.newRef
        source.init.newRef
        (fun cached active pending =>
          (RawMarkedOpenInterpreter.makeCache directory cached active pending, cached, active, pending)) lockedAt =
      .ok (cache, cached, active, pending) prepared := initializedCache
    obtain ⟨root, actualDirectory, actualActive, actualPending, opened, setDirectory, setActive,
      openRoot, directoryRef, activeRef, pendingRef, exactCache⟩ :=
      source.init.reachedSuccess directory _ physicalCache
    have identities : cache = RawMarkedOpenInterpreter.makeCache directory actualDirectory actualActive actualPending ∧
        cached = actualDirectory ∧ active = actualActive ∧ pending = actualPending := by
      simpa only [Prod.mk.injEq] using exactCache
    obtain ⟨rfl, rfl, rfl, rfl⟩ := identities
    let worker := source.worker cached active pending directory lock
      (RawMarkedOpenInterpreter.makeCache directory cached active pending)
    have workerRan : worker prepared = .ok table reached := by
      simp only [Bind.bind, EStateM.bind, initializedCache] at initialized
      change (tryCatchThe IO.Error worker fun cause => do
        source.dispose (RawMarkedOpenInterpreter.makeCache directory cached active pending)
        throw cause) prepared = .ok table reached at initialized
      cases success : worker prepared with
      | ok value after =>
        simpa only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, success] using initialized
      | error error failed =>
        cases disposed : source.dispose
            (RawMarkedOpenInterpreter.makeCache directory cached active pending) failed <;>
          simp [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, success, EStateM.Backtrackable.restore,
            EStateM.dummyRestore, Bind.bind, EStateM.bind, disposed, throw, throwThe, MonadExceptOf.throw,
            EStateM.throw] at initialized
    exact ⟨directory, lock, lockMetadata, resolved, checked, probed, appended, lockedAt, root, cached,
      active, pending, opened, setDirectory, setActive, prepared, path, flat, probe, safe, lockOpen,
      flock, openRoot, directoryRef, activeRef, pendingRef, workerRan⟩

/-- Observations from the directory open and the individual reference
allocations. The readonly descriptor is added to the actual census. -/
structure OpenSyncCacheCallbacks.ProjectionEffects {heap image : Type}
    (calls : OpenSyncCacheCallbacks heap) (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (names : heap → FilePath → Option Nat) : Prop where
  openRoot : ∀ {before after root}, calls.openDirectory directory.path before = .ok root after →
    ∃ slot : DescriptorSlot,
      (view.descriptors before).references slot.description = [] ∧
      (view.descriptors after).slots = slot :: (view.descriptors before).slots ∧
      (∀ other ∈ (view.descriptors before).slots,
        (view.descriptors after).inode other.description = (view.descriptors before).inode other.description) ∧
      view.handle after root = (view.descriptors after, slot, 0) ∧
      names before directory.path = some ((view.descriptors after).inode slot.description) ∧
      view.files after = view.files before ∧
      ∀ file, (view.handle before file).2.1 ∈ (view.descriptors before).slots →
        (view.handle after file).2.1 = (view.handle before file).2.1
  refFrames : ∀ {α : Type} (value : α) {before after ref}, calls.newRef value before = .ok ref after →
    view.descriptors after = view.descriptors before ∧ view.files after = view.files before ∧
    ∀ file, view.handle after file = view.handle before file
  directoryRef : ∀ {root before after ref}, calls.newRef (some root) before = .ok ref after →
    view.directory after ref = some root
  activeRef : ∀ {before after ref}, calls.newRef (none : Option (FilePath × IO.FS.Handle)) before = .ok ref after →
    view.active after ref = none ∧ ∀ cached, view.directory after cached = view.directory before cached
  pendingRef : ∀ {before after ref}, calls.newRef ([] : List (FilePath × IO.FS.Handle)) before = .ok ref after →
    view.pending after ref = [] ∧ (∀ cached, view.directory after cached = view.directory before cached) ∧
      ∀ active, view.active after active = view.active before active

/-- The returned cells contain the actual cached directory and two empty
collections. Its live slot and the previously acquired lock both survive. -/
theorem OpenSyncCacheCallbacks.projectsHeldCache {heap image : Type}
    {calls : OpenSyncCacheCallbacks heap} {view : OpenCloseHeapView heap image} {directory : DiskDirectory}
    {names : heap → FilePath → Option Nat} (effects : calls.ProjectionEffects view directory names)
    {lock root : IO.FS.Handle} {owner : DescriptorSlot} {ownerInode : Nat}
    {cached : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {locked opened setDirectory setActive prepared : heap}
    (attachedLock : attachedReadSlot view lock owner ownerInode locked)
    (owned : (view.files locked).owners.Owns directory owner.description)
    (openRoot : calls.openDirectory directory.path locked = .ok root opened)
    (setRoot : calls.newRef (some root) opened = .ok cached setDirectory)
    (setEmptyActive : calls.newRef none setDirectory = .ok active setActive)
    (setEmptyPending : calls.newRef [] setActive = .ok pending prepared) :
    ∃ (captured : DescriptorInventory) (slot : DescriptorSlot),
      names locked directory.path = some (captured.inode slot.description) ∧
      view.descriptors prepared = captured ∧
      view.files prepared = view.files locked ∧
      view.handle prepared root = (captured, slot, 0) ∧
      view.directory prepared cached = some root ∧
      view.active prepared active = none ∧ view.pending prepared pending = [] ∧
      view.cacheAt prepared cached active pending = ⟨some (captured, slot, 0), none, []⟩ ∧
      attachedReadSlot view root slot (captured.inode slot.description) prepared ∧
      attachedReadSlot view lock owner ownerInode prepared ∧ slot.description ≠ owner.description ∧
      (view.files prepared).owners.Owns directory owner.description := by
  obtain ⟨slot, fresh, rootSlots, oldInodes, openedHandle, named, rootFiles, lockSlot⟩ := effects.openRoot openRoot
  obtain ⟨directoryCensus, directoryFiles, directoryHandles⟩ := effects.refFrames (some root) setRoot
  obtain ⟨activeCensus, activeFiles, activeHandles⟩ := effects.refFrames none setEmptyActive
  obtain ⟨pendingCensus, pendingFiles, pendingHandles⟩ := effects.refFrames [] setEmptyPending
  obtain ⟨activeEmpty, activeKeepsRoot⟩ := effects.activeRef setEmptyActive
  obtain ⟨pendingEmpty, pendingKeepsRoot, pendingKeepsActive⟩ := effects.pendingRef setEmptyPending
  have census := pendingCensus.trans (activeCensus.trans directoryCensus)
  have files := pendingFiles.trans (activeFiles.trans (directoryFiles.trans rootFiles))
  have keeps file := (pendingHandles file).trans ((activeHandles file).trans (directoryHandles file))
  have rootHandle := (keeps root).trans openedHandle
  have rootCell := (pendingKeepsRoot cached).trans ((activeKeepsRoot cached).trans (effects.directoryRef setRoot))
  have activeCell := (pendingKeepsActive active).trans activeEmpty
  have cache : view.cacheAt prepared cached active pending = ⟨some (view.descriptors opened, slot, 0), none, []⟩ := by
    simp only [OpenCloseHeapView.cacheAt, rootCell, rootHandle, activeCell, pendingEmpty, Option.map_some,
      Option.map_none, List.map_nil]
  have rootMember : slot ∈ (view.descriptors prepared).slots := by
    rw [census, rootSlots]
    exact List.mem_cons_self
  have ownerMember : owner ∈ (view.descriptors prepared).slots := by
    rw [census, rootSlots]
    exact List.mem_cons_of_mem _ attachedLock.2.1
  have lockLive : (view.handle locked lock).2.1 ∈ (view.descriptors locked).slots := by
    rw [attachedLock.1]
    exact attachedLock.2.1
  have ownerSlot := (congrArg (fun handle => handle.2.1) (keeps lock)).trans
    ((lockSlot lock lockLive).trans attachedLock.1)
  refine ⟨_, slot, named, census, files, rootHandle, rootCell, activeCell, pendingEmpty, cache,
    ⟨?_, rootMember, ?_⟩, ⟨ownerSlot, ownerMember, ?_⟩, ?_, ?_⟩
  · rw [rootHandle]
  · rw [census]
  · rw [census, oldInodes owner attachedLock.2.1]
    exact attachedLock.2.2
  · intro same
    have retained := (view.descriptors locked).mem_references.mpr ⟨owner, attachedLock.2.1, rfl, same.symm⟩
    rw [fresh] at retained
    exact List.not_mem_nil retained
  · rw [files]
    exact owned

section HeldCacheFrames

variable {heap : Type} {frame : heap → heap → Prop}

private theorem realPathFrame
    (realPath : FilePath → EStateM IO.Error heap FilePath)
    {input : FilePath} {before after : heap} {directory : DiskDirectory}
    (keeps : ∀ {path reached}, realPath input before = .ok path reached → frame before reached)
    (returned : DiskDirectory.openWith realPath input before = .ok directory after) :
    frame before after := by
  simp only [DiskDirectory.openWith, Bind.bind, EStateM.bind] at returned
  cases observed : realPath input before with
  | error cause reached => simp [observed] at returned
  | ok path reached =>
    by_cases absolute : path.toString.startsWith '/' = true
    · simp only [observed, absolute, ↓reduceDIte, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
      exact returned.2 ▸ keeps observed
    · simp [observed, absolute, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned

/-- Turning the metadata response into an option retains the lookup heap on every outcome. -/
theorem optionalMetadata_reachedState
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) {before : heap} :
    reachedState (optionalMetadataWith lookup before) = reachedState (lookup before) := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind]
  cases lookup before with
  | error => rfl
  | ok result =>
    cases result with
    | ok => rfl
    | error cause =>
      cases cause <;> try rfl
      rename_i _ code _
      by_cases missing : code = 2 <;>
        simp [missing, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reachedState]

/-- Rejecting a flat WAL is a pure decision after the filesystem lookup. -/
theorem rejectFlatWal_reachedState {directory : DiskDirectory} {entry : heap}
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) :
    reachedState (rejectFlatWalWith directory (optionalMetadataWith lookup) entry) = reachedState (lookup entry) := by
  rw [← optionalMetadata_reachedState lookup]
  simp only [rejectFlatWalWith, Bind.bind, EStateM.bind]
  cases optionalMetadataWith lookup entry with
  | error => rfl
  | ok metadata => cases metadata <;> rfl

theorem optionalMetadata_success_frames
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {before after : heap} {metadata : Option IO.FS.Metadata}
    (keeps : ∀ {result reached}, lookup before = .ok result reached → frame before reached)
    (returned : optionalMetadataWith lookup before = .ok metadata after) : frame before after := by
  have sameHeap := optionalMetadata_reachedState lookup (before := before)
  cases observed : lookup before with
  | error => simp [optionalMetadataWith, Bind.bind, EStateM.bind, observed] at returned
  | ok result reached =>
    simp only [returned, observed, reachedState] at sameHeap
    exact sameHeap.symm ▸ keeps observed

/-- Independent projections of the successful primitives that acquire a
lock and initialize its cache. Each frame uses the actual reached heap. -/
structure RawMarkedOpenInterpreter.HeldCacheFrames {stream : Type}
    (source : RawMarkedOpenInterpreter heap stream) (frame : heap → heap → Prop) : Prop where
  realPath : ∀ {input path before after}, source.calls.realPath input before = .ok path after → frame before after
  lookup : ∀ {path result before after}, source.calls.lookup path before = .ok result after → frame before after
  flock : ∀ {lock before after}, source.calls.flock lock before = .ok true after → frame before after
  openDirectory : ∀ {path root before after}, source.init.openDirectory path before = .ok root after → frame before after
  newRef : ∀ {α : Type} (value : α) {ref before after}, source.init.newRef value before = .ok ref after → frame before after

/-- The path and metadata observations can advance the heap while
preserving the caller's selected projection. -/
theorem RawMarkedOpenInterpreter.HeldCacheFrames.throughProbes {stream : Type}
    {source : RawMarkedOpenInterpreter heap stream}
    (effects : source.HeldCacheFrames frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    {input : FilePath} {directory : DiskDirectory} {metadata : Option IO.FS.Metadata}
    {entry resolved checked probed : heap}
    (path : DiskDirectory.openWith source.calls.realPath input entry = .ok directory resolved)
    (flat : optionalMetadataWith (source.calls.lookup (directory.file .wal)) resolved = .ok none checked)
    (lockProbe : optionalMetadataWith (source.calls.lookup (directory.file .lock)) checked = .ok metadata probed) :
    frame entry probed :=
  trans (realPathFrame source.calls.realPath (fun ran => effects.realPath ran) path)
    (trans (optionalMetadata_success_frames _ (fun ran => effects.lookup ran) flat)
      (optionalMetadata_success_frames _ (fun ran => effects.lookup ran) lockProbe))

/-- Readonly directory open and the reference allocations preserve the
same projection after the lock has been acquired. -/
theorem RawMarkedOpenInterpreter.HeldCacheFrames.throughAllocations {stream : Type}
    {source : RawMarkedOpenInterpreter heap stream}
    (effects : source.HeldCacheFrames frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    {directory : DiskDirectory} {root : IO.FS.Handle}
    {cached : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {locked opened setDirectory setActive prepared : heap}
    (openRoot : source.init.openDirectory directory.path locked = .ok root opened)
    (directoryRef : source.init.newRef (some root) opened = .ok cached setDirectory)
    (activeRef : source.init.newRef none setDirectory = .ok active setActive)
    (pendingRef : source.init.newRef [] setActive = .ok pending prepared) :
    frame locked prepared :=
  trans (effects.openDirectory openRoot) (trans (effects.newRef (some root) directoryRef)
    (trans (effects.newRef none activeRef) (effects.newRef [] pendingRef)))

end HeldCacheFrames

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
    tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, RawMarkedOpenInterpreter.cacheInitialization, openSyncFilesWith,
    seed.rawOpened, seed.directoryAllocated, seed.activeAllocated, seed.pendingAllocated, Pure.pure, EStateM.pure]

/-- A healthy return transfers the original lock and cache to the
table. The fixed worker is the only source of a successful result. -/
theorem RawOpenAdmissionReport.returnsHealthyMarkedInterpreter
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    {table : DiskTable} {reached : heap} :
    source.openTable input entry = .ok table reached ↔
      source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
        (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
        seed.afterPending = .ok table reached := by
  rw [raw.markedInterpreterStarts source seed]
  cases worker : source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
      (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef) seed.afterPending with
  | ok value atWorker =>
    simp only [finishFailedOpen, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker]
  | error cause atWorker =>
    simp only [finishFailedOpen, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, worker,
      EStateM.Backtrackable.restore, EStateM.dummyRestore, Bind.bind, EStateM.bind, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]
    cases source.dispose
        (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef) atWorker with
    | ok _ afterDisposal | error _ afterDisposal =>
      cases unlocked : source.calls.unlock raw.lock afterDisposal <;> simp [unlocked]

/-- The observed aligned, empty-suffix repair and reference allocations
determine the public success. Each callback starts at the preceding return
heap, and the keeper fsync uses the handle selected from the pending cell. -/
theorem RawOpenAdmissionReport.returnsAlignedMarkedInterpreter
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    {checked marked prepared issued authorized loaded consumed repaired afterPhase reached : heap}
    {metadata : IO.FS.Metadata} {plan : Plan} {opened : Reopened} {extent : Nat}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      seed.afterPending = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
      .ok (some metadata) marked)
    (prepare : source.markedPreparation seed.pendingRef directory marked = .ok (plan, opened, extent) prepared)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (aligned : extent = plan.keeperSize) (noLater : plan.newer = [])
    {keeper : IO.FS.Handle} {entries : List (FilePath × IO.FS.Handle)}
    (loadRoot : source.keeperCallbacks.getDirectory seed.directoryRef prepared = .ok (some seed.handle) issued)
    (syncRoot : source.keeperCallbacks.sync seed.handle issued = .ok () authorized)
    (loadKeeper : source.keeperCallbacks.getPending seed.pendingRef authorized = .ok entries loaded)
    (selected : entries.find? (fun item => item.1 == directory.file (.walSegment plan.keeper)) =
      some (directory.file (.walSegment plan.keeper), keeper))
    (consume : source.keeperCallbacks.setPending seed.pendingRef
      (entries.filter (fun item => item.1 != directory.file (.walSegment plan.keeper))) loaded = .ok () consumed)
    (syncKeeper : source.keeperCallbacks.sync keeper consumed = .ok () repaired)
    {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (phaseAllocated : source.allocatePhase (.ready opened.installed) repaired = .ok phase afterPhase)
    (tokenAllocated : source.allocateToken () afterPhase = .ok token reached) :
    let cache := RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef
    source.openTable input entry = .ok (RawMarkedOpenInterpreter.assemble directory raw.lock cache phase token) reached := by
  intro cache
  let calls := source.keeperCallbacks.withFileReads source.fileCalls
  let sync := calls.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have root := calls.syncsDirectory (dir := directory.path) (active := seed.activeRef) (pending := seed.pendingRef)
    loadRoot syncRoot
  have pending := calls.syncsSelectedPending (cached := seed.directoryRef) (active := seed.activeRef)
    (file_ne_directory directory (.walSegment plan.keeper)) loadKeeper selected consume syncKeeper
  have finished := finishBoundedMarkedOpen_alignedEmpty directory plan extent source.remove
    (source.stage.stage seed.pendingRef calls.modifyPending) sync source.rename valid size aligned noLater root pending
  apply (raw.returnsHealthyMarkedInterpreter source seed).2
  change source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock cache seed.afterPending = _
  have recovered : recoverHealthyMarkedWithRefs source.fileCalls source.directoryCalls source.keeperCallbacks
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.stage source.rename source.calls.lookup
      directory (source.bootstrap directory cache) seed.afterPending = .ok opened repaired := by
    change (recoverSegmentedWalWith _ _ (do
      let (selectedPlan, replay, physicalExtent) ← source.markedPreparation seed.pendingRef directory
      finishBoundedMarkedOpen directory selectedPlan physicalExtent source.remove
        (source.stage.stage seed.pendingRef calls.modifyPending) sync source.rename
      pure replay) _) seed.afterPending = _
    simp only [recoverSegmentedWalWith, Bind.bind, EStateM.bind, flat, marker, Option.isSome, ↓reduceIte,
      prepare, finished, Pure.pure, EStateM.pure]
  simp only [RawMarkedOpenInterpreter.worker, installReady, Bind.bind, EStateM.bind, recovered, phaseAllocated,
    tokenAllocated, Pure.pure, EStateM.pure]

/-- After the two marked guards, the literal worker hands the values and heap
returned by its reader to repair. Errors from preparation, repair and
installation are carried by separate binds and may have the same diagnostic. -/
theorem RawMarkedOpenInterpreter.worker_markedError_iff
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cache : DiskTable.OpenSyncFiles)
    {entry checked marked : heap} {metadata : IO.FS.Metadata}
    {cause : IO.Error} {failed : heap}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      entry = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
      .ok (some metadata) marked) :
    let keeper := source.keeperCallbacks.withFileReads source.fileCalls
    let prepare := source.markedPreparation pending directory
    let repair := fun plan extent => finishBoundedMarkedOpen directory plan extent source.remove
      (source.stage.stage pending keeper.modifyPending) (keeper.syncPaths directory.path cached active pending) source.rename
    let install := fun (opened : Reopened) => installReady opened.installed source.allocatePhase source.allocateToken
      fun phase token => pure (RawMarkedOpenInterpreter.assemble directory lock cache phase token)
    source.worker cached active pending directory lock cache entry = .error cause failed ↔
      prepare marked = .error cause failed ∨
      ∃ plan opened extent prepared, prepare marked = .ok (plan, opened, extent) prepared ∧
        (repair plan extent prepared = .error cause failed ∨
          ∃ repaired, repair plan extent prepared = .ok () repaired ∧ install opened repaired = .error cause failed) := by
  intro keeper prepare repair install
  have dispatch : recoverHealthyMarkedWithRefs source.fileCalls source.directoryCalls source.keeperCallbacks
      cached active pending source.remove source.stage source.rename source.calls.lookup directory
      (source.bootstrap directory cache) entry = (do
        let (plan, opened, extent) ← prepare
        repair plan extent
        pure opened) marked := by
    simp only [recoverHealthyMarkedWithRefs, recoverSegmentedWalWith, Bind.bind, EStateM.bind,
      flat, marker, Option.isSome, ↓reduceIte]
    rfl
  change ((recoverHealthyMarkedWithRefs _ _ _ _ _ _ _ _ _ _ _ _ >>= install) entry = _) ↔ _
  simp only [Bind.bind, EStateM.bind, dispatch]
  cases ready : prepare marked with
  | error why reached => simp
  | ok payload reached =>
    obtain ⟨plan, opened, extent⟩ := payload
    constructor
    · intro failedWorker
      refine .inr ⟨plan, opened, extent, reached, rfl, ?_⟩
      cases finished : repair plan extent reached with
      | error why ended =>
        exact .inl (by simpa only [finished, EStateM.Result.error.injEq] using failedWorker)
      | ok result ended =>
        cases result
        exact .inr ⟨ended, rfl, by simpa only [finished, Pure.pure, EStateM.pure] using failedWorker⟩
    · rintro (impossible | ⟨_, _, _, _, h, failedStep⟩)
      · cases impossible
      · cases h
        rcases failedStep with failedRepair | ⟨_, finished, failedInstall⟩
        · simp only [failedRepair]
        · simpa only [finished, Pure.pure, EStateM.pure] using failedInstall

/-- A successful held worker returns the recovered state through its own
phase and token allocations to the table it assembled. -/
theorem RawMarkedOpenInterpreter.worker_reachesMarkedInstallation
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    {table : DiskTable} {reached : heap}
    (workerReturn : source.worker cached active pending directory lock
      (RawMarkedOpenInterpreter.makeCache directory cached active pending) cacheReady = .ok table reached) :
    let cache := RawMarkedOpenInterpreter.makeCache directory cached active pending
    ∃ (opened : Reopened) (repaired : heap) (phase : IO.Ref (Phase Installed)) (afterPhase : heap) (token : IO.Ref Unit),
      recoverHealthyMarkedWithRefs source.fileCalls source.directoryCalls source.keeperCallbacks
        cached active pending source.remove source.stage source.rename source.calls.lookup
        directory (source.bootstrap directory cache) cacheReady = .ok opened repaired ∧
      source.allocatePhase (.ready opened.installed) repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token reached ∧
      table = RawMarkedOpenInterpreter.assemble directory lock cache phase token := by
  intro cache
  have worker := workerReturn
  let recover := recoverHealthyMarkedWithRefs source.fileCalls source.directoryCalls source.keeperCallbacks
    cached active pending source.remove source.stage source.rename source.calls.lookup
    directory (source.bootstrap directory cache)
  change ((do
    let opened ← recover
    installReady opened.installed source.allocatePhase source.allocateToken fun phase token =>
      pure (RawMarkedOpenInterpreter.assemble directory lock cache phase token)) cacheReady) = _ at worker
  simp only [installReady, Bind.bind, EStateM.bind] at worker
  cases prepared : recover cacheReady with
  | error cause repaired => simp [prepared] at worker
  | ok opened repaired =>
    simp only [prepared] at worker
    cases phaseReturn : source.allocatePhase (.ready opened.installed) repaired with
    | error cause afterPhase => simp [phaseReturn] at worker
    | ok phase afterPhase =>
      simp only [phaseReturn] at worker
      cases tokenReturn : source.allocateToken () afterPhase with
      | error cause heap => simp [tokenReturn] at worker
      | ok token afterToken =>
        simp only [tokenReturn, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at worker
        exact ⟨opened, repaired, phase, afterPhase, token, prepared, phaseReturn, worker.2 ▸ tokenReturn, worker.1.symm⟩

theorem optionalMetadata_absenceLookup
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) {before after : heap}
    (returned : optionalMetadataWith lookup before = .ok none after) :
    ∃ name message, lookup before = .ok (.error (.noFileOrDirectory name 2 message)) after := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind] at returned
  cases issued : lookup before with
  | error cause failed => simp [issued] at returned
  | ok outcome reached =>
    cases outcome with
    | ok metadata => simp [issued, Pure.pure, EStateM.pure] at returned
    | error cause =>
      cases cause <;> simp [issued, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      rename_i name code message
      by_cases missing : code = 2
      · subst code
        have same : reached = after := by simpa [Pure.pure, EStateM.pure] using returned
        exact ⟨name, message, same ▸ rfl⟩
      · simp [missing, EStateM.throw] at returned

private theorem flatGuard_absenceLookup (directory : DiskDirectory)
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)) {before after : heap}
    (returned : rejectFlatWalWith directory (optionalMetadataWith lookup) before = .ok () after) :
    ∃ name message, lookup before = .ok (.error (.noFileOrDirectory name 2 message)) after := by
  simp only [rejectFlatWalWith, Bind.bind, EStateM.bind] at returned
  cases tested : optionalMetadataWith lookup before with
  | error cause reached => simp [tested] at returned
  | ok metadata reached =>
    cases metadata with
    | none =>
      have same : reached = after := by simpa [tested, Pure.pure, EStateM.pure] using returned
      exact optionalMetadata_absenceLookup lookup (same ▸ tested)
    | some _ => simp [tested, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned

private theorem recoverSegmentedWal_successfulGuards (rejectFlat : EStateM IO.Error heap Unit)
    (marker : EStateM IO.Error heap (Option IO.FS.Metadata)) (marked bootstrap : EStateM IO.Error heap Reopened)
    {before after : heap} {opened : Reopened}
    (returned : recoverSegmentedWalWith rejectFlat marker marked bootstrap before = .ok opened after) :
    ∃ checked probed metadata, rejectFlat before = .ok () checked ∧ marker checked = .ok metadata probed := by
  simp only [recoverSegmentedWalWith, Bind.bind, EStateM.bind] at returned
  cases flat : rejectFlat before with
  | error cause failed => simp [flat] at returned
  | ok result checked =>
    cases result
    simp only [flat] at returned
    cases markerReturn : marker checked with
    | error cause failed => simp [markerReturn] at returned
    | ok metadata probed => exact ⟨checked, probed, metadata, rfl, markerReturn⟩

/-- A healthy return from the fixed worker executes both probes. If the
selected marker binding survives the flat-WAL probe, truthful no-follow
lookup rules out the markerless dispatch at that reached heap. -/
theorem RawMarkedOpenInterpreter.worker_reachesMarkedGuards
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    (names : heap → FilePath → Option Nat) {inode : Nat}
    (presentAtCache : names cacheReady (directory.file .walBoundary) = some inode)
    (flatKeepsMarker : ∀ {checked name message},
      source.calls.lookup (directory.file .wal) cacheReady =
        .ok (.error (.noFileOrDirectory name 2 message)) checked →
      names checked (directory.file .walBoundary) = names cacheReady (directory.file .walBoundary))
    (lookupMissing : ∀ {before after name message},
      source.calls.lookup (directory.file .walBoundary) before =
        .ok (.error (.noFileOrDirectory name 2 message)) after →
      names before (directory.file .walBoundary) = none)
    {table : DiskTable} {reached : heap}
    (workerReturn : source.worker cached active pending directory lock
      (RawMarkedOpenInterpreter.makeCache directory cached active pending) cacheReady = .ok table reached) :
    ∃ checked marked metadata,
      rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
        cacheReady = .ok () checked ∧
      optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
        .ok (some metadata) marked := by
  obtain ⟨_, _, _, _, _, recovered, _, _, _⟩ := source.worker_reachesMarkedInstallation
    directory lock cached active pending cacheReady workerReturn
  unfold recoverHealthyMarkedWithRefs at recovered
  obtain ⟨checked, marked, found, flat, probe⟩ := recoverSegmentedWal_successfulGuards _ _ _ _ recovered
  cases found with
  | some metadata => exact ⟨checked, marked, metadata, flat, probe⟩
  | none =>
    obtain ⟨_, _, marker⟩ := optionalMetadata_absenceLookup _ probe
    obtain ⟨_, _, absentFlat⟩ := flatGuard_absenceLookup directory _ flat
    have impossible : (none : Option Nat) = some inode :=
      (lookupMissing marker).symm.trans ((flatKeepsMarker absentFlat).trans presentAtCache)
    cases impossible

/-- The actual marked success fixes the checkpoint, marker and WAL
returns at adjoining heaps. Replay determines the plan passed to the
repair, and the resulting table uses the references allocated after
that same repair. -/
theorem RawMarkedOpenInterpreter.worker_reachesMarkedReadsAndRepair
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    {checked marked reached : heap} {metadata : IO.FS.Metadata} {table : DiskTable}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      cacheReady = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked = .ok (some metadata) marked)
    (workerReturn : source.worker cached active pending directory lock
      (RawMarkedOpenInterpreter.makeCache directory cached active pending) cacheReady = .ok table reached) :
    let cache := RawMarkedOpenInterpreter.makeCache directory cached active pending
    let keeper := source.keeperCallbacks.withFileReads source.fileCalls
    let readOptional := source.fileCalls.readOptional directory
    let readCheckpoint := readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
      source.fileCalls.runSize source.fileCalls.runPrefix
    let readWal := fun watermark length => readSelectedWithCachedExtents directory watermark length
      source.directoryCalls.run (MarkedWalExtentReports.inspect source.fileCalls) source.fileCalls.seal
      (source.fileCalls.readKeeperWithRelease
        (fun path handle => keeper.modifyPending pending (SyncHandleRouting.pushPending path handle)))
    let writeStage := source.stage.stage pending keeper.modifyPending
    let syncPaths := keeper.syncPaths directory.path cached active pending
    ∃ (selected : Option (PackedTable × UInt64)) (afterCheckpoint : heap) (markerBytes : ByteArray)
      (afterMarker : heap) (length : UInt64) (reads : WalSegmentMarkerReads) (extent : Nat)
      (prepared repaired : heap) (patched : ByteArray) (logical : PackedTable) (first : Nat) (bytes : ByteArray)
      (phase : IO.Ref (Phase Installed)) (afterPhase : heap) (token : IO.Ref Unit),
      readCheckpoint marked = .ok selected afterCheckpoint ∧
      readOptional (directory.file .walBoundary) afterCheckpoint = .ok (some markerBytes) afterMarker ∧
      WAL.Boundary.decode markerBytes = .ok length ∧
      readWal ((selected.getD (.empty, 0)).1.committed.toNat) length afterMarker = .ok (reads, extent) prepared ∧
      recoverMarkedWalSegments (selected.getD (.empty, 0)).1 length reads.files = .ok (patched, logical) ∧
      reads.files.getLast? = some (first, bytes) ∧
      finishBoundedMarkedOpen directory ⟨length.toNat / WAL.frameSize, first, reads.newer, bytes⟩ extent
        source.remove writeStage syncPaths source.rename prepared = .ok () repaired ∧
      source.allocatePhase (.ready (Reopened.installed ⟨logical, (selected.getD (.empty, 0)).2, length, first⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token reached ∧
      table = RawMarkedOpenInterpreter.assemble directory lock cache phase token := by
  intro cache keeper readOptional readCheckpoint readWal writeStage syncPaths
  obtain ⟨opened, repaired, phase, afterPhase, token, recovered, allocated, tokenAllocated, exactTable⟩ :=
    source.worker_reachesMarkedInstallation directory lock cached active pending cacheReady workerReturn
  obtain ⟨plan, extent, prepared, preparedReads, repairedWal⟩ :=
    reachedMarkedPreparation source.fileCalls source.directoryCalls source.keeperCallbacks
      cached active pending source.remove source.stage source.rename source.calls.lookup
      directory _ flat marker recovered
  obtain ⟨selected, afterCheckpoint, markerBytes, afterMarker, length, reads, patched, logical, first, bytes,
    checkpointReturned, markerReturned, decoded, walReturned, replayed, lastKeeper, exactPlan, exactOpened⟩ :=
    reachedMarkedReaders directory readCheckpoint readOptional readWal preparedReads
  exact ⟨selected, afterCheckpoint, markerBytes, afterMarker, length, reads, extent, prepared, repaired, patched,
    logical, first, bytes, phase, afterPhase, token, checkpointReturned, markerReturned, decoded, walReturned,
    replayed, lastKeeper, exactPlan ▸ repairedWal, exactOpened ▸ allocated, tokenAllocated, exactTable⟩

variable {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- The fixed error handler disposes the cache returned by initialization,
then unlocks and releases the acquired lock. Its diagnostic follows the
unlock result. Cache contents do not affect this control-flow proof. -/
theorem RawOpenAdmissionReport.returnsFailedMarkedInterpreter
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    {cause : IO.Error} {before afterDisposal afterUnlock reached : heap}
    (worker : source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
      (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      seed.afterPending = .error cause before)
    (disposed : source.dispose (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      before = .ok () afterDisposal)
    (unlockResult : Except IO.Error Unit)
    (unlocked : source.calls.unlock raw.lock afterDisposal = match unlockResult with
      | .ok () => .ok () afterUnlock
      | .error diagnostic => .error diagnostic afterUnlock)
    (released : source.release raw.lock afterUnlock = reached) :
    source.openTable input entry = .error (RawOpenCacheDisposal.diagnosticAfterUnlock cause unlockResult) reached := by
  rw [raw.markedInterpreterStarts source seed]
  cases unlockResult with
  | error diagnostic => simp [finishFailedOpen, worker, disposed, unlocked, released, tryCatchThe,
      MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.Backtrackable.restore, EStateM.dummyRestore, Bind.bind,
      EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, RawOpenCacheDisposal.diagnosticAfterUnlock]
  | ok value =>
    cases value
    simp [finishFailedOpen, worker, disposed, unlocked, released, tryCatchThe, MonadExceptOf.tryCatch,
      EStateM.tryCatch, EStateM.Backtrackable.restore, EStateM.dummyRestore, Bind.bind, EStateM.bind, throw,
      throwThe, MonadExceptOf.throw, EStateM.throw, RawOpenCacheDisposal.diagnosticAfterUnlock]

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
  exact raw.returnsFailedMarkedInterpreter source seed worker (sameDisposal.symm ▸ seen.disposed _ uses)
    seen.unlockResult seen.unlocked finalized.finalized

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

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}

/-- The cache constructor and held worker determine the same successful
return in the fixed interpreter. Compare workers only at the reached
admission heap, so other branches may use different callbacks. -/
theorem RawOpenAdmissionReport.returnsFixedAfterWorkerAgreement
    {admission : CensusOpenAdmissionReports input directory inventory retry}
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (cacheUses : let cache := makeCache seed.directoryRef seed.activeRef seed.pendingRef
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧ cache.AtDirectory directory.path)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable)
    (agrees : let fixed := RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef
      recover directory raw.lock fixed seed.afterPending =
        source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock fixed seed.afterPending)
    {table : DiskTable} {reached : heap}
    (returned : source.calls.runOpen input source.init makeCache recover entry = .ok table reached) :
    source.openTable input entry = .ok table reached := by
  let cache := makeCache seed.directoryRef seed.activeRef seed.pendingRef
  let fixed := RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef
  have fixedUses := RawMarkedOpenInterpreter.cacheReferences directory seed.directoryRef seed.activeRef seed.pendingRef
  have sameCache : cache = fixed := sameCacheAtReferences cacheUses.1 cacheUses.2 fixedUses.1 fixedUses.2
  have initialized : openSyncFilesWith (source.init.openDirectory directory.path)
      source.init.newRef source.init.newRef source.init.newRef makeCache raw.afterFlock =
      .ok cache seed.afterPending := by
    simp only [openSyncFilesWith, Bind.bind, EStateM.bind, seed.rawOpened, seed.directoryAllocated,
      seed.activeAllocated, seed.pendingAllocated, Pure.pure, EStateM.pure, cache]
  rw [raw.startsHeldWorker source.init seed initialized recover, sameCache] at returned
  apply (raw.returnsHealthyMarkedInterpreter source seed).2
  change recover directory raw.lock fixed seed.afterPending = _ at agrees
  cases ran : recover directory raw.lock fixed seed.afterPending with
  | ok value after =>
    rw [← agrees]
    simpa only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, ran] using returned
  | error diagnostic heap =>
    simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, ran, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
    cases unlocked : source.calls.unlock raw.lock heap <;> simp [unlocked] at returned

end

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
  let recover := fun resolved lock cache => do
    let opened ← recoverHealthyMarkedWithRefs raw.fileCalls raw.directoryCalls raw.callbacks raw.seed.directoryRef
      raw.seed.activeRef raw.seed.pendingRef source.remove source.stage source.rename source.calls.lookup resolved
      (source.bootstrap resolved cache)
    installReady opened.installed source.allocatePhase source.allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))
  refine raw.raw.returnsFixedAfterWorkerAgreement source raw.seed makeCache cacheUses recover ?_ returned
  intro fixed
  have sameTable : assemble directory raw.raw.lock fixed = RawMarkedOpenInterpreter.assemble directory raw.raw.lock fixed :=
    (constructs directory raw.raw.lock fixed).trans (RawMarkedOpenInterpreter.assembles directory raw.raw.lock fixed).symm
  unfold RawMarkedOpenInterpreter.worker
  simp only [recover, files, directoryReads, keeper, sameTable]

end

end Alvoki.Storage.DiskSession
