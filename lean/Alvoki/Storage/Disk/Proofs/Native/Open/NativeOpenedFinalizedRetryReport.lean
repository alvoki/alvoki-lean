import Alvoki.Storage.Disk.Proofs.Native.Open.NativeFinalizedRetryAlignedOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The old public close supplies the first actual caller heap. Each
reported rejection supplies the next heap, through the last lock drop.
The final reader starts there on the released writer's checkpoint and WAL. -/
structure NativeOpenedFinalizedRetryReport (current : NativeOpenedPosition opened)
    (inputs : List FilePath) (input : FilePath) (view : OpenCloseHeapView heap FileImage) where
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  directory : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences active pending directory
  closeCalls : OpenCloseCallbacks heap
  samePhase : view.phase = opened.contents
  sameGet : closeCalls.getPhase = opened.get
  sameSet : @closeCalls.set (Phase Installed) = opened.set
  close : NativeReadyClose current.current.ready.state
  closeEffects : OpenCloseObservation close.report view closeCalls opened.lock opened.phase
    active pending directory current.reached
  success : close.report.result = .ok ()
  files : NativeCloseFiles current.current.ready.state
  openCalls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  release : IO.FS.Handle → heap → heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  observe : ∀ after, current.closeOnOpenedCells closeCalls active pending directory = .ok () after →
    ∃ (errors : List (FilePath × IO.Error)) (last : heap)
      (plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
        current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint)
      (reader : NativeCloseAlignedReads files input (view.descriptors last) plan.layout selected),
      errors.map Prod.fst = inputs ∧
      RawFinalizedOpenAttempts view current.current.ready.state.session.directory openCalls init release after errors last ∧
      Nonempty (RawAlignedReopenEffects reader view openCalls init last phaseIdentity tokenIdentity
        allocatePhase allocateToken stream)
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {inputs : List FilePath} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage}

/-- The returned table and common execution have the same successful
close, exact diagnostic sequence and aligned final read. -/
structure NativeOpenedFinalizedRetryReport.Returned (seen : NativeOpenedFinalizedRetryReport current inputs input view)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle)
    (errors : List (FilePath × IO.Error)) : Prop where
  sourceClose : opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
    (seen.active.set none) (seen.pending.set []) (seen.directory.set none) (opened.phase.set .closed)
  witnessed :
    let state := current.current.ready.state
    ∃ (afterClose last : heap) (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint)
      (reader : NativeCloseAlignedReads seen.files input (view.descriptors last) plan.layout selected)
      (reopen : RawAlignedReopenEffects reader view seen.openCalls seen.init last seen.phaseIdentity seen.tokenIdentity
        seen.allocatePhase seen.allocateToken seen.stream)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      current.closeOnOpenedCells seen.closeCalls seen.active seen.pending seen.directory = .ok () afterClose ∧
      opened.contents afterClose opened.phase = some .closed ∧
      view.files afterClose = state.releasedFiles ∧ view.descriptors afterClose = seen.close.report.finished.descriptors ∧
      RawFinalizedOpenAttempts view state.session.directory seen.openCalls seen.init seen.release afterClose errors last ∧
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      reopen.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble makeCache =
        .ok handle.table start.reached ∧
      handle.lock = reopen.admission.raw.lock ∧
      handle.files.UsesCacheReferences reopen.admission.seed.activeRef reopen.admission.seed.pendingRef
        reopen.admission.seed.directoryRef ∧
      view.cacheAt start.reached reopen.admission.seed.directoryRef reopen.admission.seed.activeRef
        reopen.admission.seed.pendingRef = start.current.ready.state.cache
  paths : errors.map Prod.fst = inputs
  common : NativeExecutionStep current.current (.rejectedOpenSequenceRecovered inputs input (errors.map Prod.snd)) start.current
  contents : handle.contents = view.phase
  sameGet : handle.get = opened.get
  sameSet : handle.set = opened.set
  samePtrEq : handle.ptrEq = opened.ptrEq
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census

/-- Derive the next ready table directly from the exact successor heap
after the last caller-visible failed attempt. -/
theorem NativeOpenedFinalizedRetryReport.reaches (seen : NativeOpenedFinalizedRetryReport current inputs input view) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (errors : List (FilePath × IO.Error)), seen.Returned start errors := by
  let state := current.current.ready.state
  obtain ⟨valid, rows, prior⟩ := current.current.ready.readPrefix.refines
  obtain ⟨rawActive, rawPending, rawDirectory, refs, source⟩ := current.uses.close
  have active := refs.1.symm.trans seen.references.1
  have pending := refs.2.1.symm.trans seen.references.2.1
  have directory := refs.2.2.symm.trans seen.references.2.2
  subst rawActive rawPending rawDirectory
  have notClosed : state.closeState.phase ≠ .closed := by simp [state, NativeReadyState.closeState, valid.phase]
  have raw := seen.closeEffects.returns notClosed
  rw [OpenCloseObservation.Reached, seen.success] at raw
  obtain ⟨clears, ran, frame⟩ := raw
  have ranClose : current.closeOnOpenedCells seen.closeCalls seen.active seen.pending seen.directory =
      .ok () clears.afterPhase := by
    simpa only [NativeOpenedPosition.closeOnOpenedCells, seen.sameGet, seen.sameSet] using ran
  obtain ⟨closed, closedPhase, closedFiles, closedCensus, _⟩ := seen.close.closes valid seen.success
  have phase : opened.contents clears.afterPhase opened.phase = some .closed := by
    rw [← seen.samePhase, ← closedPhase]
    exact frame.1
  have files : view.files clears.afterPhase = state.releasedFiles := by
    have reached := frame.2.2.1
    rw [closedFiles] at reached
    exact reached
  have census := frame.2.2.2
  obtain ⟨errors, last, plan, selected, reader, paths, attempts, ⟨reopen⟩⟩ := seen.observe clears.afterPhase ranClose
  have reachedFiles := reopen.admission.raw.entryFiles
  have closeInodes := congrArg DescriptorInventory.inode (census.trans closedCensus)
  have reachedInodes : (view.descriptors last).inode = state.census.inode := by
    simpa only [DescriptorInventory.afterDrops] using attempts.preserves.1.trans closeInodes
  obtain ⟨next, reopened, readerRan, returned, owner, slot, cache⟩ :=
    current.current.ready.reopensAfterRejectedOpensAt (view.descriptors last, view.files last)
      reachedFiles reachedInodes seen.files plan selected reader
  have pendingReplay : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history :=
    rows.symm ▸ prior
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length :=
    rows.symm ▸ current.current.ready.readPrefix.readsBounded
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩ :=
    reopen.opens valid.retained pendingReplay bounded seen.remove seen.write seen.rename seen.bootstrap seen.assemble seen.constructs
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set :=
    seen.samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, position, table, lock, cacheFiles, _, _, contents, getEq, setEq, compared, _, heap,
    pins, nextFiles, nextCensus, nextCache⟩ :=
    installed.startsAtSameHistory rows next readerRan returned cache owner slot phaseEffects opened.ptrEq
  have common := NativeExecutionStep.recoverFinalizedOpenSequence current.current (input := input)
    seen.close closed files census attempts seen.files next reopened
  rw [paths, ← position] at common
  refine ⟨handle, start, errors, source, ?_, paths, common, contents, getEq, setEq, compared, pins,
    position.symm ▸ nextFiles, position.symm ▸ nextCensus⟩
  refine ⟨clears.afterPhase, last, plan, selected, reader, reopen, cacheOpen, makeCache, ranClose, phase, files,
    census, attempts, cacheAction, cacheSource, ?_, lock, cacheFiles.symm ▸ installed.cacheReferences, ?_⟩
  · simpa only [heap, table] using rawOpen
  · rw [position]
    exact nextCache

end Alvoki.Storage.DiskSession
