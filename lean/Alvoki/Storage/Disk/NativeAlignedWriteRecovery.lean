import Alvoki.Storage.Disk.NativeSourceLedger

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair CheckpointPublication

variable {heap stream : Type} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {returns : List (FilePath × IO.Error)} {first reached : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {prior : List WAL.Write} {log : List DatabaseSubmissions} {batch : List WAL.Write} {target : Target}
  {current : NativeReadPosition prior log} {source : RawMarkedOpenInterpreter heap stream}
  {vacant : TryLockObserves (view.files reached).owners current.state.session.directory (.ok true)}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

local notation "dir" => current.state.session.directory

/-- Local effects scoped to the actual aligned branch of the selected
mark reader and repair. Each return is from the fixed interpreter. -/
def NativeReadPosition.AlignedRetryEffects
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop :=
  ∀ (plan : current.SelectedWritePlan batch target (view.files reached).image)
      (opening : MarkedReadyOpenObservations input dir (view.descriptors reached) (view.files reached) plan.layout
        current.state.writer.published vacant plan.selected)
      (raw : RawHealthyMarkedOpenEffects opening view source.calls source.init reached phaseIdentity tokenIdentity
        source.allocatePhase source.allocateToken stream source.remove source.stage source.rename),
      raw.fileCalls = source.fileCalls → raw.directoryCalls = source.directoryCalls → raw.callbacks = source.keeperCallbacks →
      let path := (dir).file (.walSegment plan.layout.keeper.first)
      let live (heap : heap) : CheckpointSurvivingFiles := ⟨(observe heap).files.names, fun inode => [visible heap inode]⟩
      let frame before after := MarkedOpenReadFrame dir current.state.selectedRetryPath path
        (observe before) (observe after) (visible before) (visible after)
      ∀ (finish : CapturedAlignedFinish opening.callbacks opening.reads vacant plan.selected)
        (seen : AlignedKeeperCacheReport finish view source.init raw.raw.afterFlock raw.seed
          (raw.callbacks.withFileReads raw.fileCalls) raw.beforeKeeper),
        (⟨opening.finish, raw.repaired, raw.keeper⟩ :
          Σ finish : CapturedKeeperFinish opening.callbacks opening.reads vacant plan.selected, Σ heap : heap,
            NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper source.remove
              source.stage source.rename finish heap) = ⟨.aligned finish, seen.reached, .aligned seen⟩ →
        (raw.raw.CacheFrames raw.seed fun before after =>
          (observe before).Frames current.state.selectedRetryPath (observe after) ∧
          (live before).Frames (· = path) (live after)) ∧
        raw.fileCalls.ScopeFrames frame ∧ raw.directoryCalls.ScopeFrames dir frame ∧
        (raw.callbacks.modifyPending raw.seed.pendingRef (pushPending path seen.keeper) seen.read =
          .ok () seen.remembered → frame seen.read seen.remembered) ∧
        (∀ state : NativeReadyState, state.session.directory = dir → seen.StorageEffects observe visible state) ∧
        (raw.callbacks.sync raw.seed.handle seen.remembered = .ok () seen.authorized →
          (live seen.remembered).Frames (· = path) (live seen.authorized)) ∧
        (raw.callbacks.setPending raw.seed.pendingRef [] seen.authorized = .ok () seen.consumed →
          (live seen.authorized).Frames (· = path) (live seen.consumed)) ∧
        Nonempty (RunOpenLinkCensus (path := path) (before := raw.listing.reached) raw.fileCalls.stat
          (observe raw.listing.reached).files.names opening.reads.wal.keeper.observesFile.object) ∧
        (∀ (state : NativeReadyState) ref heap,
          source.allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref heap →
          (observe raw.repaired).Frames state.crashPath (observe heap) ∧ visible heap = visible raw.repaired) ∧
        (∀ (state : NativeReadyState) before ref heap,
          source.allocateToken () before = .ok ref heap →
          (observe before).Frames state.crashPath (observe heap) ∧ visible heap = visible before)

/-- Reuse the plan, reader and raw successful return selected by the
retry proof. The durable footprint is at the last retry heap. The
remaining laws are local effects of the selected aligned open. -/
theorem NativeReadPosition.SelectedWriteRecovery.readyAlignedWriter
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (recovered : current.SelectedWriteRecovery (returns := returns) (input := input) (view := view)
      (batch := batch) (target := target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      source (fun heap => (observe heap).files.names) visible first vacant get set ptrEq)
    (durable : current.state.SelectedRetryDurability target (observe reached))
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    (laws : NativeReadPosition.AlignedRetryEffects (current := current) (batch := batch) (target := target) (input := input)
      (view := view) (reached := reached) (vacant := vacant) (source := source)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) observe visible) :
    ∃ (plan : current.SelectedWritePlan batch target (view.files reached).image)
      (opening : MarkedReadyOpenObservations input dir (view.descriptors reached) (view.files reached) plan.layout
        current.state.writer.published vacant plan.selected)
      (raw : RawHealthyMarkedOpenEffects opening view source.calls source.init reached phaseIdentity tokenIdentity
        source.allocatePhase source.allocateToken stream source.remove source.stage source.rename),
      raw.ReadyWriterReturn (log ++ [.uncertainBatch batch]) current.reads (fun _ => source.openTable input reached)
        get set observe visible := by
  obtain ⟨_, _, kept, manifest, plan, opening, raw, files, listing, keeperCalls, root, lock, _, _, keeper, _, _, returned⟩ :=
    recovered
  have exactBytes : plan.layout.keeper.bytes = target.trimmed := congrArg Target.trimmed plan.targetEq
  obtain ⟨finish, seen, aligned⟩ := raw.alignedOfExactKeeper (by simpa only [exactBytes] using exactKeeper) noLater
  obtain ⟨admitted, read, scan, remember, repair, directory, consume, ⟨links⟩, phase, token⟩ :=
    laws plan opening raw files listing keeperCalls finish seen aligned
  have footprint : current.state.SelectedRetryDurability plan.layout.target (observe reached) :=
    plan.targetEq.symm ▸ durable
  have selectedManifest := (congrArg (fun target : Target => target.pair.manifest) plan.targetEq).trans manifest
  refine ⟨plan, opening, raw, returned.readyAfterAlignedRetry seen aligned observe visible current.readPrefix.refines.1
    footprint kept selectedManifest root lock admitted ⟨read, scan, remember⟩ repair
    ⟨keeper.1, keeper.2, directory, consume⟩ links phase token⟩

/-- Continue the same failed-call prefix at its last returned heap.
An exact keeper and empty suffix select the aligned repair on that open.
The successful open's phase, token and cache are the next writer's. -/
theorem NativeReadPosition.opensReadyAfterAlignedRetries
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (request : WriteRequest) (cause : IO.Error) {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table request.rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {attempts : source.FailedCalls first returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun heap => ⟨(observe heap).files.names, fun inode => [visible heap inode]⟩)
      current.state.selectedRetryPath
      (fun heap => RawOpenRetryTrace.KeeperAt view dir target (fun heap => (observe heap).files.names) visible heap ∧
        current.state.SelectedRetryDurability target (observe heap)) attempts)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target (fun heap => (observe heap).files.names) visible first)
    (durable : current.state.SelectedRetryDurability target (observe first))
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    (healthy : current.ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch) (target := target)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source (fun heap => (observe heap).files.names) vacant)
    (phase : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (laws : NativeReadPosition.AlignedRetryEffects (current := current) (batch := batch) (target := target)
      (input := input) (view := view) (reached := reached) (vacant := vacant) (source := source)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) observe visible) :
    ∃ (plan : current.SelectedWritePlan batch target (view.files reached).image)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (cache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (retained : List WAL.Write),
      source.openTable input reached = .ok handle.table start.reached ∧
      start.current.history = plan.history ∧
      (⟨prior, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        [.uncertainWriteCrashRecovered request input cause batch retained] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session ∧
      start.WriteStorageEntry view cache (observe start.reached) (visible start.reached) := by
  obtain ⟨retained, recovered⟩ := current.opensAfterWriteRetries source prepared fits admitted
    (fun heap => (observe heap).files.names) visible effects initial ⟨initial.keeper, durable⟩ And.left
    vacant healthy phase ptrEq
  obtain ⟨plan, _, _, writer⟩ := recovered.readyAlignedWriter observe visible retained.2 exactKeeper noLater laws
  obtain ⟨handle, start, cache, retained, opened, selected, ledger, replay, physical⟩ :=
    plan.ledgerAtReadyWriter writer request cause
  exact ⟨plan, handle, start, cache, retained, opened, selected, ledger, replay, physical⟩

end Alvoki.Storage.DiskSession
