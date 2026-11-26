import Alvoki.Storage.Disk.NativeAlignedMarkedReady

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
      ∃ (finish : CapturedAlignedFinish opening.callbacks opening.reads vacant plan.selected)
        (seen : AlignedKeeperCacheReport finish view source.init raw.raw.afterFlock raw.seed
          (raw.callbacks.withFileReads raw.fileCalls) raw.beforeKeeper),
        (⟨opening.finish, raw.repaired, raw.keeper⟩ :
          Σ finish : CapturedKeeperFinish opening.callbacks opening.reads vacant plan.selected, Σ heap : heap,
            NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper source.remove
              source.stage source.rename finish heap) = ⟨.aligned finish, seen.reached, .aligned seen⟩ ∧
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
  obtain ⟨finish, seen, aligned, admitted, read, scan, remember, repair, directory, consume, ⟨links⟩, phase, token⟩ :=
    laws plan opening raw files listing keeperCalls
  have footprint : current.state.SelectedRetryDurability plan.layout.target (observe reached) :=
    plan.targetEq.symm ▸ durable
  have selectedManifest := (congrArg (fun target : Target => target.pair.manifest) plan.targetEq).trans manifest
  refine ⟨plan, opening, raw, returned.readyAfterAlignedRetry seen aligned observe visible current.readPrefix.refines.1
    footprint kept selectedManifest root lock admitted ⟨read, scan, remember⟩ repair
    ⟨keeper.1, keeper.2, directory, consume⟩ links phase token⟩

end Alvoki.Storage.DiskSession
