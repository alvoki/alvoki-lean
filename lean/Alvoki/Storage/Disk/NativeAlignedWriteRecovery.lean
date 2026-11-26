import Alvoki.Storage.Disk.NativeSourceLedger
import Alvoki.Storage.Disk.NativeCheckpointOpenChronology

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

section LiteralRead

/-- Effects of the actual admission, read and cache callbacks on a
protected footprint. The checked directory stream lists the held root. -/
structure RawOpenAdmissionReport.AlignedReadEffects {directory : DiskDirectory} {inventory : DescriptorInventory}
    {admission : CensusOpenAdmissionReports input directory inventory (view.files reached)}
    (raw : RawOpenAdmissionReport admission view source.calls reached)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop) where
  admissionFrame : raw.CacheFrames seed fun before after =>
    (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
      ⟨names after, fun inode => [visible after inode]⟩
  guard : ∀ path before,
    (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
      ⟨names (reachedState (source.calls.lookup path before)),
        fun inode => [visible (reachedState (source.calls.lookup path before)) inode]⟩
  opens : source.fileCalls.OpensReadSlot view names visible
  reads : source.fileCalls.ReadsAtCursor view visible
  fileFrames : source.fileCalls.FileFrames (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) scope
  statFrame : ∀ path before,
    (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
      ⟨names (reachedState (source.fileCalls.stat path before)),
        fun inode => [visible (reachedState (source.fileCalls.stat path before)) inode]⟩
  statObject : FilePath → heap → heap → Option Nat
  stat : ∀ {path before metadata after}, source.fileCalls.stat path before = .ok (.ok metadata) after →
    ∃ inode, statObject path before after = some inode ∧ names before path = some inode ∧
      metadata.byteSize.toNat = (visible before inode).size
  statMissing : ∀ {path before name message after},
    source.fileCalls.stat path before = .ok (.error (.noFileOrDirectory name 2 message)) after → names before path = none
  eof : ∀ file slot inode (request : USize) before after, attachedReadSlot view file slot inode before →
    0 < request.toNat → source.fileCalls.readChunk file request before = .ok .empty after →
    (visible before inode).size ≤ (view.handle before file).2.2
  listingFrames : source.directoryCalls.ScopeFrames directory fun before after =>
    (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
      ⟨names after, fun inode => [visible after inode]⟩
  streamObject : heap → stream → DeviceInode
  streamRoot : ∀ {before descriptor opened},
    source.directoryCalls.openDir directory.path before = .ok descriptor opened → streamObject opened descriptor = root
  complete : ∀ {before descriptor opened scanned closed entries},
    source.directoryCalls.openDir directory.path before = .ok descriptor opened →
    source.directoryCalls.readDir descriptor opened = ((entries, .ok ()), scanned) →
    source.directoryCalls.closeDir descriptor scanned = .ok () closed →
    (⟨entries, .ok (), .ok ()⟩ : OpenedDirectoryScan).visibleNames.Perm
      (namespaceView.names (streamObject opened descriptor))
  absent : ∀ {before entries after}, source.directoryCalls.run directory.path before = .ok entries after →
    MarkedWalExtentReports.TruthfulAbsence source.fileCalls directory namespaceView root (entries.toList.map (·.fileName)) after
  remember : ∀ {path file before after},
    (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef
      (pushPending path file) before = .ok () after →
    (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
      ⟨names after, fun inode => [visible after inode]⟩

/-- Match the actual checkpoint, marker and selected WAL read of one
open. The aligned finisher gets the same pending handle as the reader.
The phase installed after that repair contains the exact replay. -/
theorem NativeReadPosition.SelectedWritePlan.readsLiteralAlignedOpen {inventory : DescriptorInventory}
    {admission : CensusOpenAdmissionReports input current.state.session.directory inventory (view.files reached)}
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (raw : RawOpenAdmissionReport admission view source.calls reached)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    (effects : raw.AlignedReadEffects seed names visible namespaceView root scope)
    (protectedFiles : NativeReadyProtectedStorage current.state ⟨names reached, fun inode => [visible reached inode]⟩)
    (manifest : target.pair.manifest = current.state.writer.target.pair.manifest)
    (markerStored : ∀ marker, (view.files reached).image.directory.active.walBoundary = some marker →
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Stored
        ((dir).file .walBoundary) marker)
    (includes : ∀ path, current.state.selectedRetryPath path → scope path)
    (scopedWindow : ∀ start, plan.layout.first ≤ start → start ≤ plan.layout.range.through →
      scope ((dir).file (.walSegment start)))
    (child : ∀ start, plan.layout.first ≤ start → start ≤ plan.layout.range.through →
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names reached ((dir).file (.walSegment start)))
    (physical : plan.layout.VisibleWal dir (names reached) (visible reached))
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : ∀ start, plan.layout.range.through < start →
      namespaceView.child root (renderWalSegmentName start) = none)
    {checked marked returnedAt : heap} {metadata : IO.FS.Metadata} {table : DiskTable}
    (flat : rejectFlatWalWith dir
      (optionalMetadataWith (source.calls.lookup ((dir).file .wal))) seed.afterPending = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup ((dir).file .walBoundary)) checked = .ok (some metadata) marked)
    (returned : source.openTable input reached = .ok table returnedAt) :
    let keeperCalls := source.keeperCallbacks.withFileReads source.fileCalls
    let segment := plan.layout.keeper
    let path := (dir).file (.walSegment segment.first)
    let cache := RawMarkedOpenInterpreter.makeCache dir seed.directoryRef seed.activeRef seed.pendingRef
    let files := (plan.layout.sealed ++ [segment]).map fun item => (item.first, item.bytes)
    ∃ (count : UInt64) (markerBytes patched : ByteArray) (logical : PackedTable)
      (keeper : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat)
      (readHeap prepared repaired : heap) (phase : IO.Ref (Phase Installed)) (afterPhase : heap) (token : IO.Ref Unit),
      (view.files reached).image.directory.active.walBoundary = some markerBytes ∧
      WAL.Boundary.decode markerBytes = .ok count ∧
      count.toNat / WAL.frameSize = plan.layout.range.through ∧
      recoverMarkedWalSegments (current.state.writer.checkpoint.getD (.empty, 0)).1 count files = .ok (patched, logical) ∧
      names reached path = some inode ∧ attachedReadSlot view keeper slot inode readHeap ∧
      keeperCalls.modifyPending seed.pendingRef (pushPending path keeper) readHeap = .ok () prepared ∧
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Frames scope
        ⟨names prepared, fun inode => [visible prepared inode]⟩ ∧
      finishBoundedMarkedOpen dir ⟨plan.layout.range.through, segment.first, [], segment.bytes⟩ segment.bytes.size
        source.remove (source.stage.stage seed.pendingRef keeperCalls.modifyPending)
        (keeperCalls.syncPaths (dir).path seed.directoryRef seed.activeRef seed.pendingRef) source.rename prepared =
        .ok () repaired ∧
      source.allocatePhase (.ready (Reopened.installed
        ⟨logical, (current.state.writer.checkpoint.getD (.empty, 0)).2, count, segment.first⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token returnedAt ∧
      table = RawMarkedOpenInterpreter.assemble dir raw.lock cache phase token := by
  intro keeperCalls segment path cache files
  have selectedManifest := (congrArg (fun target : Target => target.pair.manifest) plan.targetEq).trans manifest
  have selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.writer.target.pair.manifest current.state.writer.checkpoint :=
    selectedManifest ▸ plan.selected
  obtain ⟨watermark, _, markerBytes, count, markerName, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting plan.layout.decoded
  have through : count.toNat / WAL.frameSize = plan.layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have checkpointCount := Option.some.inj (plan.selected.watermark.symm.trans watermark)
  have statExtent {path before metadata after inode}
      (call : source.fileCalls.stat path before = .ok (.ok metadata) after) (bound : names before path = some inode) :
      metadata.byteSize.toNat = (visible before inode).size := by
    obtain ⟨actual, _, boundAtStat, size⟩ := effects.stat call
    exact (Option.some.inj (boundAtStat.symm.trans bound)) ▸ size
  obtain ⟨afterCheckpoint, afterMarker, length, payloads, extent, prepared, repaired, patched, logical, first,
    bytes, phase, afterPhase, token, _, _, readMarker, wal, framed, replay, lastKeeper, finish, allocPhase, allocToken,
    assembled⟩ := raw.selectsCheckpointAndMarkerFromActualOpen source seed names visible effects.opens effects.reads
      selected protectedFiles (markerStored _ markerName) scope includes effects.admissionFrame effects.guard
      effects.fileFrames effects.statFrame statExtent effects.statMissing effects.eof flat marker returned
  have countEq : length = count := Except.ok.inj (readMarker.symm.trans decoded)
  subst length
  rw [checkpointCount] at wal
  have childAtRead (start : Nat) (lower : plan.layout.first ≤ start) (upper : start ≤ plan.layout.range.through) :
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names afterMarker ((dir).file (.walSegment start)) :=
    (child start lower upper).trans ((framed _ (scopedWindow start lower upper)).1).symm
  obtain ⟨payloadEq, extentEq, newer, file, slot, inode, _, _, readHeap, named, _, attached, route, preserved⟩ :=
    source.fileCalls.readsCanonicalWal source.directoryCalls dir view names visible plan.layout namespaceView root scope
      effects.opens effects.reads effects.fileFrames effects.listingFrames
      (fun path file => keeperCalls.modifyPending seed.pendingRef (pushPending path file))
      effects.remember effects.statObject effects.stat effects.statFrame framed
      (fun listed => source.directoryCalls.listedRootNames (dir).path namespaceView root effects.streamObject listed
        (fun _ _ ran => effects.streamRoot ran) (fun _ _ _ _ opened scan close => effects.complete opened scan close))
      effects.absent
      through plan.modeledWindow.2 physical scopedWindow childAtRead wal
  have exact : (view.files reached).image.keeper.active = some segment.bytes :=
    exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm)
  have alignedBytes : segment.bytes ++ plan.layout.tail = segment.bytes :=
    Option.some.inj (plan.layout.visible.symm.trans exact)
  have size : extent = segment.bytes.size := extentEq.trans (congrArg ByteArray.size alignedBytes)
  have suffix : payloads.newer = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro start present
    obtain ⟨later, child, bound⟩ := (newer start).mp present
    rw [noLater start later] at bound
    contradiction
  have last : payloads.files.getLast? = some (segment.first, segment.bytes) := by
    rw [payloadEq, List.map_append]
    simp [segment]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lastKeeper.symm.trans last))
  have remembered : keeperCalls.modifyPending seed.pendingRef (pushPending path file) readHeap = .ok () prepared := by
    rcases route with remembered | released
    · exact remembered.2
    · exact (Nat.lt_irrefl _ (size ▸ released.1)).elim
  refine ⟨count, markerBytes, patched, logical, file, slot, inode, readHeap, prepared, repaired, phase, afterPhase, token,
    markerName, decoded, through, ?_, named, attached, remembered, preserved, ?_, allocPhase, allocToken, assembled⟩
  · simpa only [payloadEq, files, segment] using replay
  · simpa only [size, suffix, through] using finish

end LiteralRead

end Alvoki.Storage.DiskSession
