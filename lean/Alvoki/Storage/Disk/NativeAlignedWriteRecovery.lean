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

private def alignedReadFrame (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (scope : FilePath → Prop) (keeps : heap → heap → Prop) (before after : heap) : Prop :=
  (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
    ⟨names after, fun inode => [visible after inode]⟩ ∧ keeps before after

/-- Effects of the actual admission, read and cache callbacks on a
protected footprint. The checked directory stream lists the held root. -/
structure RawOpenAdmissionReport.AlignedReadEffects {directory : DiskDirectory} {inventory : DescriptorInventory}
    {admission : CensusOpenAdmissionReports input directory inventory (view.files reached)}
    (raw : RawOpenAdmissionReport admission view source.calls reached)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    (keeps : heap → heap → Prop) where
  admissionFrame : raw.CacheFrames seed (alignedReadFrame names visible scope keeps)
  guard : ∀ path before,
    alignedReadFrame names visible scope keeps before (reachedState (source.calls.lookup path before))
  opens : source.fileCalls.OpensReadSlot view names visible
  reads : source.fileCalls.ReadsAtCursor view visible
  fileFrames : source.fileCalls.ScopeFrames (alignedReadFrame names visible scope keeps)
  statFrame : ∀ path before,
    alignedReadFrame names visible scope keeps before (reachedState (source.fileCalls.stat path before))
  statObject : FilePath → heap → heap → Option Nat
  stat : ∀ {path before metadata after}, source.fileCalls.stat path before = .ok (.ok metadata) after →
    ∃ inode, statObject path before after = some inode ∧ names before path = some inode ∧
      metadata.byteSize.toNat = (visible before inode).size
  statMissing : ∀ {path before name message after},
    source.fileCalls.stat path before = .ok (.error (.noFileOrDirectory name 2 message)) after → names before path = none
  eof : ∀ file slot inode (request : USize) before after, attachedReadSlot view file slot inode before →
    0 < request.toNat → source.fileCalls.readChunk file request before = .ok .empty after →
    (visible before inode).size ≤ (view.handle before file).2.2
  listingFrames : source.directoryCalls.ScopeFrames directory (alignedReadFrame names visible scope keeps)
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
      (pushPending path file) before = .ok () after → alignedReadFrame names visible scope keeps before after

/-- Match the actual checkpoint, marker and selected WAL read of one
open. The reader passes its exact handle to the pending callback.
The phase installed after that repair contains the exact replay. -/
theorem NativeReadPosition.SelectedWritePlan.readsLiteralAlignedOpen {inventory : DescriptorInventory}
    {admission : CensusOpenAdmissionReports input current.state.session.directory inventory (view.files reached)}
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (raw : RawOpenAdmissionReport admission view source.calls reached)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    {keeps : heap → heap → Prop} (keepsRefl : ∀ atHeap, keeps atHeap atHeap)
    (keepsTrans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (effects : raw.AlignedReadEffects seed names visible namespaceView root scope keeps)
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
      keeps reached prepared ∧
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
  let filesAt (atHeap : heap) : CheckpointSurvivingFiles := ⟨names atHeap, fun inode => [visible atHeap inode]⟩
  let visibleFrame before after := (filesAt before).Frames scope (filesAt after)
  have admissionVisible : raw.CacheFrames seed visibleFrame :=
    ⟨fun ran => (effects.admissionFrame.lockOpen ran).1, fun ran => (effects.admissionFrame.flock ran).1,
      fun ran => (effects.admissionFrame.openDirectory ran).1, fun ran => (effects.admissionFrame.directoryRef ran).1,
      fun ran => (effects.admissionFrame.activeRef ran).1, fun ran => (effects.admissionFrame.pendingRef ran).1⟩
  have readsVisible : source.fileCalls.ScopeFrames visibleFrame :=
    ⟨fun path before => (effects.fileFrames.openRead path before).1,
      fun file amount before => (effects.fileFrames.readChunk file amount before).1,
      fun file before => (effects.fileFrames.release file before).1⟩
  have listingVisible : source.directoryCalls.ScopeFrames dir visibleFrame :=
    ⟨fun ran => (effects.listingFrames.openDir ran).1, fun handle before => (effects.listingFrames.readDir handle before).1,
      fun ran => (effects.listingFrames.closeDir ran).1⟩
  obtain ⟨afterCheckpoint, afterMarker, length, payloads, extent, prepared, repaired, patched, logical, first,
    bytes, phase, afterPhase, token, checkpointRead, markerRead, readMarker, wal, framed, replay, lastKeeper, finish, allocPhase, allocToken,
    assembled⟩ := raw.selectsCheckpointAndMarkerFromActualOpen source seed names visible effects.opens effects.reads
      selected protectedFiles (markerStored _ markerName) scope includes admissionVisible (fun path before => (effects.guard path before).1)
      readsVisible (fun path before => (effects.statFrame path before).1) statExtent effects.statMissing effects.eof flat marker returned
  have countEq : length = count := Except.ok.inj (readMarker.symm.trans decoded)
  subst length
  rw [checkpointCount] at wal
  have childAtRead (start : Nat) (lower : plan.layout.first ≤ start) (upper : start ≤ plan.layout.range.through) :
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names afterMarker ((dir).file (.walSegment start)) :=
    (child start lower upper).trans ((framed _ (scopedWindow start lower upper)).1).symm
  obtain ⟨payloadEq, extentEq, newer, file, slot, inode, _, _, readHeap, named, _, attached, route, preserved⟩ :=
    source.fileCalls.readsCanonicalWal source.directoryCalls dir view names visible plan.layout namespaceView root scope
      effects.opens effects.reads readsVisible listingVisible
      (fun path file => keeperCalls.modifyPending seed.pendingRef (pushPending path file))
      (fun ran => (effects.remember ran).1) effects.statObject effects.stat
      (fun path before => (effects.statFrame path before).1) framed
      (fun listed => source.directoryCalls.listedRootNames (dir).path namespaceView root effects.streamObject listed
        (fun _ _ ran => effects.streamRoot ran) (fun _ _ _ _ opened scan close => effects.complete opened scan close))
      effects.absent
      through plan.modeledWindow.2 physical scopedWindow childAtRead wal
  let frame := alignedReadFrame names visible scope keeps
  have refl (atHeap : heap) : frame atHeap atHeap := ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, keepsRefl atHeap⟩
  have trans {before middle after : heap} (left : frame before middle) (right : frame middle after) : frame before after :=
    ⟨left.1.trans right.1, keepsTrans left.2 right.2⟩
  have throughAdmission := raw.framesThroughCache seed (frame := frame) trans effects.admissionFrame
  have throughGuards := markedGuards_keepFrame (frame := frame) dir source.calls.lookup trans effects.guard flat marker
  have throughCheckpoint := source.fileCalls.framesCheckpointSuccess dir refl trans effects.fileFrames effects.statFrame checkpointRead
  have throughMarker := source.fileCalls.readOptionalFrames effects.fileFrames refl trans effects.statFrame
    dir ((dir).file .walBoundary) afterCheckpoint
  rw [markerRead, reachedState] at throughMarker
  have throughWal := source.fileCalls.selectedWalKeepsFrame source.directoryCalls dir refl trans effects.fileFrames
    effects.listingFrames effects.statFrame
    (fun path file => keeperCalls.modifyPending seed.pendingRef (pushPending path file)) effects.remember wal
  have throughReader : keeps reached prepared :=
    (trans throughAdmission (trans throughGuards (trans throughCheckpoint (trans throughMarker throughWal)))).2
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
    markerName, decoded, through, ?_, named, attached, remembered, preserved, throughReader, ?_, allocPhase, allocToken, assembled⟩
  · simpa only [payloadEq, files, segment] using replay
  · simpa only [size, suffix, through] using finish

end LiteralRead

section LiteralRepair

/-- Interpret only the file-image projection of the reached callbacks.
Ownership and durable physical bytes have separate projections. -/
structure AlignedRepairImageEffects (view : OpenCloseHeapView heap FileImage)
    (calls : AlignedKeeperCacheCallbacks heap) (root keeper : IO.FS.Handle) where
  rootLoad : ∀ {cached before after}, calls.getDirectory cached before = .ok (some root) after →
    (view.files after).image = (view.files before).image
  rootSync : ∀ {before after}, calls.sync root before = .ok () after →
    (view.files after).image = (view.files before).image.syncDirectory
  pendingLoad : ∀ {pending before after entries}, calls.getPending pending before = .ok entries after →
    (view.files after).image = (view.files before).image
  pendingClear : ∀ {pending before after entries}, calls.setPending pending entries before = .ok () after →
    (view.files after).image = (view.files before).image
  keeperSync : ∀ {before after}, calls.sync keeper before = .ok () after →
    (view.files after).image = (view.files before).image.syncKeeper

/-- Interpret the exact aligned finisher at the heap reached by the
remembered WAL read. Its two real barriers supply the file image needed
by the retained writer, and expose the root and keeper receipts. -/
theorem NativeReadPosition.SelectedWritePlan.retainsLiteralAlignedRepair
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {readHeap prepared repaired : heap} {root keeper : IO.FS.Handle}
    (model : AlignedRepairImageEffects view calls root keeper)
    (cachedRoot : view.directory prepared cached = some root)
    (remembered : calls.modifyPending pending (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
      readHeap = .ok () prepared)
    (recordsKeeper : calls.modifyPending pending (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
      view.pending prepared pending = pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper
        (view.pending readHeap pending))
    (readsRoot : ∀ {result issued}, calls.getDirectory cached prepared = .ok result issued →
      result = view.directory prepared cached ∧ view.pending issued pending = view.pending prepared pending)
    (syncKeepsPending : ∀ {issued after}, calls.sync root issued = .ok () after →
      view.pending after pending = view.pending issued pending)
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (finished : finishBoundedMarkedOpen dir ⟨plan.layout.range.through, plan.layout.keeper.first, [], plan.layout.keeper.bytes⟩
      plan.layout.keeper.bytes.size remove write (calls.syncPaths (dir).path cached active pending) rename prepared =
        .ok () repaired)
    (readOnly : (view.files prepared).image = (view.files reached).image)
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    (kept : (view.files reached).image.kept = current.state.writer.files.kept)
    {owner : DescriptorSlot} (held : (view.files repaired).owners.Owns dir owner.description)
    {count : UInt64} {markerBytes patched : ByteArray} {logical : PackedTable}
    (marker : (view.files reached).image.directory.active.walBoundary = some markerBytes)
    (decoded : WAL.Boundary.decode markerBytes = .ok count)
    (replayed : recoverMarkedWalSegments (current.state.writer.checkpoint.getD (.empty, 0)).1 count
      ((plan.layout.sealed ++ [plan.layout.keeper]).map fun segment => (segment.first, segment.bytes)) =
        .ok (patched, logical)) :
    let installed := Reopened.installed ⟨logical, (current.state.writer.checkpoint.getD (.empty, 0)).2, count,
      plan.layout.keeper.first⟩
    let wal := current.state.writer.wal.appendSelectedView (view.files reached).image.directory.active plan.history
    let writer := SegmentedWriterState.ofReopen installed wal plan.history current.state.writer.published
      plan.layout.target current.state.writer.checkpoint (view.files repaired)
    writer.RetainedReady dir owner.description ∧
    ∃ (rootIssued afterDirectory : heap) (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getDirectory cached prepared = .ok (some root) rootIssued ∧
      calls.sync root rootIssued = .ok () afterDirectory ∧
      calls.getPending pending afterDirectory = .ok entries loaded ∧
      entries.find? (fun item => item.1 == (dir).file (.walSegment plan.layout.keeper.first)) =
        some ((dir).file (.walSegment plan.layout.keeper.first), keeper) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != (dir).file (.walSegment plan.layout.keeper.first)))
        loaded = .ok () consumed ∧
      calls.sync keeper consumed = .ok () repaired := by
  intro installed wal writer
  let repairPlan : Plan := ⟨plan.layout.range.through, plan.layout.keeper.first, [], plan.layout.keeper.bytes⟩
  have size : repairPlan.keeperBytes.size = repairPlan.keeperSize := plan.layout.target.trimmedSize
  have valid : repairPlan.valid = true := (Plan.valid_iff repairPlan).mpr
    ⟨plan.layout.target.firstCovered, Nat.le_of_eq size.symm, by simp [repairPlan]⟩
  obtain ⟨rootIssued, afterDirectory, entries, loaded, consumed, getRoot, syncRoot, getPending, found, clear, syncKeeper⟩ :=
    calls.alignedRepairSyncs view dir repairPlan plan.layout.keeper.bytes.size cached active pending remove write rename
      valid size size rfl cachedRoot remembered recordsKeeper readsRoot syncKeepsPending readsPending finished
  have directoryEffect : (view.files afterDirectory).image = (view.files reached).image.syncDirectory :=
    (model.rootSync syncRoot).trans (congrArg FileImage.syncDirectory ((model.rootLoad getRoot).trans readOnly))
  have keeperEffect : (view.files repaired).image = (view.files afterDirectory).image.syncKeeper :=
    (model.keeperSync syncKeeper).trans
      (congrArg FileImage.syncKeeper ((model.pendingClear clear).trans (model.pendingLoad getPending)))
  have tail : plan.layout.tail = ByteArray.empty := by
    have bytes : plan.layout.keeper.bytes ++ plan.layout.tail = plan.layout.keeper.bytes :=
      Option.some.inj (plan.layout.visible.symm.trans
        (exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm)))
    have counts := congrArg ByteArray.size bytes
    rw [ByteArray.size_append] at counts
    exact ByteArray.size_eq_zero_iff.mp (by omega)
  have ready := plan.layout.readyAfterAlignedEffects tail noLater directoryEffect keeperEffect
  have keptBySync : (view.files repaired).image.kept = (view.files reached).image.kept := by
    rw [keeperEffect, directoryEffect]
    rfl
  have keptByLayout : (view.files repaired).image.kept = (wal.checkpointReopenFiles wal.directory none).kept :=
    keptBySync.trans (kept.trans current.readPrefix.refines.1.retained.sealedFiles)
  have keeperEq : plan.layout.keeper.first = wal.active.first := congrArg WalSegment.first plan.keeper
  obtain ⟨retained, _, _, _⟩ := plan.layout.retainedFromActualReplay plan.selected plan.accepted plan.ordered marker decoded rfl
    replayed plan.walLayout plan.walValid current.readPrefix.refines.1.retained.spans rfl keeperEq ready keptByLayout held
  exact ⟨retained, rootIssued, afterDirectory, entries, loaded, consumed, getRoot, syncRoot, getPending, found, clear, syncKeeper⟩

end LiteralRepair

section LiteralInstall

variable {calls : AlignedKeeperCacheCallbacks heap} {readHeap prepared repaired : heap}
  {root keeper lock : IO.FS.Handle} {owner directorySlot keeperSlot : DescriptorSlot}
  {writer : SegmentedWriterState}
  {allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired}
  {syncFiles : DiskTable.OpenSyncFiles} {cache : OpenSyncCacheRefs syncFiles current.state.session.directory.path}
  {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}

local notation "readyState" => allocation.readyState writer dir owner directorySlot
  cache.directory cache.active cache.pending phaseIdentity tokenIdentity

/-- Transport the settled storage and client ledger from the actual
aligned repair through the two allocations of the literal returned
table. The retained writer is the replay at this repair's reached heap. -/
theorem NativeReadPosition.SelectedWritePlan.continuesLiteralAligned
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (request : WriteRequest) (cause : IO.Error)
    (constructor : DiskTable.OpenReferenceAssembly dir lock syncFiles assemble)
    (retained : writer.RetainedReady dir owner.description)
    (sameHistory : writer.history = plan.history)
    (selected : writer.target = target) (manifest : target.pair.manifest = current.state.writer.target.pair.manifest)
    (published : writer.published.durable = current.state.writer.published.durable)
    (kept : writer.files.kept = current.state.writer.files.kept)
    (ownsSlot : (view.handle repaired lock).2.1 = owner)
    (ownerLive : owner ∈ (view.descriptors repaired).slots)
    (directoryLive : directorySlot ∈ (view.descriptors repaired).slots)
    (directoryCached : ∃ captured, (view.cacheAt repaired cache.directory cache.active cache.pending).directory =
      some (captured, directorySlot, 0))
    (cachePhase : CacheAllocationFrame view cache.directory cache.active cache.pending repaired allocation.afterPhase)
    (cacheToken : CacheAllocationFrame view cache.directory cache.active cache.pending allocation.afterPhase allocation.afterToken)
    (rootInode : ∀ captured, (readyState).cache.directory = some (captured, directorySlot, 0) →
      captured.inode directorySlot.description = (readyState).census.inode directorySlot.description)
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (tokenEqual : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (returned : source.openTable input reached = .ok (assemble allocation.phase allocation.token) allocation.afterToken)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (physical : current.state.SelectedRetryDurability target (observe prepared))
    (rootBound : (observe prepared).files.names (dir).path = some ((readyState).census.inode directorySlot.description))
    (lockBound : (observe prepared).files.names ((dir).file .lock) = some ((readyState).census.inode owner.description))
    {keeperInode : Nat} (keeperBound : (observe prepared).files.names ((dir).file (.walSegment writer.wal.active.first)) =
      some keeperInode)
    (keeperBytes : visible prepared keeperInode = writer.wal.active.bytes)
    (apart : ∀ path, path = (dir).file .walBoundary ∨ (readyState).writeFramePath path →
      (observe prepared).files.names path ≠ some keeperInode)
    (physicalSyncs : AlignedRepairStorageEffects calls view readyState observe visible keeperInode)
    (handleEffects : AlignedRepairHandleEffects calls view ((dir).file (.walSegment writer.wal.active.first)) root keeper)
    (rootAtRead : attachedReadSlot view root directorySlot ((readyState).census.inode directorySlot.description) readHeap)
    (keeperAtRead : attachedReadSlot view keeper keeperSlot keeperInode readHeap)
    (remembered : calls.modifyPending cache.pending (pushPending ((dir).file (.walSegment writer.wal.active.first)) keeper)
      readHeap = .ok () prepared)
    {rootIssued afterDirectory loaded consumed : heap} {entries : List (FilePath × IO.FS.Handle)}
    (getRoot : calls.getDirectory cache.directory prepared = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () afterDirectory)
    (getPending : calls.getPending cache.pending afterDirectory = .ok entries loaded)
    (findKeeper : entries.find? (fun item => item.1 == (dir).file (.walSegment writer.wal.active.first)) =
      some ((dir).file (.walSegment writer.wal.active.first), keeper))
    (clear : calls.setPending cache.pending
      (entries.filter (fun item => item.1 != (dir).file (.walSegment writer.wal.active.first))) loaded = .ok () consumed)
    (syncKeeper : calls.sync keeper consumed = .ok () repaired)
    (phaseFrame : (observe repaired).Frames (readyState).crashPath (observe allocation.afterPhase))
    (tokenFrame : (observe allocation.afterPhase).Frames (readyState).crashPath (observe allocation.afterToken))
    (phaseKeeper : ∀ inode, (observe repaired).files.names ((dir).file (.walSegment writer.wal.active.first)) = some inode →
      visible allocation.afterPhase inode = visible repaired inode)
    (tokenKeeper : ∀ inode, (observe allocation.afterPhase).files.names ((dir).file (.walSegment writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = visible allocation.afterPhase inode) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (keptBatch : List WAL.Write),
      source.openTable input reached = .ok handle.table start.reached ∧
      start.current.history = plan.history ∧
      (⟨prior, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        [.uncertainWriteCrashRecovered request input cause batch keptBatch] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session ∧
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) := by
  have stateValid : (readyState).Valid := ⟨rfl, rfl, ownerLive, directoryLive, directoryCached, retained⟩
  obtain ⟨protectedFiles, marker, rootSettled⟩ := physical.forReopenedWriter current.readPrefix.refines.1 stateValid rfl
    selected manifest published kept rootBound lockBound
  obtain ⟨rootAttached, keeperAttached⟩ := handleEffects.issuedAttachments rootAtRead keeperAtRead remembered getRoot
    syncRoot getPending findKeeper clear
  obtain ⟨settled, live⟩ := physicalSyncs.readyAfterSyncs getRoot syncRoot getPending clear syncKeeper rootAttached
    keeperAttached protectedFiles marker rootSettled keeperBound keeperBytes apart
  have init : PendingClientReplay (log ++ [.uncertainBatch batch]) current.reads (readyState).writer.history :=
    sameHistory.symm ▸ plan.pending
  have bounded : ∀ read ∈ current.reads, read.BoundedBy (readyState).writer.history.length :=
    sameHistory.symm ▸ plan.bounded
  obtain ⟨handle, start, nextCache, opened, _, _, _, history, submissions, _, reads, _, writeEntry⟩ :=
    allocation.opensReadyWriter stateValid constructor cache returned phaseEffects tokenEqual init bounded observe visible settled live
      rfl ownsSlot rfl cachePhase cacheToken rootInode phaseFrame tokenFrame phaseKeeper tokenKeeper
  have selectedHistory := history.trans sameHistory
  obtain ⟨keptBatch, ledger⟩ := plan.ledgerAfterReopen start.current selectedHistory submissions reads request input cause
  exact ⟨handle, start, nextCache, keptBatch, opened, selectedHistory, ledger, start.current.ready.readPrefix.guardedReplay, writeEntry⟩

end LiteralInstall

end Alvoki.Storage.DiskSession
