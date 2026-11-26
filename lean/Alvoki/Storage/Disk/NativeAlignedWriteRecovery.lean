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
  statLinks : ∀ {path issued statHeap metadata inode other},
    source.fileCalls.stat path issued = .ok (.ok metadata) statHeap → statObject path issued statHeap = some inode →
    (∃ first, path = directory.file (.walSegment first)) →
    scope path → scope other → (other = directory.path ∨ ∃ file, other = directory.file file) → other ≠ path →
    names issued path = some inode → names issued other = some inode → 2 ≤ metadata.numLinks.toNat
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
      (∀ other, scope other → (other = (dir).path ∨ ∃ file, other = (dir).file file) →
        names prepared other = some inode → other = path) ∧
      keeps reached prepared ∧ keeps seed.afterPending prepared ∧
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
    effects.fileFrames.map (fun framed => framed.1)
  have listingVisible : source.directoryCalls.ScopeFrames dir visibleFrame :=
    ⟨fun ran => (effects.listingFrames.openDir ran).1, fun ran => (effects.listingFrames.readDir ran).1,
      fun opened scanned closed => (effects.listingFrames.closeDir opened scanned closed).1⟩
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
  obtain ⟨payloadEq, extentEq, newer, file, slot, inode, _, _, readHeap, named, _, attached, route, preserved, privateAtReturn⟩ :=
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
  have fromCache := trans throughGuards (trans throughCheckpoint (trans throughMarker throughWal))
  have throughReader : keeps reached prepared := (trans throughAdmission fromCache).2
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
    markerName, decoded, through, ?_, named, attached, remembered, preserved, privateAtReturn (fun looked object => effects.statLinks looked object ⟨segment.first, rfl⟩), throughReader, fromCache.2, ?_, allocPhase, allocToken, assembled⟩
  · simpa only [payloadEq, files, segment] using replay
  · simpa only [size, suffix, through] using finish

end LiteralRead

section LiteralRepair

/-- Interpret the file image of the reached callbacks. An independent
frame can carry the held authority across the same effects. -/
structure AlignedRepairImageEffects (view : OpenCloseHeapView heap FileImage)
    (calls : AlignedKeeperCacheCallbacks heap) (root keeper : IO.FS.Handle)
    (keeps : heap → heap → Prop) where
  rootLoad : ∀ {cached before after}, calls.getDirectory cached before = .ok (some root) after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  rootSync : ∀ {before after}, calls.sync root before = .ok () after →
    (view.files after).image = (view.files before).image.syncDirectory ∧ keeps before after
  pendingLoad : ∀ {pending before after entries}, calls.getPending pending before = .ok entries after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  pendingClear : ∀ {pending before after entries}, calls.setPending pending entries before = .ok () after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  keeperSync : ∀ {before after}, calls.sync keeper before = .ok () after →
    (view.files after).image = (view.files before).image.syncKeeper ∧ keeps before after

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
    {keeps : heap → heap → Prop}
    (keepsTrans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (model : AlignedRepairImageEffects view calls root keeper keeps)
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
    {owner : DescriptorSlot} (held : (view.files prepared).owners.Owns dir owner.description)
    (keepsOwner : keeps prepared repaired → (view.files prepared).owners.Owns dir owner.description →
      (view.files repaired).owners.Owns dir owner.description)
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
    writer.RetainedReady dir owner.description ∧ keeps prepared repaired ∧
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
  obtain ⟨getRootImage, getRootFrame⟩ := model.rootLoad getRoot
  obtain ⟨syncRootImage, syncRootFrame⟩ := model.rootSync syncRoot
  obtain ⟨getPendingImage, getPendingFrame⟩ := model.pendingLoad getPending
  obtain ⟨clearImage, clearFrame⟩ := model.pendingClear clear
  obtain ⟨syncKeeperImage, syncKeeperFrame⟩ := model.keeperSync syncKeeper
  have framed := keepsTrans getRootFrame (keepsTrans syncRootFrame
    (keepsTrans getPendingFrame (keepsTrans clearFrame syncKeeperFrame)))
  have directoryEffect : (view.files afterDirectory).image = (view.files reached).image.syncDirectory :=
    syncRootImage.trans (congrArg FileImage.syncDirectory (getRootImage.trans readOnly))
  have keeperEffect : (view.files repaired).image = (view.files afterDirectory).image.syncKeeper :=
    syncKeeperImage.trans (congrArg FileImage.syncKeeper (clearImage.trans getPendingImage))
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
    replayed plan.walLayout plan.walValid current.readPrefix.refines.1.retained.spans rfl keeperEq ready keptByLayout (keepsOwner framed held)
  exact ⟨retained, framed, rootIssued, afterDirectory, entries, loaded, consumed, getRoot, syncRoot, getPending, found, clear, syncKeeper⟩

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
    (rootAtPrepared : attachedReadSlot view root directorySlot ((readyState).census.inode directorySlot.description) prepared)
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
  obtain ⟨rootAttached, keeperAttached⟩ := handleEffects.issuedAttachments rootAtPrepared keeperAtRead remembered getRoot
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

section LiteralContinuation

variable {inventory : DescriptorInventory}
  {admission : CensusOpenAdmissionReports input current.state.session.directory inventory (view.files reached)}
  {raw : RawOpenAdmissionReport admission view source.calls reached}

local notation "keeperCalls" => source.keeperCallbacks.withFileReads source.fileCalls

/-- The authority established by an observed admission. The root cache
stores its captured description and cursor; the two live slots refer to
that root and to the held lock. Other descriptors may change. -/
structure LiteralOpenAuthority (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (atHeap : heap) : Prop where
  directoryCell : view.directory atHeap seed.directoryRef = some seed.handle
  rootHandle : view.handle atHeap seed.handle = (admission.reached, admission.cached, 0)
  rootAttached : attachedReadSlot view seed.handle admission.cached
    (admission.reached.inode admission.cached.description) atHeap
  ownerAttached : attachedReadSlot view raw.lock admission.owner
    (admission.reached.inode admission.owner.description) atHeap
  owned : (view.files atHeap).owners.Owns dir admission.owner.description

/-- The admitted root and lock have the same live slots after the
actual cache initializer. Only preservation of the lock handle's slot
is needed at the four cache callbacks. -/
theorem RawOpenAdmissionReport.literalAuthorityAtCache
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (openKeepsLock : ∀ {before after handle}, source.init.openDirectory (dir).path before = .ok handle after →
      (view.handle after raw.lock).2.1 = (view.handle before raw.lock).2.1)
    (newRefKeepsLock : ∀ {α : Type} (value : α) {before after ref},
      source.init.newRef value before = .ok ref after →
      (view.handle after raw.lock).2.1 = (view.handle before raw.lock).2.1) :
    LiteralOpenAuthority seed seed.afterPending := by
  obtain ⟨_, _, _, _, _, _, _, _, directoryCell, _, _, _, files, census, _, ownerLive, rootLive, _⟩ := seed.installs
  have rootHandle := seed.sameHandle.trans seed.openedHandle
  have lockHandle := raw.sameLock.trans raw.appendHandle
  have lockSlot : (view.handle seed.afterPending raw.lock).2.1 = admission.owner :=
    (newRefKeepsLock [] seed.pendingAllocated).trans ((newRefKeepsLock none seed.activeAllocated).trans
      ((newRefKeepsLock (some seed.handle) seed.directoryAllocated).trans
        ((openKeepsLock seed.rawOpened).trans (congrArg (fun handle => handle.2.1) lockHandle))))
  refine ⟨directoryCell, rootHandle, ⟨?_, rootLive, ?_⟩, ⟨lockSlot, ownerLive, ?_⟩, ?_⟩
  · rw [rootHandle]
  · rw [census]
    rfl
  · rw [census]
    rfl
  · rw [files]
    exact admission.opened.held

/-- A read frames the immutable footprint, the logical image and any
authority already established at its entry. In particular, just before
the cache is created the authority implication can be vacuous. -/
def literalOpenReadFrame (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (observe : heap → CheckpointStorageObservation) (before after : heap) : Prop :=
  (observe before).Frames current.state.selectedRetryPath (observe after) ∧
    (view.files after).image = (view.files before).image ∧
    (LiteralOpenAuthority seed before → LiteralOpenAuthority seed after)

private theorem literalReadFrame_refl
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (observe : heap → CheckpointStorageObservation) (atHeap : heap) :
    literalOpenReadFrame seed observe atHeap atHeap :=
  ⟨.refl _ _, rfl, id⟩

private theorem literalReadFrame_trans
    {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
    {observe : heap → CheckpointStorageObservation} {before middle after : heap}
    (left : literalOpenReadFrame seed observe before middle) (right : literalOpenReadFrame seed observe middle after) :
    literalOpenReadFrame seed observe before after :=
  ⟨left.1.trans right.1, right.2.1.trans left.2.1, right.2.2 ∘ left.2.2⟩

private def managedPath (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ ∃ file, path = directory.file file

/-- Consume one literal aligned open from its exact checkpoint and WAL
bytes, through the two repair barriers, to the next write entry. The
primitive laws are keyed by their actual heaps and returned handles. -/
theorem NativeReadPosition.SelectedWritePlan.returnsLiteralAlignedWriter
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (request : WriteRequest) (cause : IO.Error)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (readEffects : raw.AlignedReadEffects seed (fun atHeap => (observe atHeap).files.names) visible admission.view
      admission.root (managedPath dir) (literalOpenReadFrame seed observe))
    (entry : RawOpenRetryTrace.SelectedEntry view current.state target
      (fun atHeap => (observe atHeap).files.names) visible reached)
    (child : ∀ start, plan.layout.first ≤ start → start ≤ plan.layout.range.through →
      (admission.view.child admission.root (renderWalSegmentName start)).map admission.view.modelObject =
        (observe reached).files.names ((dir).file (.walSegment start)))
    (physical : plan.layout.VisibleWal dir (observe reached).files.names (visible reached))
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (laterNames : ∀ start, plan.layout.range.through < start →
      (∃ object, admission.view.child admission.root (renderWalSegmentName start) = some object) →
      start ∈ (view.files reached).image.later.visible)
    (noLater : (view.files reached).image.later.visible = [])
    (durable : current.state.SelectedRetryDurability target (observe reached))
    (openKeepsLock : ∀ {before after handle}, source.init.openDirectory (dir).path before = .ok handle after →
      (view.handle after raw.lock).2.1 = (view.handle before raw.lock).2.1)
    (newRefKeepsLock : ∀ {α : Type} (value : α) {before after ref},
      source.init.newRef value before = .ok ref after →
      (view.handle after raw.lock).2.1 = (view.handle before raw.lock).2.1)
    (rootName : (observe reached).files.names (dir).path = some (admission.reached.inode admission.cached.description))
    (ownerName : (observe reached).files.names ((dir).file .lock) = some (admission.reached.inode admission.owner.description))
    (repairEffects : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
      (observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first)) = some inode →
      (keeperCalls).modifyPending seed.pendingRef (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
        readHeap = .ok () prepared →
      AlignedRepairImageEffects view keeperCalls seed.handle keeper
        (fun before after => LiteralOpenAuthority seed before → LiteralOpenAuthority seed after))
    (recordsKeeper : ∀ {path keeper before after}, (keeperCalls).modifyPending seed.pendingRef (pushPending path keeper)
      before = .ok () after → view.pending after seed.pendingRef = pushPending path keeper (view.pending before seed.pendingRef))
    (readsRoot : ∀ {before result issued}, (keeperCalls).getDirectory seed.directoryRef before = .ok result issued →
      result = view.directory before seed.directoryRef ∧ view.pending issued seed.pendingRef = view.pending before seed.pendingRef)
    (syncKeepsPending : ∀ {issued after}, (keeperCalls).sync seed.handle issued = .ok () after →
      view.pending after seed.pendingRef = view.pending issued seed.pendingRef)
    (readsPending : ∀ {before entries loaded}, (keeperCalls).getPending seed.pendingRef before = .ok entries loaded →
      entries = view.pending before seed.pendingRef)
    (syncStorage : ∀ (state : NativeReadyState), state.session.directory = dir → ∀ inode,
      AlignedRepairStorageEffects keeperCalls view state observe visible inode)
    (syncHandles : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
      (observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first)) = some inode →
      (keeperCalls).modifyPending seed.pendingRef (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
        readHeap = .ok () prepared →
      AlignedRepairHandleEffects keeperCalls view ((dir).file (.walSegment plan.layout.keeper.first)) seed.handle keeper)
    (allocatesPhase : ∀ {installed before ref after}, source.allocatePhase (.ready installed) before = .ok ref after →
      view.phase after ref = some (.ready installed) ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef before after ∧
      (observe before).Frames (managedPath dir) (observe after) ∧ visible after = visible before)
    (allocatesToken : ∀ {before ref after}, source.allocateToken () before = .ok ref after →
      (∀ phase, view.phase after phase = view.phase before phase) ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef before after ∧
      (observe before).Frames (managedPath dir) (observe after) ∧ visible after = visible before)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (tokenEqual : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {checked marked returnedAt : heap} {metadata : IO.FS.Metadata} {table : DiskTable}
    (flat : rejectFlatWalWith dir
      (optionalMetadataWith (source.calls.lookup ((dir).file .wal))) seed.afterPending = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup ((dir).file .walBoundary)) checked = .ok (some metadata) marked)
    (returned : source.openTable input reached = .ok table returnedAt) :
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
  have scope (path : FilePath) (selected : current.state.selectedRetryPath path) : managedPath dir path := by
    rcases selected with mark | immutable
    · exact .inr ⟨.walBoundary, mark⟩
    · exact NativeReadyState.crashPath_rootOrChild
        (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr immutable)))
  have markerLive (bytes : ByteArray) (selected : (view.files reached).image.directory.active.walBoundary = some bytes) :
      (CheckpointSurvivingFiles.mk (observe reached).files.names fun inode => [visible reached inode]).Stored
        ((dir).file .walBoundary) bytes := by
    have atTarget := (congrArg DirectoryPublication.Bindings.walBoundary entry.valid.selected).symm.trans selected
    obtain ⟨inode, named, exactBytes⟩ := Option.map_eq_some_iff.mp (entry.marker.trans atTarget)
    exact ⟨inode, named, congrArg (fun bytes => [bytes]) exactBytes⟩
  have later (start : Nat) (beyond : plan.layout.range.through < start) :
      admission.view.child admission.root (renderWalSegmentName start) = none := by
    cases found : admission.view.child admission.root (renderWalSegmentName start) with
    | none => rfl
    | some object =>
      have listed := laterNames start beyond ⟨object, found⟩
      rw [noLater] at listed
      exact (List.not_mem_nil listed).elim
  obtain ⟨count, markerBytes, patched, logical, keeper, slot, inode, readHeap, prepared, repaired, phase, afterPhase,
    token, markerName, decoded, _, replay, named, attached, remembered, liveFrame, privateKeeper, readFrame, cacheFrame, finish,
    phaseReturn, tokenReturn, tableEq⟩ :=
    plan.readsLiteralAlignedOpen raw seed (fun atHeap => (observe atHeap).files.names) visible admission.view admission.root
      (managedPath dir) (literalReadFrame_refl seed observe) literalReadFrame_trans readEffects entry.protectedFiles
      entry.manifest markerLive scope (fun first _ _ => .inr ⟨.walSegment first, rfl⟩) child physical exactKeeper later
      flat marker returned
  have authority := RawOpenAdmissionReport.literalAuthorityAtCache seed openKeepsLock newRefKeepsLock
  have preparedAuthority := cacheFrame.2.2 authority
  obtain ⟨retained, repairFrame, rootIssued, afterDirectory, entries, loaded, consumed,
    getRoot, syncRoot, getPending, findKeeper, clear, syncKeeper⟩ :=
    plan.retainsLiteralAlignedRepair keeperCalls seed.directoryRef seed.activeRef seed.pendingRef source.remove
      (source.stage.stage seed.pendingRef (keeperCalls).modifyPending) source.rename
      (keeps := fun before after => LiteralOpenAuthority seed before → LiteralOpenAuthority seed after)
      (fun first second => second ∘ first) (repairEffects attached named remembered) preparedAuthority.directoryCell remembered
      (recordsKeeper) readsRoot syncKeepsPending readsPending finish readFrame.2.1 exactKeeper noLater entry.kept
      preparedAuthority.owned (fun kept _ => (kept preparedAuthority).owned) markerName decoded replay
  have repairedAuthority := repairFrame preparedAuthority
  let installed := Reopened.installed ⟨logical, (current.state.writer.checkpoint.getD (.empty, 0)).2, count,
    plan.layout.keeper.first⟩
  let wal := current.state.writer.wal.appendSelectedView (view.files reached).image.directory.active plan.history
  let writer := SegmentedWriterState.ofReopen installed wal plan.history current.state.writer.published
    plan.layout.target current.state.writer.checkpoint (view.files repaired)
  have keeperEq : writer.wal.active = plan.layout.keeper := plan.keeper.symm
  have keeperPathEq : (dir).file (.walSegment writer.wal.active.first) =
      (dir).file (.walSegment plan.layout.keeper.first) := congrArg (fun item : WalSegment => (dir).file (.walSegment item.first)) keeperEq
  let files := RawMarkedOpenInterpreter.makeCache dir seed.directoryRef seed.activeRef seed.pendingRef
  obtain ⟨uses, atDir⟩ := RawMarkedOpenInterpreter.cacheReferences dir seed.directoryRef seed.activeRef seed.pendingRef
  let cache : OpenSyncCacheRefs files (dir).path := ⟨seed.directoryRef, seed.activeRef, seed.pendingRef, uses, atDir⟩
  obtain ⟨initialized, phaseCache, phaseStorage, phaseVisible⟩ := allocatesPhase phaseReturn
  obtain ⟨keepsPhase, tokenCache, tokenStorage, tokenVisible⟩ := allocatesToken tokenReturn
  let allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired :=
    ⟨phase, token, afterPhase, returnedAt, phaseReturn, initialized, tokenReturn, keepsPhase phase⟩
  let state := allocation.readyState writer dir admission.owner admission.cached cache.directory cache.active cache.pending
    phaseIdentity tokenIdentity
  have dirCached : state.cache.directory = some (admission.reached, admission.cached, 0) := by
    change (view.cacheAt repaired seed.directoryRef seed.activeRef seed.pendingRef).directory = _
    simp only [OpenCloseHeapView.cacheAt, repairedAuthority.directoryCell, repairedAuthority.rootHandle, Option.map_some]
  have rootInCensus := repairedAuthority.rootAttached.2.2
  have keeperScope : managedPath dir ((dir).file (.walSegment plan.layout.keeper.first)) := .inr ⟨_, rfl⟩
  obtain ⟨preservedName, preservedBytes⟩ := liveFrame _ keeperScope
  have keeperBound := preservedName.trans named
  have exactBytes : visible reached inode = plan.layout.keeper.bytes := by
    have contents := physical.keeper
    rw [named, Option.map_some] at contents
    apply Option.some.inj (contents.trans ?_)
    exact plan.layout.visible.symm.trans (exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm))
  have preparedBytes := (List.cons.inj (preservedBytes inode named)).1.trans exactBytes
  have protectedRoot : current.state.selectedRetryPath (dir).path := .inr (.inl rfl)
  have protectedLock : current.state.selectedRetryPath ((dir).file .lock) := .inr (.inr (.inl rfl))
  have atRoot := (readFrame.1.visible _ protectedRoot).1.trans (rootName.trans (congrArg some rootInCensus.symm))
  have atLock := (readFrame.1.visible _ protectedLock).1.trans
    (ownerName.trans (congrArg some repairedAuthority.ownerAttached.2.2.symm))
  have preparedDurability := durable.frame readFrame.1.visible
    (readFrame.1.weaken (fun _ same => same.symm ▸ protectedRoot))
  have valid : state.Valid := ⟨rfl, rfl, repairedAuthority.ownerAttached.2.1, repairedAuthority.rootAttached.2.1,
    ⟨_, dirCached⟩, retained⟩
  have noAlias (path : FilePath) (keep : path = (dir).file .walBoundary ∨ state.writeFramePath path) :
      (observe prepared).files.names path ≠ some inode := by
    have pathInDir : managedPath dir path :=
      NativeReadyState.crashPath_rootOrChild (state := state) ((NativeReadyState.crashPath_iff_write (state := state)).mpr
        (keep.elim Or.inl (fun immutable => .inr (.inr immutable))))
    intro aliases
    have same := privateKeeper path pathInDir pathInDir aliases
    apply NativeReadyState.protectedPathNeWalFromActive valid keep (Nat.le_of_eq (congrArg WalSegment.first keeperEq))
    exact same
  have keepsSeals : writer.files.kept = current.state.writer.files.kept :=
    retained.sealedFiles.trans current.readPrefix.refines.1.retained.sealedFiles.symm
  have exactReturn : source.openTable input reached =
      .ok (RawMarkedOpenInterpreter.assemble dir raw.lock files allocation.phase allocation.token) allocation.afterToken :=
    returned.trans (congrArg (fun value => EStateM.Result.ok value returnedAt) tableEq)
  have compatible (captured : DescriptorInventory) (seen : state.cache.directory = some (captured, admission.cached, 0)) :
      captured.inode admission.cached.description = state.census.inode admission.cached.description := by
    rw [dirCached] at seen
    obtain rfl := congrArg Prod.fst (Option.some.inj seen).symm
    exact rootInCensus.symm
  exact plan.continuesLiteralAligned (allocation := allocation) (cache := cache)
    (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
    request cause (RawMarkedOpenInterpreter.assembles dir raw.lock files) retained rfl plan.targetEq entry.manifest rfl
    keepsSeals repairedAuthority.ownerAttached.1 repairedAuthority.ownerAttached.2.1 repairedAuthority.rootAttached.2.1
    ⟨_, dirCached⟩ phaseCache tokenCache compatible phaseEffects tokenEqual exactReturn observe visible
    preparedDurability atRoot atLock (keeperInode := inode)
    (by simpa only [keeperPathEq] using keeperBound) (keeperEq.symm ▸ preparedBytes) noAlias
    (syncStorage state rfl inode) (by simpa only [keeperPathEq] using syncHandles attached named remembered)
    (rootInCensus.symm ▸ preparedAuthority.rootAttached) attached
    (by simpa only [keeperPathEq] using remembered) getRoot syncRoot getPending
    (by simpa only [keeperPathEq] using findKeeper) (by simpa only [keeperPathEq] using clear) syncKeeper
    (phaseStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
    (tokenStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
    (fun other _ => congrFun phaseVisible other) (fun other _ => congrFun tokenVisible other)

end LiteralContinuation

end Alvoki.Storage.DiskSession
