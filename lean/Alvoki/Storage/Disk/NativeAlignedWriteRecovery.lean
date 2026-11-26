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

section LiteralRead

private def alignedReadFrame (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (scope : FilePath → Prop) (keeps : heap → heap → Prop) (before after : heap) : Prop :=
  (CheckpointSurvivingFiles.mk (names before) fun inode => [visible before inode]).Frames scope
    ⟨names after, fun inode => [visible after inode]⟩ ∧ keeps before after

/-- Effects of the actual read and cache callbacks on a protected
footprint. The checked directory stream lists the held root. -/
structure RawMarkedOpenInterpreter.AlignedReadEffects (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    (keeps : heap → heap → Prop) where
  guard : ∀ path before,
    alignedReadFrame names visible scope keeps before (reachedState (source.calls.lookup path before))
  markerMissing : ∀ {before after name message},
    source.calls.lookup (directory.file .walBoundary) before = .ok (.error (.noFileOrDirectory name 2 message)) after →
    names before (directory.file .walBoundary) = none
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
    (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending pending
      (pushPending path file) before = .ok () after → alignedReadFrame names visible scope keeps before after

/-- The selected checkpoint and WAL bytes fix the replay throughout
the marked worker. The actual extent selects whether the keeper
is remembered or released. The directory scan fixes the suffix
handed to repair independently of that extent. -/
theorem NativeReadPosition.SelectedWritePlan.readsLiteralMarkedOpen
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (lock : IO.FS.Handle) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    {keeps : heap → heap → Prop} (keepsRefl : ∀ atHeap, keeps atHeap atHeap)
    (keepsTrans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (admissionFrame : alignedReadFrame names visible scope keeps reached cacheReady)
    (effects : source.AlignedReadEffects view dir pending names visible namespaceView root scope keeps)
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
    {returnedAt : heap} {table : DiskTable}
    (returned : source.worker cached active pending dir lock
      (RawMarkedOpenInterpreter.makeCache dir cached active pending) cacheReady = .ok table returnedAt) :
    let keeperCalls := source.keeperCallbacks.withFileReads source.fileCalls
    let segment := plan.layout.keeper
    let path := (dir).file (.walSegment segment.first)
    let cache := RawMarkedOpenInterpreter.makeCache dir cached active pending
    let files := (plan.layout.sealed ++ [segment]).map fun item => (item.first, item.bytes)
    ∃ (count : UInt64) (markerBytes patched : ByteArray) (logical : PackedTable)
      (keeper : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat)
      (readHeap prepared repaired : heap) (extent : Nat) (newer : List Nat)
      (phase : IO.Ref (Phase Installed)) (afterPhase : heap) (token : IO.Ref Unit),
      (view.files reached).image.directory.active.walBoundary = some markerBytes ∧
      WAL.Boundary.decode markerBytes = .ok count ∧
      count.toNat / WAL.frameSize = plan.layout.range.through ∧
      recoverMarkedWalSegments (current.state.writer.checkpoint.getD (.empty, 0)).1 count files = .ok (patched, logical) ∧
      names reached path = some inode ∧ attachedReadSlot view keeper slot inode readHeap ∧
      ((segment.bytes.size = extent ∧
        keeperCalls.modifyPending pending (pushPending path keeper) readHeap = .ok () prepared) ∨
       (segment.bytes.size < extent ∧ source.fileCalls.release keeper readHeap = .ok () prepared)) ∧
      extent = (segment.bytes ++ plan.layout.tail).size ∧
      (∀ start, start ∈ newer ↔ plan.layout.range.through < start ∧
        ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ∧
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Frames scope
        ⟨names prepared, fun inode => [visible prepared inode]⟩ ∧
      (∀ other, scope other → (other = (dir).path ∨ ∃ file, other = (dir).file file) →
        names prepared other = some inode → other = path) ∧
      keeps reached prepared ∧ keeps cacheReady prepared ∧
      finishBoundedMarkedOpen dir ⟨plan.layout.range.through, segment.first, newer, segment.bytes⟩ extent
        source.remove (source.stage.stage pending keeperCalls.modifyPending)
        (keeperCalls.syncPaths (dir).path cached active pending) source.rename prepared =
        .ok () repaired ∧
      source.allocatePhase (.ready (Reopened.installed
        ⟨logical, (current.state.writer.checkpoint.getD (.empty, 0)).2, count, segment.first⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token returnedAt ∧
      table = RawMarkedOpenInterpreter.assemble dir lock cache phase token := by
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
  have markerScoped : scope ((dir).file .walBoundary) := includes _ (.inl rfl)
  obtain ⟨markerInode, markerNamed, _⟩ := markerStored _ markerName
  have markerAtCache : names cacheReady ((dir).file .walBoundary) = some markerInode :=
    (admissionFrame.1 _ markerScoped).1.trans markerNamed
  have flatKeepsMarker {checked name message}
      (ran : source.calls.lookup ((dir).file .wal) cacheReady =
        .ok (.error (.noFileOrDirectory name 2 message)) checked) :
      names checked ((dir).file .walBoundary) = names cacheReady ((dir).file .walBoundary) := by
    simpa only [ran, reachedState] using ((effects.guard ((dir).file .wal) cacheReady).1 _ markerScoped).1
  obtain ⟨checked, marked, metadata, flat, marker⟩ :=
    source.worker_reachesMarkedGuards dir lock cached active pending cacheReady names markerAtCache flatKeepsMarker effects.markerMissing returned
  have readsVisible : source.fileCalls.ScopeFrames visibleFrame :=
    effects.fileFrames.map (fun framed => framed.1)
  have listingVisible : source.directoryCalls.ScopeFrames dir visibleFrame :=
    ⟨fun ran => (effects.listingFrames.openDir ran).1, fun ran => (effects.listingFrames.readDir ran).1,
      fun opened scanned closed => (effects.listingFrames.closeDir opened scanned closed).1⟩
  obtain ⟨afterCheckpoint, afterMarker, length, payloads, extent, prepared, repaired, patched, logical, first,
    bytes, phase, afterPhase, token, checkpointRead, markerRead, readMarker, wal, framed, replay, lastKeeper, finish, allocPhase, allocToken,
    assembled⟩ := source.worker_selectsCheckpointAndMarker lock cached active pending cacheReady
      names visible effects.opens effects.reads
      selected protectedFiles (markerStored _ markerName) scope includes admissionFrame.1 (fun path before => (effects.guard path before).1)
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
      (fun path file => keeperCalls.modifyPending pending (pushPending path file))
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
  have throughGuards := markedGuards_keepFrame (frame := frame) dir source.calls.lookup trans effects.guard flat marker
  have throughCheckpoint := source.fileCalls.framesCheckpointSuccess dir refl trans effects.fileFrames effects.statFrame checkpointRead
  have throughMarker := source.fileCalls.readOptionalFrames effects.fileFrames refl trans effects.statFrame
    dir ((dir).file .walBoundary) afterCheckpoint
  rw [markerRead, reachedState] at throughMarker
  have throughWal := source.fileCalls.selectedWalKeepsFrame source.directoryCalls dir refl trans effects.fileFrames
    effects.listingFrames effects.statFrame
    (fun path file => keeperCalls.modifyPending pending (pushPending path file)) effects.remember wal
  have fromCache := trans throughGuards (trans throughCheckpoint (trans throughMarker throughWal))
  have throughReader : keeps reached prepared := (trans admissionFrame fromCache).2
  have last : payloads.files.getLast? = some (segment.first, segment.bytes) := by
    rw [payloadEq, List.map_append]
    simp [segment]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lastKeeper.symm.trans last))
  refine ⟨count, markerBytes, patched, logical, file, slot, inode, readHeap, prepared, repaired, extent, payloads.newer,
    phase, afterPhase, token, markerName, decoded, through, ?_, named, attached, route, extentEq, newer, preserved,
    privateAtReturn (fun looked object => effects.statLinks looked object ⟨segment.first, rfl⟩), throughReader,
    fromCache.2, ?_, allocPhase, allocToken, assembled⟩
  · simpa only [payloadEq, files, segment] using replay
  · simpa only [through] using finish

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
  obtain ⟨rootIssued, afterDirectory, entries, loaded, consumed, getRoot, syncRoot, getPending, found, clear, syncKeeper⟩ :=
    calls.alignedRepairSyncs view dir repairPlan plan.layout.keeper.bytes.size cached active pending remove write rename
      size rfl cachedRoot remembered recordsKeeper readsRoot syncKeepsPending readsPending finished
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

local notation "keeperCalls" => source.keeperCallbacks.withFileReads source.fileCalls

/-- The resources obtained through the successful admission prefix. The
cached inventory belongs to the returned directory handle. -/
structure HeldOpenCache (heap : Type) where
  lock : IO.FS.Handle
  handle : IO.FS.Handle
  directoryRef : IO.Ref (Option IO.FS.Handle)
  activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))
  pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))
  owner : DescriptorSlot
  rootSlot : DescriptorSlot
  captured : DescriptorInventory
  ready : heap

/-- The cache and lock authority used by later reads. Temporary reads can
change the census while preserving the two live descriptions. -/
structure LiteralOpenAuthority (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (cache : HeldOpenCache heap) (atHeap : heap) : Prop where
  directoryCell : view.directory atHeap cache.directoryRef = some cache.handle
  rootHandle : view.handle atHeap cache.handle = (cache.captured, cache.rootSlot, 0)
  rootAttached : attachedReadSlot view cache.handle cache.rootSlot
    (cache.captured.inode cache.rootSlot.description) atHeap
  ownerAttached : attachedReadSlot view cache.lock cache.owner
    (cache.captured.inode cache.owner.description) atHeap
  separate : cache.rootSlot.description ≠ cache.owner.description
  owned : (view.files atHeap).owners.Owns directory cache.owner.description

private def managedPath (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ ∃ file, path = directory.file file

private def alignedAdmissionFrame (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) (before after : heap) : Prop :=
  alignedReadFrame (fun atHeap => (observe atHeap).files.names) visible (managedPath state.session.directory)
    (fun before after => (observe before).Frames state.selectedRetryPath (observe after) ∧
      (view.files after).image = (view.files before).image) before after

/-- Local observations of the primitives used to enter the held worker.
The frame does not refer to cache cells ahead of their allocation. -/
structure RawMarkedOpenInterpreter.AlignedAdmissionEffects (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState) (input : FilePath) (entry : heap)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop where
  resolves : ∀ {directory after}, DiskDirectory.openWith source.calls.realPath input entry = .ok directory after →
    directory = state.session.directory
  frames : source.HeldCacheFrames (alignedAdmissionFrame view state observe visible)
  lockMissing : ∀ {before after name message},
    source.calls.lookup (state.session.directory.file .lock) before =
      .ok (.error (.noFileOrDirectory name 2 message)) after →
    (observe before).files.names (state.session.directory.file .lock) = none
  lockOpen : ∀ {lock checked before after inode metadata},
    optionalMetadataWith (source.calls.lookup (state.session.directory.file .lock)) checked =
      .ok (some metadata) before →
    (metadata.type == .file && metadata.numLinks == 1) = true →
    (observe before).files.names (state.session.directory.file .lock) = some inode →
    source.calls.openAppend (state.session.directory.file .lock) before = .ok lock after →
    alignedAdmissionFrame view state observe visible before after ∧
      ∃ owner, (view.descriptors before).references owner.description = [] ∧
        attachedReadSlot view lock owner inode after
  flock : ∀ {lock owner inode before after}, source.calls.flock lock before = .ok true after →
    (observe before).files.names (state.session.directory.file .lock) = some inode →
    attachedReadSlot view lock owner inode before →
    attachedReadSlot view lock owner inode after ∧ (view.files after).owners.Owns state.session.directory owner.description
  cache : source.init.ProjectionEffects view state.session.directory (fun atHeap => (observe atHeap).files.names)

/-- Derive the read authority and cache cells at the heap handed to the
worker by the literal successful open. -/
theorem RawMarkedOpenInterpreter.reachesAlignedCache {state : NativeReadyState}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    (effects : source.AlignedAdmissionEffects view state input reached observe visible)
    (protectedFiles : NativeReadyProtectedStorage state (observe reached).files)
    {returnedAt : heap} {table : DiskTable}
    (returned : source.openTable input reached = .ok table returnedAt) :
    ∃ cache : HeldOpenCache heap,
      alignedAdmissionFrame view state observe visible reached cache.ready ∧
      LiteralOpenAuthority view state.session.directory cache cache.ready ∧
      (observe reached).files.names state.session.directory.path = some (cache.captured.inode cache.rootSlot.description) ∧
      (observe reached).files.names (state.session.directory.file .lock) = some (cache.captured.inode cache.owner.description) ∧
      view.active cache.ready cache.activeRef = none ∧ view.pending cache.ready cache.pendingRef = [] ∧
      source.worker cache.directoryRef cache.activeRef cache.pendingRef state.session.directory cache.lock
        (RawMarkedOpenInterpreter.makeCache state.session.directory cache.directoryRef cache.activeRef cache.pendingRef) cache.ready =
        .ok table returnedAt := by
  obtain ⟨directory, lock, lockMetadata, _, checked, probed, _, locked, root, cached, active, pending, _, _, _, prepared,
    path, flat, probe, safe, openLock, acquire, openRoot, directoryRef, activeRef, pendingRef, worker⟩ :=
    source.reachesHeldCache input returned
  obtain rfl := effects.resolves path
  have trans {before middle after} (left : alignedAdmissionFrame view state observe visible before middle)
      (right : alignedAdmissionFrame view state observe visible middle after) :
      alignedAdmissionFrame view state observe visible before after :=
    ⟨left.1.trans right.1, left.2.1.trans right.2.1, right.2.2.trans left.2.2⟩
  have rootScope : managedPath state.session.directory state.session.directory.path := .inl rfl
  have lockScope : managedPath state.session.directory (state.session.directory.file .lock) := .inr ⟨.lock, rfl⟩
  have probes := effects.frames.throughProbes trans path flat probe
  have lockAtProbe := (probes.1 _ lockScope).1.trans protectedFiles.lockBound
  have privateMetadata : ∃ metadata, lockMetadata = some metadata := by
    cases lockMetadata with
    | some metadata => exact ⟨metadata, rfl⟩
    | none =>
      obtain ⟨_, _, missing⟩ := optionalMetadata_absenceLookup _ probe
      have frame := effects.frames.lookup missing
      have falseName := ((frame.1 _ lockScope).1.trans (effects.lockMissing missing)).symm.trans lockAtProbe
      cases falseName
  obtain ⟨metadata, agrees⟩ := privateMetadata
  obtain ⟨appendFrame, owner, _, appendedLock⟩ :=
    effects.lockOpen (agrees ▸ probe) (safe metadata agrees) lockAtProbe openLock
  have lockAtAppend := (appendFrame.1 _ lockScope).1.trans lockAtProbe
  obtain ⟨heldLock, owned⟩ := effects.flock acquire lockAtAppend appendedLock
  have throughLock := trans probes (trans appendFrame (effects.frames.flock acquire))
  have throughCache := effects.frames.throughAllocations trans openRoot directoryRef activeRef pendingRef
  obtain ⟨captured, slot, namedRoot, census, _, handle, cell, emptyActive, emptyPending, _, rootLive, lockLive, separate, held⟩ :=
    OpenSyncCacheCallbacks.projectsHeldCache effects.cache heldLock owned openRoot directoryRef activeRef pendingRef
  have ownerInode := census ▸ lockLive.2.2
  have rootAtEntry := (throughLock.1 _ rootScope).1.symm.trans namedRoot
  have lockAtEntry := protectedFiles.lockBound.trans (congrArg some ownerInode.symm)
  exact ⟨⟨lock, root, cached, active, pending, owner, slot, captured, prepared⟩,
    trans throughLock throughCache, ⟨cell, handle, rootLive, ownerInode.symm ▸ lockLive, separate, held⟩,
    rootAtEntry, lockAtEntry, emptyActive, emptyPending, worker⟩

/-- Reads preserve the immutable footprint, the logical image and the
authority that was established when the cache was allocated. -/
def literalOpenReadFrame (cache : HeldOpenCache heap)
    (observe : heap → CheckpointStorageObservation) (before after : heap) : Prop :=
  (observe before).Frames current.state.selectedRetryPath (observe after) ∧
    (view.files after).image = (view.files before).image ∧
    (LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)

private theorem literalReadFrame_refl
    (cache : HeldOpenCache heap)
    (observe : heap → CheckpointStorageObservation) (atHeap : heap) :
    literalOpenReadFrame (current := current) (view := view) cache observe atHeap atHeap :=
  ⟨.refl _ _, rfl, id⟩

private theorem literalReadFrame_trans
    {cache : HeldOpenCache heap} {observe : heap → CheckpointStorageObservation} {before middle after : heap}
    (left : literalOpenReadFrame (current := current) (view := view) cache observe before middle)
    (right : literalOpenReadFrame (current := current) (view := view) cache observe middle after) :
    literalOpenReadFrame (current := current) (view := view) cache observe before after :=
  ⟨left.1.trans right.1, right.2.1.trans left.2.1, right.2.2 ∘ left.2.2⟩

variable (source) in
/-- The local callback laws shared by literal aligned-open consumers.
They describe metadata, scoped handle effects, cache accesses, syncs,
and reference allocations. The caller supplies the actual open result
and the selected recovery entry separately. -/
structure RawMarkedOpenInterpreter.LiteralAlignedEffects
    (cache : HeldOpenCache heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) where
  readEffects : source.AlignedReadEffects view dir cache.pendingRef (fun atHeap => (observe atHeap).files.names)
    visible namespaceView root (managedPath dir) (literalOpenReadFrame (current := current) (view := view) cache observe)
  child : ∀ start, plan.layout.first ≤ start → start ≤ plan.layout.range.through →
    (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
      (observe reached).files.names ((dir).file (.walSegment start))
  laterNames : ∀ start, plan.layout.range.through < start →
    (∃ object, namespaceView.child root (renderWalSegmentName start) = some object) →
    start ∈ (view.files reached).image.later.visible
  repairEffects : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
    (observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first)) = some inode →
    (keeperCalls).modifyPending cache.pendingRef (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
    AlignedRepairImageEffects view keeperCalls cache.handle keeper
      (fun before after => LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)
  recordsKeeper : ∀ {path keeper before after}, (keeperCalls).modifyPending cache.pendingRef (pushPending path keeper)
    before = .ok () after → view.pending after cache.pendingRef = pushPending path keeper (view.pending before cache.pendingRef)
  readsRoot : ∀ {before result issued}, (keeperCalls).getDirectory cache.directoryRef before = .ok result issued →
    result = view.directory before cache.directoryRef ∧ view.pending issued cache.pendingRef = view.pending before cache.pendingRef
  syncKeepsPending : ∀ {issued after}, (keeperCalls).sync cache.handle issued = .ok () after →
    view.pending after cache.pendingRef = view.pending issued cache.pendingRef
  readsPending : ∀ {before entries loaded}, (keeperCalls).getPending cache.pendingRef before = .ok entries loaded →
    entries = view.pending before cache.pendingRef
  syncStorage : ∀ (state : NativeReadyState), state.session.directory = dir → ∀ inode,
    AlignedRepairStorageEffects keeperCalls view state observe visible inode
  syncHandles : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
    (observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first)) = some inode →
    (keeperCalls).modifyPending cache.pendingRef (pushPending ((dir).file (.walSegment plan.layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
    AlignedRepairHandleEffects keeperCalls view ((dir).file (.walSegment plan.layout.keeper.first)) cache.handle keeper
  allocatesPhase : ∀ {installed before ref after}, source.allocatePhase (.ready installed) before = .ok ref after →
    view.phase after ref = some (.ready installed) ∧
    CacheAllocationFrame view cache.directoryRef cache.activeRef cache.pendingRef before after ∧
    (observe before).Frames (managedPath dir) (observe after) ∧ visible after = visible before
  allocatesToken : ∀ {before ref after}, source.allocateToken () before = .ok ref after →
    (∀ phase, view.phase after phase = view.phase before phase) ∧
    CacheAllocationFrame view cache.directoryRef cache.activeRef cache.pendingRef before after ∧
    (observe before).Frames (managedPath dir) (observe after) ∧ visible after = visible before

/-- Consume one literal aligned open from its exact checkpoint and WAL
bytes, through the two repair barriers, to the next write entry. The
primitive laws are keyed by their actual heaps and returned handles. -/
theorem NativeReadPosition.SelectedWritePlan.returnsLiteralAlignedWriter
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (cache : HeldOpenCache heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (request : WriteRequest) (cause : IO.Error)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (effects : source.LiteralAlignedEffects cache namespaceView root plan observe visible)
    (admissionFrame : alignedAdmissionFrame view current.state observe visible reached cache.ready)
    (authority : LiteralOpenAuthority view dir cache cache.ready)
    (rootNamed : (observe reached).files.names (dir).path = some (cache.captured.inode cache.rootSlot.description))
    (lockNamed : (observe reached).files.names ((dir).file .lock) = some (cache.captured.inode cache.owner.description))
    (entry : RawOpenRetryTrace.SelectedEntry view current.state target
      (fun atHeap => (observe atHeap).files.names) visible reached)
    (physical : plan.layout.VisibleWal dir (observe reached).files.names (visible reached))
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    (durable : current.state.SelectedRetryDurability target (observe reached))
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (tokenEqual : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {returnedAt : heap} {table : DiskTable}
    (returned : source.openTable input reached = .ok table returnedAt)
    (workerReturn : source.worker cache.directoryRef cache.activeRef cache.pendingRef dir cache.lock
      (RawMarkedOpenInterpreter.makeCache dir cache.directoryRef cache.activeRef cache.pendingRef) cache.ready =
      .ok table returnedAt) :
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
  have untilHeld : alignedReadFrame (fun atHeap => (observe atHeap).files.names) visible (managedPath dir)
      (literalOpenReadFrame (current := current) (view := view) cache observe) reached cache.ready :=
    ⟨admissionFrame.1, admissionFrame.2.1, admissionFrame.2.2, fun _ => authority⟩
  obtain ⟨count, markerBytes, patched, logical, keeper, slot, inode, readHeap, prepared, repaired, extent, newer,
    phase, afterPhase, token, markerName, decoded, _, replay, named, attached, route, extentEq, laterNames, liveFrame,
    privateKeeper, readFrame, cacheFrame, rawFinish, phaseReturn, tokenReturn, tableEq⟩ :=
    plan.readsLiteralMarkedOpen cache.lock cache.directoryRef cache.activeRef cache.pendingRef cache.ready
      (fun atHeap => (observe atHeap).files.names) visible namespaceView root
      (managedPath dir) (literalReadFrame_refl cache observe) literalReadFrame_trans untilHeld effects.readEffects entry.protectedFiles
      entry.manifest markerLive scope (fun first _ _ => .inr ⟨.walSegment first, rfl⟩) effects.child physical workerReturn
  have exactImage : (view.files reached).image.keeper.active = some plan.layout.keeper.bytes :=
    exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm)
  have alignedBytes : plan.layout.keeper.bytes ++ plan.layout.tail = plan.layout.keeper.bytes :=
    Option.some.inj (plan.layout.visible.symm.trans exactImage)
  have size : extent = plan.layout.keeper.bytes.size := extentEq.trans (congrArg ByteArray.size alignedBytes)
  have suffix : newer = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro start present
    obtain ⟨later, listed⟩ := (laterNames start).mp present
    have visibleLater := effects.laterNames start later listed
    rw [noLater] at visibleLater
    exact List.not_mem_nil visibleLater
  have remembered := route.resolve_right (fun released => Nat.lt_irrefl _ (size ▸ released.1))
  have finish := rawFinish
  rw [size, suffix] at finish
  have preparedAuthority := cacheFrame.2.2 authority
  obtain ⟨retained, repairFrame, rootIssued, afterDirectory, entries, loaded, consumed,
    getRoot, syncRoot, getPending, findKeeper, clear, syncKeeper⟩ :=
    plan.retainsLiteralAlignedRepair keeperCalls cache.directoryRef cache.activeRef cache.pendingRef source.remove
      (source.stage.stage cache.pendingRef (keeperCalls).modifyPending) source.rename
      (keeps := fun before after => LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)
      (fun first second => second ∘ first) (effects.repairEffects attached named remembered.2) preparedAuthority.directoryCell remembered.2
      (effects.recordsKeeper) effects.readsRoot effects.syncKeepsPending effects.readsPending finish readFrame.2.1 exactKeeper noLater entry.kept
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
  let files := RawMarkedOpenInterpreter.makeCache dir cache.directoryRef cache.activeRef cache.pendingRef
  obtain ⟨uses, atDir⟩ := RawMarkedOpenInterpreter.cacheReferences dir cache.directoryRef cache.activeRef cache.pendingRef
  let refs : OpenSyncCacheRefs files (dir).path := ⟨cache.directoryRef, cache.activeRef, cache.pendingRef, uses, atDir⟩
  obtain ⟨initialized, phaseCache, phaseStorage, phaseVisible⟩ := effects.allocatesPhase phaseReturn
  obtain ⟨keepsPhase, tokenCache, tokenStorage, tokenVisible⟩ := effects.allocatesToken tokenReturn
  let allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired :=
    ⟨phase, token, afterPhase, returnedAt, phaseReturn, initialized, tokenReturn, keepsPhase phase⟩
  let state := allocation.readyState writer dir cache.owner cache.rootSlot refs.directory refs.active refs.pending
    phaseIdentity tokenIdentity
  have dirCached : state.cache.directory = some (cache.captured, cache.rootSlot, 0) := by
    change (view.cacheAt repaired cache.directoryRef cache.activeRef cache.pendingRef).directory = _
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
  have atRoot := (readFrame.1.visible _ protectedRoot).1.trans (rootNamed.trans (congrArg some rootInCensus.symm))
  have atLock := (readFrame.1.visible _ protectedLock).1.trans
    (lockNamed.trans (congrArg some repairedAuthority.ownerAttached.2.2.symm))
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
      .ok (RawMarkedOpenInterpreter.assemble dir cache.lock files allocation.phase allocation.token) allocation.afterToken :=
    returned.trans (congrArg (fun value => EStateM.Result.ok value returnedAt) tableEq)
  have compatible (captured : DescriptorInventory) (seen : state.cache.directory = some (captured, cache.rootSlot, 0)) :
      captured.inode cache.rootSlot.description = state.census.inode cache.rootSlot.description := by
    rw [dirCached] at seen
    obtain rfl := congrArg Prod.fst (Option.some.inj seen).symm
    exact rootInCensus.symm
  exact plan.continuesLiteralAligned (allocation := allocation) (cache := refs)
    (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
    request cause (RawMarkedOpenInterpreter.assembles dir cache.lock files) retained rfl plan.targetEq entry.manifest rfl
    keepsSeals repairedAuthority.ownerAttached.1 repairedAuthority.ownerAttached.2.1 repairedAuthority.rootAttached.2.1
    ⟨_, dirCached⟩ phaseCache tokenCache compatible phaseEffects tokenEqual exactReturn observe visible
    preparedDurability atRoot atLock (keeperInode := inode)
    (by simpa only [keeperPathEq] using keeperBound) (keeperEq.symm ▸ preparedBytes) noAlias
    (effects.syncStorage state rfl inode) (by simpa only [keeperPathEq] using effects.syncHandles attached named remembered.2)
    (rootInCensus.symm ▸ preparedAuthority.rootAttached) attached
    (by simpa only [keeperPathEq] using remembered.2) getRoot syncRoot getPending
    (by simpa only [keeperPathEq] using findKeeper) (by simpa only [keeperPathEq] using clear) syncKeeper
    (phaseStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
    (tokenStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
    (fun other _ => congrFun phaseVisible other) (fun other _ => congrFun tokenVisible other)

/-- Carry the selected reboot entry through the failed opens, then
interpret one literal successful open at the resulting heap. An earlier
write can select either marker independently of these recovery calls. -/
theorem NativeReadPosition.opensLiteralAlignedAfterWriteRetries
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (request : WriteRequest) (cause : IO.Error) {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table request.rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {firstOffset : Nat} (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target (fun atHeap => (observe atHeap).files.names) visible first)
    (window : current.state.writer.wal.NamespaceWindow dir firstOffset (prior ++ batch).length (observe first).files.names)
    (durable : current.state.SelectedRetryDurability target (observe first))
    {attempts : source.FailedCalls first returns reached}
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun atHeap => ⟨(observe atHeap).files.names, fun inode => [visible atHeap inode]⟩)
      current.state.selectedRetryPath
      (fun atHeap =>
        current.state.writer.wal.NamespaceWindow dir firstOffset (prior ++ batch).length (observe atHeap).files.names ∧
        RawOpenRetryTrace.KeeperAt view dir target (fun atHeap => (observe atHeap).files.names) visible atHeap ∧
        current.state.SelectedRetryDurability target (observe atHeap)) attempts)
    (admission : source.AlignedAdmissionEffects view current.state input reached observe visible)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootBinding : (observe reached).files.names (dir).path = some (namespaceView.modelObject root))
    (effects : ∀ (cache : HeldOpenCache heap) (plan : current.SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      source.LiteralAlignedEffects cache namespaceView root (current := current) (batch := batch) (target := target)
        plan observe visible)
    (exactKeeper : (view.files reached).image.keeper.active = some target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (tokenEqual : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {returnedAt : heap} {returnedTable : DiskTable}
    (returned : source.openTable input reached = .ok returnedTable returnedAt) :
    ∃ (plan : current.SelectedWritePlan batch target (view.files reached).image)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (keptBatch : List WAL.Write),
      source.openTable input reached = .ok handle.table start.reached ∧
      start.current.history = plan.history ∧
      (⟨prior, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        [.uncertainWriteCrashRecovered request input cause batch keptBatch] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session ∧
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) := by
  obtain ⟨plan, physical, entry, settled⟩ := current.preparesDurableVisibleWriteRetry prepared fits admitted
    observe visible covers initial window durable retryEffects
  obtain ⟨held, framed, authority, rootNamed, lockNamed, _, _, worker⟩ :=
    RawMarkedOpenInterpreter.reachesAlignedCache admission settled.protectedFiles returned
  have rootObject := Option.some.inj (rootBinding.symm.trans rootNamed)
  obtain ⟨handle, start, cache, keptBatch, opened, history, ledger, replay, writeEntry⟩ :=
    plan.returnsLiteralAlignedWriter held namespaceView root request cause observe visible
      (effects held plan authority rootObject) framed authority rootNamed lockNamed entry physical exactKeeper
      noLater settled phaseIdentity tokenIdentity phaseEffects tokenEqual returned worker
  exact ⟨plan, handle, start, cache, keptBatch, opened, history, ledger, replay, writeEntry⟩

end LiteralContinuation

end Alvoki.Storage.DiskSession
