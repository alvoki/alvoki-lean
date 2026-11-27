import Alvoki.Storage.Disk.NativeSourceLedger
import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperStorage

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
  remember : ∀ {path file before after},
    (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending pending
      (pushPending path file) before = .ok () after → alignedReadFrame names visible scope keeps before after

/-- The healthy worker's returned table and the reached callbacks that
read its selected checkpoint and WAL, repair the keeper and allocate it. -/
abbrev RawMarkedOpenInterpreter.LiteralMarkedReturn
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory)
    {image : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout image history)
    (checkpoint : Option (PackedTable × UInt64))
    (lock : IO.FS.Handle) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    (keeps : heap → heap → Prop) (entry returnedAt : heap) (table : DiskTable) : Prop :=
    let keeperCalls := source.keeperCallbacks.withFileReads source.fileCalls
    let segment := layout.keeper
    let path := (directory).file (.walSegment segment.first)
    let cache := RawMarkedOpenInterpreter.makeCache directory cached active pending
    let files := (layout.sealed ++ [segment]).map fun item => (item.first, item.bytes)
    ∃ (count : UInt64) (markerBytes patched : ByteArray) (logical : PackedTable)
      (keeper : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat)
      (readHeap prepared repaired : heap) (extent : Nat) (newer : List Nat)
      (phase : IO.Ref (Phase Installed)) (afterPhase : heap) (token : IO.Ref Unit),
      image.directory.active.walBoundary = some markerBytes ∧
      WAL.Boundary.decode markerBytes = .ok count ∧
      count.toNat / WAL.frameSize = layout.range.through ∧
      recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files = .ok (patched, logical) ∧
      names entry path = some inode ∧ attachedReadSlot view keeper slot inode readHeap ∧
      ((segment.bytes.size = extent ∧
        keeperCalls.modifyPending pending (pushPending path keeper) readHeap = .ok () prepared) ∨
       (segment.bytes.size < extent ∧ source.fileCalls.release keeper readHeap = .ok () prepared)) ∧
      extent = (segment.bytes ++ layout.tail).size ∧
      (∀ start, start ∈ newer ↔ layout.range.through < start ∧
        ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ∧
      (CheckpointSurvivingFiles.mk (names entry) fun inode => [visible entry inode]).Frames scope
        ⟨names prepared, fun inode => [visible prepared inode]⟩ ∧
      (∀ other, scope other → (other = (directory).path ∨ ∃ file, other = (directory).file file) →
        names prepared other = some inode → other = path) ∧
      keeps entry prepared ∧ keeps cacheReady prepared ∧
      finishBoundedMarkedOpen directory ⟨layout.range.through, segment.first, newer, segment.bytes⟩ extent
        source.remove (source.stage.stage pending keeperCalls.modifyPending)
        (keeperCalls.syncPaths (directory).path cached active pending) source.rename prepared =
        .ok () repaired ∧
      source.allocatePhase (.ready (Reopened.installed
        ⟨logical, (checkpoint.getD (.empty, 0)).2, count, segment.first⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token returnedAt ∧
      table = RawMarkedOpenInterpreter.assemble directory lock cache phase token ∧
      ∃ (checked marked afterCheckpoint afterMarker : heap) (metadata : IO.FS.Metadata),
        rejectFlatWalWith directory
          (optionalMetadataWith (source.calls.lookup (directory.file .wal))) cacheReady = .ok () checked ∧
        optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked = .ok (some metadata) marked ∧
        readIntegrityCheckpointSized directory
          (source.fileCalls.readOptional directory (directory.file .manifest))
          source.fileCalls.runSize source.fileCalls.runPrefix marked = .ok checkpoint afterCheckpoint ∧
        source.fileCalls.readOptional directory (directory.file .walBoundary) afterCheckpoint =
          .ok (some markerBytes) afterMarker

/-- The selected checkpoint and WAL bytes fix the replay throughout
the marked worker. The actual extent selects whether the keeper
is remembered or released. The directory scan fixes the suffix
handed to repair independently of that extent. -/
theorem RawMarkedOpenInterpreter.readsLiteralMarkedOpen
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory)
    {image : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout image history)
    {durable : RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable layout.target.pair.manifest checkpoint)
    (lock : IO.FS.Handle) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cacheReady : heap)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (scope : FilePath → Prop)
    {keeps : heap → heap → Prop} (keepsRefl : ∀ atHeap, keeps atHeap atHeap)
    (keepsTrans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (admissionFrame : alignedReadFrame names visible scope keeps reached cacheReady)
    (effects : source.AlignedReadEffects view directory pending names visible namespaceView root scope keeps)
    (manifestStored : (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).StoresManifest
      directory layout.target.pair.manifest)
    (runsStored : ∀ bytes metadata, layout.target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload, durable metadata.header.generation index = some payload →
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Stored
        (directory.file (.run metadata.header.generation index)) payload)
    (markerStored : ∀ marker, image.directory.active.walBoundary = some marker →
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Stored
        ((directory).file .walBoundary) marker)
    (manifestScoped : scope (directory.file .manifest))
    (runsScoped : ∀ bytes metadata, layout.target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, scope (directory.file (.run metadata.header.generation index)))
    (markerScoped : scope (directory.file .walBoundary))
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (scopedWindow : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
      scope ((directory).file (.walSegment start)))
    (child : ∀ start, layout.first ≤ start → start ≤ layout.range.through →
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names reached ((directory).file (.walSegment start)))
    (laterAbsent : ∀ {before entries listed}, source.directoryCalls.run directory.path before = .ok entries listed →
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Frames scope
        ⟨names listed, fun inode => [visible listed inode]⟩ →
      MarkedWalExtentReports.TruthfulAbsenceOn (layout.range.through < ·) source.fileCalls directory
        namespaceView root (entries.toList.map (·.fileName)) listed)
    (physical : layout.VisibleWal directory (names reached) (visible reached))
    {returnedAt : heap} {table : DiskTable}
    (returned : source.worker cached active pending directory lock
      (RawMarkedOpenInterpreter.makeCache directory cached active pending) cacheReady = .ok table returnedAt) :
    source.LiteralMarkedReturn directory layout checkpoint lock cached active pending cacheReady view
      names visible namespaceView root scope keeps reached returnedAt table ∧
    ∃ (before listed : heap) (entries : Array IO.FS.DirEntry),
      source.directoryCalls.run directory.path before = .ok entries listed ∧
      (CheckpointSurvivingFiles.mk (names reached) fun inode => [visible reached inode]).Frames scope
        ⟨names listed, fun inode => [visible listed inode]⟩ := by
  let keeperCalls := source.keeperCallbacks.withFileReads source.fileCalls
  let segment := layout.keeper
  let files := (layout.sealed ++ [segment]).map fun item => (item.first, item.bytes)
  obtain ⟨watermark, _, markerBytes, count, markerName, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have through : count.toNat / WAL.frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have checkpointCount := Option.some.inj (selected.watermark.symm.trans watermark)
  have statExtent {path before metadata after inode}
      (call : source.fileCalls.stat path before = .ok (.ok metadata) after) (bound : names before path = some inode) :
      metadata.byteSize.toNat = (visible before inode).size := by
    obtain ⟨actual, _, boundAtStat, size⟩ := effects.stat call
    exact (Option.some.inj (boundAtStat.symm.trans bound)) ▸ size
  let filesAt (atHeap : heap) : CheckpointSurvivingFiles := ⟨names atHeap, fun inode => [visible atHeap inode]⟩
  let visibleFrame before after := (filesAt before).Frames scope (filesAt after)
  obtain ⟨markerInode, markerNamed, _⟩ := markerStored _ markerName
  have markerAtCache : names cacheReady ((directory).file .walBoundary) = some markerInode :=
    (admissionFrame.1 _ markerScoped).1.trans markerNamed
  have flatKeepsMarker {checked name message}
      (ran : source.calls.lookup ((directory).file .wal) cacheReady =
        .ok (.error (.noFileOrDirectory name 2 message)) checked) :
      names checked ((directory).file .walBoundary) = names cacheReady ((directory).file .walBoundary) := by
    simpa only [ran, reachedState] using ((effects.guard ((directory).file .wal) cacheReady).1 _ markerScoped).1
  obtain ⟨checked, marked, metadata, flat, marker⟩ :=
    source.worker_reachesMarkedGuards directory lock cached active pending cacheReady names markerAtCache flatKeepsMarker effects.markerMissing returned
  have readsVisible : source.fileCalls.ScopeFrames visibleFrame :=
    effects.fileFrames.map (fun framed => framed.1)
  have listingVisible : source.directoryCalls.ScopeFrames directory visibleFrame :=
    ⟨fun ran => (effects.listingFrames.openDir ran).1, fun ran => (effects.listingFrames.readDir ran).1,
      fun opened scanned closed => (effects.listingFrames.closeDir opened scanned closed).1⟩
  obtain ⟨afterCheckpoint, afterMarker, length, payloads, extent, prepared, repaired, patched, logical, first,
    bytes, phase, afterPhase, token, checkpointRead, markerRead, readMarker, wal, framed, replay, lastKeeper, finish, allocPhase, allocToken,
    assembled⟩ := source.worker_selectsCheckpointAndMarker directory lock cached active pending cacheReady
      names visible effects.opens effects.reads selected manifestStored runsStored (markerStored _ markerName)
      scope manifestScoped runsScoped markerScoped admissionFrame.1 (fun path before => (effects.guard path before).1)
      readsVisible (fun path before => (effects.statFrame path before).1) statExtent effects.statMissing effects.eof flat marker returned
  have countEq : length = count := Except.ok.inj (readMarker.symm.trans decoded)
  subst length
  rw [checkpointCount] at wal
  have childAtRead (start : Nat) (lower : layout.first ≤ start) (upper : start ≤ layout.range.through) :
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names afterMarker ((directory).file (.walSegment start)) :=
    (child start lower upper).trans ((framed _ (scopedWindow start lower upper)).1).symm
  obtain ⟨payloadEq, extentEq, newer, ⟨entries, listed, listedCall, listedFrame⟩, file, slot, inode, _, _, readHeap, named, _, attached, route, preserved, privateAtReturn⟩ :=
    source.fileCalls.readsCanonicalWal source.directoryCalls directory view names visible layout namespaceView root scope
      effects.opens effects.reads readsVisible listingVisible
      (fun path file => keeperCalls.modifyPending pending (pushPending path file))
      (fun ran => (effects.remember ran).1) effects.statObject effects.stat
      (fun path before => (effects.statFrame path before).1) framed
      (fun listed => source.directoryCalls.listedRootNames (directory).path namespaceView root effects.streamObject listed
        (fun _ _ ran => effects.streamRoot ran) (fun _ _ _ _ opened scan close => effects.complete opened scan close))
      (fun {entries listedHeap} listed fromEntry => by
        have bounded : MarkedWalExtentReports.TruthfulAbsenceOn
            (fun start => layout.first ≤ start ∧ start ≤ layout.range.through) source.fileCalls directory
            namespaceView root (entries.toList.map (·.fileName)) listedHeap :=
          source.fileCalls.absenceOnFromNamePresence directory names visible namespaceView root scope
            (relevant := fun start => layout.first ≤ start ∧ start ≤ layout.range.through) fromEntry
            (fun path before => (effects.statFrame path before).1) effects.statMissing
            (fun start inside => scopedWindow start inside.1 inside.2)
            (fun start inside => by
              rw [← child start inside.1 inside.2, Option.isSome_map, Option.isSome_iff_exists])
        intro earlier rest name start order parsed lower
        by_cases within : start ≤ layout.range.through
        · exact bounded order parsed ⟨lower, within⟩
        · exact laterAbsent listed fromEntry order parsed (Nat.lt_of_not_ge within))
      through following physical scopedWindow childAtRead wal
  let frame := alignedReadFrame names visible scope keeps
  have refl (atHeap : heap) : frame atHeap atHeap := ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, keepsRefl atHeap⟩
  have trans {before middle after : heap} (left : frame before middle) (right : frame middle after) : frame before after :=
    ⟨left.1.trans right.1, keepsTrans left.2 right.2⟩
  have throughGuards := markedGuards_keepFrame (frame := frame) directory source.calls.lookup trans effects.guard flat marker
  have throughCheckpoint := source.fileCalls.framesCheckpointSuccess directory refl trans effects.fileFrames effects.statFrame checkpointRead
  have throughMarker := source.fileCalls.readOptionalFrames effects.fileFrames refl trans effects.statFrame
    directory ((directory).file .walBoundary) afterCheckpoint
  rw [markerRead, reachedState] at throughMarker
  have throughWal := source.fileCalls.selectedWalKeepsFrame source.directoryCalls directory refl trans effects.fileFrames
    effects.listingFrames effects.statFrame
    (fun path file => keeperCalls.modifyPending pending (pushPending path file)) effects.remember wal
  have fromCache := trans throughGuards (trans throughCheckpoint (trans throughMarker throughWal))
  have throughReader : keeps reached prepared := (trans admissionFrame fromCache).2
  have last : payloads.files.getLast? = some (segment.first, segment.bytes) := by
    rw [payloadEq, List.map_append]
    simp [segment]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lastKeeper.symm.trans last))
  refine ⟨?_, afterMarker, listed, entries, listedCall, listedFrame⟩
  refine ⟨count, markerBytes, patched, logical, file, slot, inode, readHeap, prepared, repaired, extent, payloads.newer,
    phase, afterPhase, token, markerName, decoded, through, ?_, named, attached, route, extentEq, newer, preserved,
    privateAtReturn (fun looked object => effects.statLinks looked object ⟨segment.first, rfl⟩), throughReader,
    fromCache.2, ?_, allocPhase, allocToken, assembled,
    ⟨checked, marked, afterCheckpoint, afterMarker, metadata, flat, marker, checkpointRead, markerRead⟩⟩
  · simpa only [payloadEq, files, segment] using replay
  · simpa only [through] using finish

end LiteralRead

section LiteralRepair

/-- Interpret the reached aligned repair callbacks. A rooted barrier can
settle an earlier replacement's binding while keeping its visible bytes.
The file sync settles the selected keeper after that barrier. -/
structure AlignedRepairImageEffects (view : OpenCloseHeapView heap FileImage)
    (calls : AlignedKeeperCacheCallbacks heap) (root keeper : IO.FS.Handle)
    (keeperPath : FilePath) (keeps : heap → heap → Prop) where
  rootLoad : ∀ {cached before after}, calls.getDirectory cached before = .ok (some root) after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  rootSync : ∀ {cached before issued after}, calls.getDirectory cached before = .ok (some root) issued →
    calls.sync root issued = .ok () after →
    (view.files after).image = { (view.files issued).image.syncDirectory with keeper := (view.files after).image.keeper } ∧
    (view.files after).image.keeper.active = (view.files issued).image.keeper.active ∧ keeps issued after
  pendingLoad : ∀ {pending before after entries}, calls.getPending pending before = .ok entries after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  pendingClear : ∀ {pending before after entries}, calls.setPending pending entries before = .ok () after →
    (view.files after).image = (view.files before).image ∧ keeps before after
  keeperSync : ∀ {pending rootIssued authorized loaded consumed after entries},
    calls.sync root rootIssued = .ok () authorized →
    calls.getPending pending authorized = .ok entries loaded →
    entries.find? (fun item => item.1 == keeperPath) = some (keeperPath, keeper) →
    calls.setPending pending (entries.filter (fun item => item.1 != keeperPath)) loaded = .ok () consumed →
    calls.sync keeper consumed = .ok () after →
    (view.files after).image = (view.files consumed).image.syncKeeper ∧ keeps consumed after

/-- Interpret the aligned repair's actual directory sync, any checked
suffix unlinks, and the sync of the remembered keeper. -/
theorem AlignedRepairImageEffects.readyAfterReturn
    {directory : DiskDirectory} {target : Target} (repairPlan : Plan)
    (size : repairPlan.keeperBytes.size = repairPlan.keeperSize)
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {readHeap prepared repaired : heap} {root keeper : IO.FS.Handle}
    {keeps : heap → heap → Prop} {before : heap}
    (keepsTrans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (model : AlignedRepairImageEffects view calls root keeper (directory.file (.walSegment repairPlan.keeper)) keeps)
    (cachedRoot : view.directory prepared cached = some root)
    (remembered : calls.modifyPending pending (pushPending (directory.file (.walSegment repairPlan.keeper)) keeper)
      readHeap = .ok () prepared)
    (recordsKeeper : calls.modifyPending pending (pushPending (directory.file (.walSegment repairPlan.keeper)) keeper)
      readHeap = .ok () prepared →
      view.pending prepared pending = pushPending (directory.file (.walSegment repairPlan.keeper)) keeper
        (view.pending readHeap pending))
    (readsRoot : ∀ {result issued}, calls.getDirectory cached prepared = .ok result issued →
      result = view.directory prepared cached ∧ view.pending issued pending = view.pending prepared pending)
    (syncKeepsPending : ∀ {issued after}, calls.sync root issued = .ok () after →
      view.pending after pending = view.pending issued pending)
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (suffix : repairPlan.newer ≠ [] → calls.SuffixCacheEffects view directory repairPlan cached pending root remove)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ repairPlan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (view.files after).image = (view.files before).image.unlinkLater ordinal ∧ keeps before after)
    (finished : finishBoundedMarkedOpen directory repairPlan
      repairPlan.keeperBytes.size remove write (calls.syncPaths directory.path cached active pending) rename prepared =
        .ok () repaired)
    (readOnly : (view.files prepared).image = (view.files before).image)
    (exactKeeper : (view.files before).image.keeper.active = some target.trimmed)
    (covers : ∀ ordinal ∈ (view.files before).image.later.visible, ordinal ∈ repairPlan.newer)
    (selected : (view.files before).image.directory.active = target.pair) :
    (view.files repaired).image.Ready target ∧
    (view.files repaired).image.kept = (view.files before).image.kept ∧ keeps prepared repaired ∧
    ∃ (rootIssued authorized keeperEntry : heap) (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getDirectory cached prepared = .ok (some root) rootIssued ∧
      calls.sync root rootIssued = .ok () authorized ∧
      (if repairPlan.newer = [] then keeperEntry = authorized
        else ∃ (unlinked suffixIssued : heap),
          ((repairPlan.newer.map Step.unlink).forM
            (performPaths directory repairPlan remove throw write (calls.syncPaths directory.path cached active pending) rename))
            authorized = .ok () unlinked ∧
          calls.getDirectory cached unlinked = .ok (some root) suffixIssued ∧
          calls.sync root suffixIssued = .ok () keeperEntry) ∧
      calls.getPending pending keeperEntry = .ok entries loaded ∧
      entries.find? (fun item => item.1 == directory.file (.walSegment repairPlan.keeper)) =
        some (directory.file (.walSegment repairPlan.keeper), keeper) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != directory.file (.walSegment repairPlan.keeper)))
        loaded = .ok () consumed ∧
      calls.sync keeper consumed = .ok () repaired := by
  obtain ⟨rootIssued, authorized, keeperEntry, entries, loaded, consumed, getRoot, syncRoot, pruned,
    getPending, found, clear, syncKeeper⟩ :=
    calls.alignedRepairSyncsWithSuffix view directory repairPlan repairPlan.keeperBytes.size cached active pending remove write rename
      size cachedRoot remembered recordsKeeper readsRoot syncKeepsPending readsPending suffix finished
  obtain ⟨getRootImage, getRootFrame⟩ := model.rootLoad getRoot
  obtain ⟨syncRootImage, syncRootKeeper, syncRootFrame⟩ := model.rootSync getRoot syncRoot
  have authorityFrame := keepsTrans getRootFrame syncRootFrame
  have authorizationImage : (view.files authorized).image =
      { (view.files before).image.syncDirectory with keeper := (view.files authorized).image.keeper } := by
    rw [← readOnly, ← getRootImage]
    exact syncRootImage
  have authorizationKeeper := syncRootKeeper.trans
    (congrArg (fun image : FileImage => image.keeper.active) (getRootImage.trans readOnly))
  have suffixReady :
      (view.files keeperEntry).image = { (view.files before).image.syncDirectory with
        later := LaterNames.settled [], keeper := (view.files keeperEntry).image.keeper } ∧
      (view.files keeperEntry).image.keeper.active = (view.files before).image.keeper.active ∧
      keeps prepared keeperEntry ∧ ∃ lastIssued, calls.sync root lastIssued = .ok () keeperEntry := by
    by_cases empty : repairPlan.newer = []
    · have immediate : keeperEntry = authorized := by simpa only [empty, ite_true] using pruned
      subst keeperEntry
      have noLater : (view.files before).image.later.visible = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro ordinal present
        exact List.not_mem_nil (empty ▸ covers ordinal present)
      refine ⟨?_, authorizationKeeper, authorityFrame, rootIssued, syncRoot⟩
      rw [authorizationImage]
      simp only [FileImage.syncDirectory, LaterNames.syncDirectory, noLater]
    · have later : repairPlan.newer ≠ [] := empty
      obtain ⟨unlinked, suffixIssued, removed, getSuffix, syncSuffix⟩ := by
        simpa only [ite_eq_right later] using pruned
      obtain ⟨unlinkedImage, unlinkedFrame⟩ :=
        filesAndFrameOfReturnedWalUnlinks directory repairPlan remove write (calls.syncPaths directory.path cached active pending) rename
          (fun atHeap => (view.files atHeap).image) keeps keepsTrans authorityFrame unlink removed
      obtain ⟨getSuffixImage, getSuffixFrame⟩ := model.rootLoad getSuffix
      obtain ⟨syncSuffixImage, syncSuffixKeeper, syncSuffixFrame⟩ := model.rootSync getSuffix syncSuffix
      have covered : ∀ ordinal ∈ (view.files authorized).image.later.visible, ordinal ∈ repairPlan.newer := by
        rw [authorizationImage]
        exact covers
      have settledPrune := FileImage.syncAfterCoveringUnlinks _ _ covered
      have prunedKeeper := congrArg (fun image : FileImage => image.keeper.active) settledPrune
      have unlinksKeepKeeper : (view.files unlinked).image.keeper.active =
          (view.files authorized).image.keeper.active := by
        rw [unlinkedImage]
        exact prunedKeeper
      have keeperActive := syncSuffixKeeper.trans
        ((congrArg (fun image : FileImage => image.keeper.active) getSuffixImage).trans
          (unlinksKeepKeeper.trans authorizationKeeper))
      refine ⟨?_, keeperActive, keepsTrans unlinkedFrame (keepsTrans getSuffixFrame syncSuffixFrame),
        suffixIssued, syncSuffix⟩
      rw [syncSuffixImage, getSuffixImage, unlinkedImage, settledPrune, authorizationImage]
      rfl
  obtain ⟨suffixImage, suffixKeeper, suffixFrame, lastIssued, lastRoot⟩ := suffixReady
  obtain ⟨getPendingImage, getPendingFrame⟩ := model.pendingLoad getPending
  obtain ⟨clearImage, clearFrame⟩ := model.pendingClear clear
  obtain ⟨syncKeeperImage, syncKeeperFrame⟩ := model.keeperSync lastRoot getPending found clear syncKeeper
  have framed := keepsTrans suffixFrame (keepsTrans getPendingFrame (keepsTrans clearFrame syncKeeperFrame))
  have keeperEffect : (view.files repaired).image = (view.files keeperEntry).image.syncKeeper :=
    syncKeeperImage.trans (congrArg FileImage.syncKeeper (clearImage.trans getPendingImage))
  have ready : (view.files repaired).image.Ready target := by
    rw [keeperEffect, suffixImage]
    refine FileImage.readyAfterKeeperSync ?_ ?_ (suffixKeeper.trans exactKeeper) ⟨rfl, rfl⟩
    · exact selected
    · exact congrArg (fun pair => [pair]) selected
  have keptBySync : (view.files repaired).image.kept = (view.files before).image.kept := by
    rw [keeperEffect, suffixImage]
    rfl
  exact ⟨ready, keptBySync, framed, rootIssued, authorized, keeperEntry, entries, loaded, consumed,
    getRoot, syncRoot, pruned, getPending, found, clear, syncKeeper⟩

/-- Logical file effects of the reached replacement callbacks. The
directory barrier settles the pair and later names independently of
the keeper, whose final settlement requires its completed rename. -/
structure LiteralKeeperReplacementEffects (view : OpenCloseHeapView heap FileImage)
    (directory : DiskDirectory) (plan : Plan) (target : Target)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (keeps : heap → heap → Prop) : Prop where
  rootSync : ∀ {before after}, sync #[directory.path] before = .ok () after →
    (view.files after).image = { (view.files before).image.syncDirectory with keeper := (view.files after).image.keeper } ∧
    keeps before after
  unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
    remove (directory.file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () →
    (view.files after).image = (view.files before).image.unlinkLater ordinal ∧ keeps before after
  writeStage : ∀ {before after}, write (directory.file .stagedWal) target.trimmed before = .ok () after →
    (view.files before).image.effect target (.replace .writeStaged) = some (view.files after).image ∧ keeps before after
  syncStage : ∀ {entry before after}, write (directory.file .stagedWal) target.trimmed entry = .ok () before →
    sync #[directory.file .stagedWal] before = .ok () after →
    (view.files before).image.effect target (.replace .syncStaged) = some (view.files after).image ∧ keeps before after
  renameStage : ∀ {staged before after}, sync #[directory.file .stagedWal] staged = .ok () before →
    rename (directory.file .stagedWal) (directory.file (.walSegment plan.keeper)) before = .ok () after →
    (view.files before).image.effect target (.replace .renameStaged) = some (view.files after).image ∧ keeps before after
  settleKeeper : ∀ {staged before renamed after},
    sync #[directory.file .stagedWal] staged = .ok () before →
    rename (directory.file .stagedWal) (directory.file (.walSegment plan.keeper)) before = .ok () renamed →
    sync #[directory.path] renamed = .ok () after →
    (view.files renamed).image.keeper.step target.trimmed .syncDirectory = some (view.files after).image.keeper

private theorem FileImage.replacementImageOfEffects {target : Target}
    {initial staged synced renamed repaired : FileImage}
    (write : initial.effect target (.replace .writeStaged) = some staged)
    (sync : staged.effect target (.replace .syncStaged) = some synced)
    (rename : synced.effect target (.replace .renameStaged) = some renamed)
    (settle : renamed.effect target (.replace .syncDirectory) = some repaired) :
    repaired = { initial.syncDirectory with keeper := Publication.Image.settled (some target.trimmed) } := by
  have ran : (Publication.steps.map Step.replace).foldlM (fun image action => image.effect target action) initial =
      some repaired := by
    simp only [Publication.steps, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
      write, sync, rename, settle, Bind.bind, Option.bind, Pure.pure]
  exact Option.some.inj ran.symm

/-- Derive the repaired file image at the literal longer-keeper return.
The checked unlink pass is shared with aligned repair. The former
keeper's crash choices are irrelevant once replacement settles. -/
theorem LiteralKeeperReplacementEffects.readyAfterReturn
    {directory : DiskDirectory} {plan : Plan} {target : Target}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit} {keeps : heap → heap → Prop}
    (effects : LiteralKeeperReplacementEffects view directory plan target remove write sync rename keeps)
    (trans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    {extent : Nat} {entry repaired : heap} (longer : plan.keeperSize < extent)
    (payload : plan.keeperBytes.extract 0 plan.keeperSize = target.trimmed)
    (selected : (view.files entry).image.directory.active = target.pair)
    (covers : ∀ ordinal ∈ (view.files entry).image.later.visible, ordinal ∈ plan.newer)
    (returned : finishBoundedMarkedOpen directory plan extent remove write sync rename entry = .ok () repaired) :
    (view.files repaired).image.Ready target ∧
    (view.files repaired).image.kept = (view.files entry).image.kept ∧ keeps entry repaired := by
  obtain ⟨authorized, unlinked, pruned, staged, synced, renamed, firstRoot, unlinks, pruneRoot, writeStage,
    syncStage, renameStage, lastRoot⟩ :=
    finishBoundedMarkedOpen_replacementReached directory plan extent remove write sync rename longer returned
  obtain ⟨authorizationImage, authorizationFrame⟩ := effects.rootSync firstRoot
  obtain ⟨unlinkedImage, unlinkFrame⟩ :=
    filesAndFrameOfReturnedWalUnlinks directory plan remove write sync rename
      (fun atHeap => (view.files atHeap).image) keeps trans authorizationFrame effects.unlink unlinks
  have authorizedCoverage : ∀ ordinal ∈ (view.files authorized).image.later.visible, ordinal ∈ plan.newer := by
    rw [authorizationImage]
    exact covers
  obtain ⟨pruneImage, pruneFrame⟩ := effects.rootSync pruneRoot
  have prunedImage : (view.files pruned).image =
      { (view.files entry).image.syncDirectory with later := LaterNames.settled [], keeper := (view.files pruned).image.keeper } := by
    calc
      _ = { (view.files unlinked).image.syncDirectory with keeper := (view.files pruned).image.keeper } := pruneImage
      _ = { (view.files authorized).image.syncDirectory with
        later := LaterNames.settled [], keeper := (view.files pruned).image.keeper } := by
        rw [unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ authorizedCoverage]
      _ = _ := by rw [authorizationImage]; rfl
  rw [payload] at writeStage
  obtain ⟨written, writeFrame⟩ := effects.writeStage writeStage
  obtain ⟨persisted, stageFrame⟩ := effects.syncStage writeStage syncStage
  obtain ⟨moved, moveFrame⟩ := effects.renameStage syncStage renameStage
  obtain ⟨lastImage, lastFrame⟩ := effects.rootSync lastRoot
  have settle : (view.files renamed).image.effect target (.replace .syncDirectory) =
      some (view.files repaired).image := by
    simp only [FileImage.effect, ite_true, effects.settleKeeper syncStage renameStage lastRoot, Option.map_some, ← lastImage]
  have image := FileImage.replacementImageOfEffects written persisted moved settle
  have ready : (view.files repaired).image.Ready target := by
    rw [image, prunedImage]
    exact ⟨selected, congrArg (fun pair => [pair]) selected, rfl, rfl, ⟨rfl, rfl⟩⟩
  have kept : (view.files repaired).image.kept = (view.files entry).image.kept := by
    rw [image, prunedImage]
    rfl
  have throughPrune := trans unlinkFrame pruneFrame
  have throughRename := trans (trans writeFrame stageFrame) moveFrame
  exact ⟨ready, kept, trans throughPrune (trans throughRename lastFrame)⟩

/-- The replay and the completed longer-keeper replacement together
supply the ordinary retained writer at the actual repair return. -/
theorem NativeReadPosition.SelectedWritePlan.retainsLiteralLongerRepair
    (plan : current.SelectedWritePlan batch target (view.files reached).image) (newer : List Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {prepared repaired : heap} {extent : Nat} {keeps : heap → heap → Prop}
    (trans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    (effects : LiteralKeeperReplacementEffects view dir
      ⟨plan.layout.range.through, plan.layout.keeper.first, newer, plan.layout.keeper.bytes⟩
      plan.layout.target remove write sync rename keeps)
    (longer : plan.layout.keeper.bytes.size < extent)
    (returned : finishBoundedMarkedOpen dir
      ⟨plan.layout.range.through, plan.layout.keeper.first, newer, plan.layout.keeper.bytes⟩ extent
      remove write sync rename prepared = .ok () repaired)
    (readOnly : (view.files prepared).image = (view.files reached).image)
    (covers : ∀ ordinal ∈ (view.files reached).image.later.visible, ordinal ∈ newer)
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
    writer.RetainedReady dir owner.description ∧ keeps prepared repaired := by
  intro installed wal writer
  let repairPlan : Plan := ⟨plan.layout.range.through, plan.layout.keeper.first, newer, plan.layout.keeper.bytes⟩
  have size : repairPlan.keeperBytes.size = repairPlan.keeperSize := plan.layout.target.trimmedSize
  have exactPrefix : repairPlan.keeperBytes.extract 0 repairPlan.keeperSize = plan.layout.target.trimmed := by
    rw [← size, ByteArray.extract_zero_size]
    rfl
  have selected : (view.files prepared).image.directory.active = plan.layout.target.pair := by rw [readOnly]; rfl
  have coversPrepared : ∀ ordinal ∈ (view.files prepared).image.later.visible, ordinal ∈ repairPlan.newer := by
    rw [readOnly]
    exact covers
  obtain ⟨ready, seals, framed⟩ :=
    effects.readyAfterReturn trans (size ▸ longer) exactPrefix selected coversPrepared returned
  have keptByLayout : (view.files repaired).image.kept = (wal.checkpointReopenFiles wal.directory none).kept :=
    seals.trans ((congrArg FileImage.kept readOnly).trans (kept.trans current.readPrefix.refines.1.retained.sealedFiles))
  have keeperEq : plan.layout.keeper.first = wal.active.first := congrArg WalSegment.first plan.keeper
  obtain ⟨retained, _, _, _⟩ := plan.layout.retainedFromActualReplay plan.selected plan.accepted plan.ordered marker decoded rfl
    replayed plan.walLayout plan.walValid current.readPrefix.refines.1.retained.spans rfl keeperEq ready keptByLayout (keepsOwner framed held)
  exact ⟨retained, framed⟩

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

/-- Install an exact repaired writer through the literal phase and token
allocations. The recovery mode has already supplied the ready storage. -/
theorem NativeReadPosition.SelectedWritePlan.installsLiteralRepairedWriter
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (request : WriteRequest) (cause : IO.Error)
    (constructor : DiskTable.OpenReferenceAssembly dir lock syncFiles assemble)
    (stateValid : (readyState).Valid)
    (sameHistory : writer.history = plan.history)
    (ownsSlot : (view.handle repaired lock).2.1 = owner)
    (cachePhase : CacheAllocationFrame view cache.directory cache.active cache.pending repaired allocation.afterPhase)
    (cacheToken : CacheAllocationFrame view cache.directory cache.active cache.pending allocation.afterPhase allocation.afterToken)
    (rootCache : ∃ captured, (readyState).cache.directory = some (captured, directorySlot, 0) ∧
      captured.inode directorySlot.description = (readyState).census.inode directorySlot.description)
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (tokenEqual : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (returned : source.openTable input reached = .ok (assemble allocation.phase allocation.token) allocation.afterToken)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (settled : NativeReadyStorage (readyState) (observe repaired))
    (live : ∀ inode, (observe repaired).files.names ((dir).file (.walSegment writer.wal.active.first)) = some inode →
      visible repaired inode = writer.wal.active.bytes)
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
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) ∧
      start.current.ready.state = readyState ∧ start.reached = allocation.afterToken := by
  have init : PendingClientReplay (log ++ [.uncertainBatch batch]) current.reads (readyState).writer.history :=
    sameHistory.symm ▸ plan.pending
  have bounded : ∀ read ∈ current.reads, read.BoundedBy (readyState).writer.history.length :=
    sameHistory.symm ▸ plan.bounded
  obtain ⟨handle, start, nextCache, opened, reachedEq, _, _, history, submissions, stateEq, reads, _, writeEntry, _⟩ :=
    allocation.opensReadyWriter stateValid constructor cache returned phaseEffects tokenEqual init bounded observe visible settled live
      rfl ownsSlot rfl cachePhase cacheToken rootCache phaseFrame tokenFrame phaseKeeper tokenKeeper
  have selectedHistory := history.trans sameHistory
  obtain ⟨keptBatch, ledger⟩ := plan.ledgerAfterReopen start.current selectedHistory submissions reads request input cause
  exact ⟨handle, start, nextCache, keptBatch, opened, selectedHistory, ledger,
    start.current.ready.readPrefix.guardedReplay, writeEntry, stateEq, reachedEq⟩

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
    (cachePhase : CacheAllocationFrame view cache.directory cache.active cache.pending repaired allocation.afterPhase)
    (cacheToken : CacheAllocationFrame view cache.directory cache.active cache.pending allocation.afterPhase allocation.afterToken)
    (rootCache : ∃ captured, (readyState).cache.directory = some (captured, directorySlot, 0) ∧
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
    (keeperAtEntry : (observe reached).files.names ((dir).file (.walSegment target.first)) = some keeperInode)
    (keeperPayload : writer.wal.active.bytes = target.trimmed)
    (apart : ∀ path, path = (dir).file .walBoundary ∨ (readyState).writeFramePath path →
      (observe prepared).files.names path ≠ some keeperInode)
    (physicalSyncs : AlignedRepairStorageEffects calls view readyState observe visible keeperInode)
    (handleEffects : AlignedRepairHandleEffects calls view ((dir).file (.walSegment writer.wal.active.first)) root keeper)
    (rootAtPrepared : attachedReadSlot view root directorySlot ((readyState).census.inode directorySlot.description) prepared)
    (keeperAtRead : attachedReadSlot view keeper keeperSlot keeperInode readHeap)
    (remembered : calls.modifyPending cache.pending (pushPending ((dir).file (.walSegment writer.wal.active.first)) keeper)
      readHeap = .ok () prepared)
    (repairPlan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (later : ∀ ordinal ∈ repairPlan.newer, writer.wal.active.first < ordinal)
    (beyond : ∀ ordinal ∈ repairPlan.newer, repairPlan.through < ordinal)
    (keepRootOnSync : ∀ {issued after}, calls.sync root issued = .ok () after → ReadSlotDrops view root issued after)
    (unlinkSlots : ∀ {ordinal before after result}, ordinal ∈ repairPlan.newer →
      remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      ReadSlotDrops view root before after ∧ ReadSlotDrops view keeper before after)
    (unlinkStorage : ∀ {ordinal before after result}, ordinal ∈ repairPlan.newer →
      remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (observe before).files.names ((dir).file (.walSegment writer.wal.active.first)) = some keeperInode →
      (observe before).Frames (fun path => (readyState).crashPath path ∧ path ≠ (dir).file (.walSegment ordinal))
        (observe after) ∧ visible after keeperInode = visible before keeperInode)
    {rootIssued afterDirectory keeperEntry loaded consumed : heap} {entries : List (FilePath × IO.FS.Handle)}
    (getRoot : calls.getDirectory cache.directory prepared = .ok (some root) rootIssued)
    (syncRoot : calls.sync root rootIssued = .ok () afterDirectory)
    (pruned : if repairPlan.newer = [] then keeperEntry = afterDirectory
      else ∃ (unlinked suffixIssued : heap),
        ((repairPlan.newer.map Step.unlink).forM (performPaths dir repairPlan remove throw write
          (calls.syncPaths (dir).path cache.directory cache.active cache.pending) rename)) afterDirectory = .ok () unlinked ∧
        calls.getDirectory cache.directory unlinked = .ok (some root) suffixIssued ∧
        calls.sync root suffixIssued = .ok () keeperEntry)
    (getPending : calls.getPending cache.pending keeperEntry = .ok entries loaded)
    (findKeeper : entries.find? (fun item => item.1 == (dir).file (.walSegment writer.wal.active.first)) =
      some ((dir).file (.walSegment writer.wal.active.first), keeper))
    (clear : calls.setPending cache.pending
      (entries.filter (fun item => item.1 != (dir).file (.walSegment writer.wal.active.first))) loaded = .ok () consumed)
    (syncKeeper : calls.sync keeper consumed = .ok () repaired)
    {firstOffset : Nat}
    (covers : ∀ start ∈ writer.wal.segments.map WalSegment.first, firstOffset ≤ start)
    (selectedWindow : writer.wal.NamespaceWindow dir firstOffset repairPlan.through (observe prepared).files.names)
    (boundedStarts : ∀ start ∈ writer.wal.segments.map WalSegment.first, start ≤ repairPlan.through)
    (listed : ∀ start, repairPlan.through < start →
      ((observe prepared).files.names ((dir).file (.walSegment start))).isSome = true → start ∈ repairPlan.newer)
    (walEffects : AlignedRepairWalNameEffects calls dir observe cache.directory cache.pending remove repairPlan.through)
    (phaseNames : ∀ through, WalNamePresenceFrame dir firstOffset through (observe repaired) (observe allocation.afterPhase))
    (tokenNames : ∀ through, WalNamePresenceFrame dir firstOffset through (observe allocation.afterPhase) (observe allocation.afterToken))
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
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) ∧
      start.current.ready.state.session.directory = dir ∧
      (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
      (∀ {inode}, (observe reached).files.names ((dir).file (.walSegment target.first)) = some inode →
        visible reached inode = target.trimmed →
        (observe start.reached).files.names ((dir).file (.walSegment target.first)) = some inode ∧
          visible start.reached inode = target.trimmed) ∧
      ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
        start.current.ready.state.session.directory firstOffset through (observe start.reached) := by
  have directoryCached : ∃ captured, (readyState).cache.directory = some (captured, directorySlot, 0) :=
    rootCache.imp (fun _ bound => bound.1)
  have stateValid : (readyState).Valid := ⟨rfl, rfl, ownerLive, directoryLive, directoryCached, retained⟩
  obtain ⟨protectedFiles, marker, rootSettled⟩ := physical.forReopenedWriter current.readPrefix.refines.1 stateValid rfl
    selected manifest published kept rootBound lockBound
  obtain ⟨settled, live, repairedKeeper, repairedNames⟩ := physicalSyncs.readyAfterAlignedRepair
    repairPlan remove write rename stateValid handleEffects rootAtPrepared keeperAtRead remembered
    keepRootOnSync unlinkSlots unlinkStorage getRoot syncRoot pruned getPending findKeeper clear syncKeeper
    protectedFiles marker rootSettled keeperBound keeperBytes apart selectedWindow boundedStarts
    later beyond listed walEffects
  obtain ⟨handle, start, nextCache, keptBatch, opened, history, ledger, replay, writeEntry, stateEq, reachedEq⟩ :=
    plan.installsLiteralRepairedWriter request cause constructor stateValid sameHistory ownsSlot cachePhase cacheToken
      rootCache phaseEffects tokenEqual returned observe visible settled live phaseFrame tokenFrame phaseKeeper tokenKeeper
  let keeperPath := (dir).file (.walSegment writer.wal.active.first)
  have keeperSelected : (readyState).crashPath keeperPath :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  have atPhase := (phaseFrame.visible keeperPath keeperSelected).1.trans repairedKeeper
  have atToken := (tokenFrame.visible keeperPath keeperSelected).1.trans atPhase
  have bytesAtReturn := (tokenKeeper keeperInode atPhase).trans
    ((phaseKeeper keeperInode repairedKeeper).trans (live keeperInode repairedKeeper))
  refine ⟨handle, start, nextCache, keptBatch, opened, history, ledger, replay, writeEntry, ?_, ?_, ?_, ?_⟩
  · rw [stateEq]
    rfl
  · rw [stateEq]
    exact covers
  · intro inode named _
    have sameInode := Option.some.inj (keeperAtEntry.symm.trans named)
    have sameStart := (congrArg Target.first selected).symm.trans retained.active
    rw [← sameInode, reachedEq, sameStart]
    exact ⟨atToken, bytesAtReturn.trans keeperPayload⟩
  · intro through
    rw [stateEq, reachedEq]
    exact allocation.walWindowAfterAllocations observe writer.wal dir (repairedNames through).1 (repairedNames through).2
      (fun _ => phaseNames through) (fun _ => tokenNames through)

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

/-- The literal cache cell identifies the same live root object in
the current census, even if temporary reads changed other descriptors. -/
theorem LiteralOpenAuthority.cacheRoot {directory : DiskDirectory} {cache : HeldOpenCache heap} {atHeap : heap}
    (authority : LiteralOpenAuthority view directory cache atHeap) :
    (view.cacheAt atHeap cache.directoryRef cache.activeRef cache.pendingRef).directory =
      some (cache.captured, cache.rootSlot, 0) ∧
    cache.captured.inode cache.rootSlot.description = (view.descriptors atHeap).inode cache.rootSlot.description := by
  refine ⟨?_, authority.rootAttached.2.2.symm⟩
  simp only [OpenCloseHeapView.cacheAt, authority.directoryCell, authority.rootHandle, Option.map_some]

def managedPath (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ ∃ file, path = directory.file file

private theorem selectedRetryManagedPath {state : NativeReadyState} {path : FilePath}
    (selected : state.selectedRetryPath path) : managedPath state.session.directory path := by
  rcases selected with mark | immutable
  · exact .inr ⟨.walBoundary, mark⟩
  · exact NativeReadyState.crashPath_rootOrChild
      (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr immutable)))

private theorem RawOpenRetryTrace.SelectedEntry.markerStored
    {state : NativeReadyState} {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (entry : RawOpenRetryTrace.SelectedEntry view state target names visible reached)
    {bytes : ByteArray} (selected : (view.files reached).image.directory.active.walBoundary = some bytes) :
    (CheckpointSurvivingFiles.mk (names reached) (fun inode => [visible reached inode])).Stored
      (state.session.directory.file .walBoundary) bytes := by
  have atTarget := (congrArg DirectoryPublication.Bindings.walBoundary entry.valid.selected).symm.trans selected
  obtain ⟨inode, named, exactBytes⟩ := Option.map_eq_some_iff.mp (entry.marker.trans atTarget)
  exact ⟨inode, named, congrArg (fun bytes => [bytes]) exactBytes⟩

def observedAdmissionFrame (view : OpenCloseHeapView heap FileImage)
    (directory : DiskDirectory) (selectedPath : FilePath → Prop)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) (before after : heap) : Prop :=
  alignedReadFrame (fun atHeap => (observe atHeap).files.names) visible (managedPath directory)
    (fun before after => (observe before).Frames selectedPath (observe after) ∧
      (view.files after).image = (view.files before).image) before after

/-- Local observations of the primitives used to enter the held worker.
The frame does not refer to cache cells ahead of their allocation. -/
structure RawMarkedOpenInterpreter.ObservedAdmissionEffects (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory) (selectedPath : FilePath → Prop)
    (input : FilePath) (entry : heap)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop where
  resolves : ∀ {resolved after}, DiskDirectory.openWith source.calls.realPath input entry = .ok resolved after →
    resolved = directory
  frames : source.HeldCacheFrames (observedAdmissionFrame view directory selectedPath observe visible)
  lockMissing : ∀ {before after name message},
    source.calls.lookup (directory.file .lock) before =
      .ok (.error (.noFileOrDirectory name 2 message)) after →
    (observe before).files.names (directory.file .lock) = none
  lockOpen : ∀ {lock checked before after inode metadata},
    optionalMetadataWith (source.calls.lookup (directory.file .lock)) checked =
      .ok (some metadata) before →
    (metadata.type == .file && metadata.numLinks == 1) = true →
    (observe before).files.names (directory.file .lock) = some inode →
    source.calls.openAppend (directory.file .lock) before = .ok lock after →
    observedAdmissionFrame view directory selectedPath observe visible before after ∧
      ∃ owner, (view.descriptors before).references owner.description = [] ∧
        attachedReadSlot view lock owner inode after
  flock : ∀ {lock owner inode before after}, source.calls.flock lock before = .ok true after →
    (observe before).files.names (directory.file .lock) = some inode →
    attachedReadSlot view lock owner inode before →
    attachedReadSlot view lock owner inode after ∧ (view.files after).owners.Owns directory owner.description
  cache : source.init.ProjectionEffects view directory (fun atHeap => (observe atHeap).files.names)

abbrev RawMarkedOpenInterpreter.AlignedAdmissionEffects (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState) (input : FilePath) (entry : heap)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :=
  source.ObservedAdmissionEffects view state.session.directory state.selectedRetryPath input entry observe visible

private abbrev alignedAdmissionFrame (view : OpenCloseHeapView heap FileImage) (state : NativeReadyState)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :=
  observedAdmissionFrame view state.session.directory state.selectedRetryPath observe visible

/-- Derive the read authority and cache cells at the heap handed to the
worker by the literal successful open. -/
theorem RawMarkedOpenInterpreter.reachesAlignedCache {directory : DiskDirectory} {selectedPath : FilePath → Prop}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    (effects : source.ObservedAdmissionEffects view directory selectedPath input reached observe visible)
    {lockInode : Nat} (lockBound : (observe reached).files.names (directory.file .lock) = some lockInode)
    {returnedAt : heap} {table : DiskTable}
    (returned : source.openTable input reached = .ok table returnedAt) :
    ∃ cache : HeldOpenCache heap,
      observedAdmissionFrame view directory selectedPath observe visible reached cache.ready ∧
      LiteralOpenAuthority view directory cache cache.ready ∧
      (observe reached).files.names directory.path = some (cache.captured.inode cache.rootSlot.description) ∧
      (observe reached).files.names (directory.file .lock) = some (cache.captured.inode cache.owner.description) ∧
      view.active cache.ready cache.activeRef = none ∧ view.pending cache.ready cache.pendingRef = [] ∧
      source.worker cache.directoryRef cache.activeRef cache.pendingRef directory cache.lock
        (RawMarkedOpenInterpreter.makeCache directory cache.directoryRef cache.activeRef cache.pendingRef) cache.ready =
        .ok table returnedAt := by
  obtain ⟨resolved, lock, lockMetadata, _, checked, probed, _, locked, root, cached, active, pending, _, _, _, prepared,
    path, flat, probe, safe, openLock, acquire, openRoot, directoryRef, activeRef, pendingRef, worker⟩ :=
    source.reachesHeldCache input returned
  have resolvedDirectory := effects.resolves path
  subst resolved
  have trans {before middle after} (left : observedAdmissionFrame view directory selectedPath observe visible before middle)
      (right : observedAdmissionFrame view directory selectedPath observe visible middle after) :
      observedAdmissionFrame view directory selectedPath observe visible before after :=
    ⟨left.1.trans right.1, left.2.1.trans right.2.1, right.2.2.trans left.2.2⟩
  have rootScope : managedPath directory directory.path := .inl rfl
  have lockScope : managedPath directory (directory.file .lock) := .inr ⟨.lock, rfl⟩
  have probes := effects.frames.throughProbes trans path flat probe
  have lockAtProbe := (probes.1 _ lockScope).1.trans lockBound
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
  have lockAtEntry := lockBound.trans (congrArg some ownerInode.symm)
  exact ⟨⟨lock, root, cached, active, pending, owner, slot, captured, prepared⟩,
    trans throughLock throughCache, ⟨cell, handle, rootLive, ownerInode.symm ▸ lockLive, separate, held⟩,
    rootAtEntry, lockAtEntry, emptyActive, emptyPending, worker⟩

/-- Reads preserve the selected files, logical image and authority of the held worker. -/
def observedOpenReadFrame (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (selectedPath : FilePath → Prop) (cache : HeldOpenCache heap)
    (observe : heap → CheckpointStorageObservation) (before after : heap) : Prop :=
  (observe before).Frames selectedPath (observe after) ∧
    (view.files after).image = (view.files before).image ∧
    (LiteralOpenAuthority view directory cache before → LiteralOpenAuthority view directory cache after)

theorem observedOpenReadFrame.refl (atHeap : heap) :
    observedOpenReadFrame view directory selectedPath cache observe atHeap atHeap :=
  ⟨.refl _ _, rfl, id⟩

theorem observedOpenReadFrame.trans
    (left : observedOpenReadFrame view directory selectedPath cache observe before middle)
    (right : observedOpenReadFrame view directory selectedPath cache observe middle after) :
    observedOpenReadFrame view directory selectedPath cache observe before after :=
  ⟨left.1.trans right.1, right.2.1.trans left.2.1, right.2.2 ∘ left.2.2⟩

theorem observedAdmissionFrame.entersReader
    (admissionFrame : observedAdmissionFrame view directory selectedPath observe visible entry cache.ready)
    (authority : LiteralOpenAuthority view directory cache cache.ready) :
    alignedReadFrame (fun atHeap => (observe atHeap).files.names) visible (managedPath directory)
      (observedOpenReadFrame view directory selectedPath cache observe) entry cache.ready :=
  ⟨admissionFrame.1, admissionFrame.2.1, admissionFrame.2.2, fun _ => authority⟩

abbrev literalOpenReadFrame (cache : HeldOpenCache heap)
    (observe : heap → CheckpointStorageObservation) (before after : heap) : Prop :=
  observedOpenReadFrame view dir current.state.selectedRetryPath cache observe before after

/-- Effects of the two actual reference allocations on the existing cache,
authority and crash footprint. The live-byte law follows the inode
named by the selected keeper at each call. -/
structure RawMarkedOpenInterpreter.LiteralAllocationEffects (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (cache : HeldOpenCache heap) (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (keeper : Nat) where
  allocatesPhase : ∀ {installed before ref after}, source.allocatePhase (.ready installed) before = .ok ref after →
    view.phase after ref = some (.ready installed) ∧
    CacheAllocationFrame view cache.directoryRef cache.activeRef cache.pendingRef before after ∧
    (observe before).Frames (managedPath directory) (observe after) ∧
    ∀ inode, (observe before).files.names (directory.file (.walSegment keeper)) = some inode →
      visible after inode = visible before inode
  allocatesToken : ∀ {before ref after}, source.allocateToken () before = .ok ref after →
    (∀ phase, view.phase after phase = view.phase before phase) ∧
    CacheAllocationFrame view cache.directoryRef cache.activeRef cache.pendingRef before after ∧
    (observe before).Frames (managedPath directory) (observe after) ∧
    ∀ inode, (observe before).files.names (directory.file (.walSegment keeper)) = some inode →
      visible after inode = visible before inode

variable (source) in
/-- The selected reader and installer share the same heap projections. -/
structure RawMarkedOpenInterpreter.LiteralOpenEffects
    (cache : HeldOpenCache heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) extends
    source.LiteralAllocationEffects view dir cache observe visible plan.layout.keeper.first where
  readEffects : source.AlignedReadEffects view dir cache.pendingRef (fun atHeap => (observe atHeap).files.names)
    visible namespaceView root (managedPath dir) (literalOpenReadFrame (current := current) (view := view) cache observe)
  child : ∀ start, plan.layout.first ≤ start →
    (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
      (observe reached).files.names ((dir).file (.walSegment start))

variable (source) in
/-- Local effects of retaining the reached keeper and syncing it after any
checked suffix removals. -/
structure RawMarkedOpenInterpreter.LiteralAlignedFinishEffects
    (cache : HeldOpenCache heap) (directory : DiskDirectory)
    {image : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout image history)
    (entry : heap) (observe : heap → CheckpointStorageObservation) where
  repairEffects : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
    (observe entry).files.names (directory.file (.walSegment layout.keeper.first)) = some inode →
    (keeperCalls).modifyPending cache.pendingRef (pushPending (directory.file (.walSegment layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
    AlignedRepairImageEffects view keeperCalls cache.handle keeper (directory.file (.walSegment layout.keeper.first))
      (fun before after => LiteralOpenAuthority view directory cache before → LiteralOpenAuthority view directory cache after)
  recordsKeeper : ∀ {path keeper before after}, (keeperCalls).modifyPending cache.pendingRef (pushPending path keeper)
    before = .ok () after → view.pending after cache.pendingRef = pushPending path keeper (view.pending before cache.pendingRef)
  readsRoot : ∀ {before result issued}, (keeperCalls).getDirectory cache.directoryRef before = .ok result issued →
    result = view.directory before cache.directoryRef ∧
    view.directory issued cache.directoryRef = view.directory before cache.directoryRef ∧
    view.pending issued cache.pendingRef = view.pending before cache.pendingRef
  syncKeepsCache : ∀ {issued after}, (keeperCalls).sync cache.handle issued = .ok () after →
    view.directory after cache.directoryRef = view.directory issued cache.directoryRef ∧
    view.pending after cache.pendingRef = view.pending issued cache.pendingRef ∧
    ReadSlotDrops view cache.handle issued after
  unlink : ∀ {ordinal before after result}, layout.range.through < ordinal →
    source.remove (directory.file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () →
    ((view.files after).image = (view.files before).image.unlinkLater ordinal ∧
      (LiteralOpenAuthority view directory cache before → LiteralOpenAuthority view directory cache after)) ∧
    view.directory after cache.directoryRef = view.directory before cache.directoryRef ∧
    view.pending after cache.pendingRef = view.pending before cache.pendingRef
  readsPending : ∀ {before entries loaded}, (keeperCalls).getPending cache.pendingRef before = .ok entries loaded →
    entries = view.pending before cache.pendingRef

variable (source) in
/-- The aligned finisher additionally interprets physical survivors and
descriptors needed by subsequent writes. -/
structure RawMarkedOpenInterpreter.ObservedAlignedRepairEffects
    (cache : HeldOpenCache heap) (directory : DiskDirectory) {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (entry : heap)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) extends
    source.LiteralAlignedFinishEffects (view := view) cache directory layout entry observe where
  syncStorage : ∀ (state : NativeReadyState), state.session.directory = directory → ∀ inode,
    AlignedRepairStorageEffects keeperCalls view state observe visible inode
  syncHandles : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
    (observe entry).files.names (directory.file (.walSegment layout.keeper.first)) = some inode →
    (keeperCalls).modifyPending cache.pendingRef (pushPending (directory.file (.walSegment layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
    AlignedRepairHandleEffects keeperCalls view (directory.file (.walSegment layout.keeper.first)) cache.handle keeper
  unlinkStorage : ∀ (state : NativeReadyState), state.session.directory = directory → ∀ (inode : Nat) {ordinal before after result},
    layout.range.through < ordinal →
    source.remove (directory.file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () →
    (observe before).files.names (directory.file (.walSegment layout.keeper.first)) = some inode →
    (observe before).Frames (fun path => state.crashPath path ∧ path ≠ directory.file (.walSegment ordinal)) (observe after) ∧
    visible after inode = visible before inode
  unlinkHandles : ∀ {keeper slot inode readHeap prepared}, attachedReadSlot view keeper slot inode readHeap →
    (observe entry).files.names (directory.file (.walSegment layout.keeper.first)) = some inode →
    (keeperCalls).modifyPending cache.pendingRef (pushPending (directory.file (.walSegment layout.keeper.first)) keeper)
      readHeap = .ok () prepared →
    ∀ {ordinal before after result}, layout.range.through < ordinal →
      source.remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      ReadSlotDrops view cache.handle before after ∧ ReadSlotDrops view keeper before after
  walNames : AlignedRepairWalNameEffects keeperCalls directory observe cache.directoryRef cache.pendingRef
    source.remove layout.range.through

abbrev RawMarkedOpenInterpreter.LiteralAlignedRepairEffects
    (cache : HeldOpenCache heap) (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :=
  source.ObservedAlignedRepairEffects (view := view) cache dir plan.layout reached observe visible

variable (source) in
/-- The actual aligned repair, rooted at the held reader's prepared heap. -/
structure RawMarkedOpenInterpreter.LiteralAlignedSyncs
    (directory : DiskDirectory) {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (cache : HeldOpenCache heap)
    (view : OpenCloseHeapView heap FileImage) (observe : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (readScope : FilePath → Prop) (entry repaired : heap) where
  keeper : IO.FS.Handle
  slot : DescriptorSlot
  inode : Nat
  readHeap : heap
  prepared : heap
  rootIssued : heap
  authorized : heap
  keeperEntry : heap
  loaded : heap
  consumed : heap
  entries : List (FilePath × IO.FS.Handle)
  newer : List Nat
  named : (observe entry).files.names (directory.file (.walSegment layout.keeper.first)) = some inode
  attached : attachedReadSlot view keeper slot inode readHeap
  remembered : (keeperCalls).modifyPending cache.pendingRef
    (pushPending (directory.file (.walSegment layout.keeper.first)) keeper) readHeap = .ok () prepared
  holding : LiteralOpenAuthority view directory cache prepared
  liveFrame : (⟨(observe entry).files.names, fun inode => [visible entry inode]⟩ : CheckpointSurvivingFiles).Frames
    (managedPath directory) ⟨(observe prepared).files.names, fun inode => [visible prepared inode]⟩
  storageFrame : (observe entry).Frames readScope (observe prepared)
  privateKeeper : ∀ path, managedPath directory path →
    (observe prepared).files.names path = some inode → path = directory.file (.walSegment layout.keeper.first)
  scanned : ∀ start, start ∈ newer ↔ layout.range.through < start ∧
    ∃ object, namespaceView.child root (renderWalSegmentName start) = some object
  getRoot : (keeperCalls).getDirectory cache.directoryRef prepared = .ok (some cache.handle) rootIssued
  syncRoot : (keeperCalls).sync cache.handle rootIssued = .ok () authorized
  pruned :
    let plan : Plan := ⟨layout.range.through, layout.keeper.first, newer, layout.keeper.bytes⟩
    if newer = [] then keeperEntry = authorized else ∃ (unlinked suffixIssued : heap),
      ((newer.map Step.unlink).forM (performPaths directory plan source.remove throw
        (source.stage.stage cache.pendingRef (keeperCalls).modifyPending)
        ((keeperCalls).syncPaths directory.path cache.directoryRef cache.activeRef cache.pendingRef) source.rename))
        authorized = .ok () unlinked ∧
      (keeperCalls).getDirectory cache.directoryRef unlinked = .ok (some cache.handle) suffixIssued ∧
      (keeperCalls).sync cache.handle suffixIssued = .ok () keeperEntry
  getPending : (keeperCalls).getPending cache.pendingRef keeperEntry = .ok entries loaded
  found : entries.find? (fun item => item.1 == directory.file (.walSegment layout.keeper.first)) =
    some (directory.file (.walSegment layout.keeper.first), keeper)
  clear : (keeperCalls).setPending cache.pendingRef
    (entries.filter (fun item => item.1 != directory.file (.walSegment layout.keeper.first))) loaded = .ok () consumed
  syncKeeper : (keeperCalls).sync keeper consumed = .ok () repaired

/-- Interpret storage at the repair already witnessed by the literal return.
The scan must cover every physical later WAL name at entry. Accepted
unlinks may also cover names that were already absent. -/
theorem RawMarkedOpenInterpreter.LiteralAlignedSyncs.readyStorage
    {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} {cache : HeldOpenCache heap}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {namespaceView : DirectoryReadNamespace} {root : DeviceInode} {readScope : FilePath → Prop} {entry repaired : heap}
    (seen : source.LiteralAlignedSyncs directory layout cache view observe visible namespaceView root readScope entry repaired)
    {state : NativeReadyState} (valid : state.Valid)
    (directoryEq : state.session.directory = directory) (slotEq : state.directorySlot = cache.rootSlot)
    (censusEq : state.census = view.descriptors repaired)
    (keeperStart : state.writer.wal.active.first = layout.keeper.first)
    (after : LiteralOpenAuthority view directory cache repaired)
    (effects : source.ObservedAlignedRepairEffects (view := view) cache directory layout entry observe visible)
    (protectedFiles : NativeReadyProtectedStorage state (observe seen.prepared).files)
    (marker : (observe seen.prepared).files.Stored (directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe seen.prepared).crashNames,
      names directory.path = (observe seen.prepared).files.names directory.path)
    (keeperBytes : visible entry seen.inode = state.writer.wal.active.bytes)
    {lower : Nat}
    (window : state.writer.wal.NamespaceWindow directory lower layout.range.through (observe entry).files.names)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ layout.range.through)
    (laterComplete : ∀ start, layout.range.through < start →
      (∃ inode, (observe entry).files.names (directory.file (.walSegment start)) = some inode) →
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object) :
    NativeReadyStorage state (observe repaired) ∧
    (∀ inode, (observe repaired).files.names (directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible repaired inode = state.writer.wal.active.bytes) ∧
    (observe repaired).files.names (directory.file (.walSegment state.writer.wal.active.first)) = some seen.inode ∧
    ∀ through, state.writer.wal.SettledNamespaceWindow directory lower through (observe repaired) := by
  subst directory
  let directory := state.session.directory
  let plan : Plan := ⟨layout.range.through, layout.keeper.first, seen.newer, layout.keeper.bytes⟩
  have heldRoot : attachedReadSlot view cache.handle state.directorySlot (state.census.inode state.directorySlot.description)
      seen.prepared := by
    rw [slotEq, censusEq, after.rootAttached.2.2]
    exact seen.holding.rootAttached
  have noAlias (path : FilePath) (selected : state.selectedRetryPath path) :
      (observe seen.prepared).files.names path ≠ some seen.inode := by
    have inside := selectedRetryManagedPath selected
    intro equal
    have alias := seen.privateKeeper path inside equal
    apply NativeReadyState.protectedPathNeWalFromActive valid selected (Nat.le_of_eq keeperStart)
    exact alias
  have received (start : Nat) :
      (observe seen.prepared).files.names (directory.file (.walSegment start)) =
        (observe entry).files.names (directory.file (.walSegment start)) :=
    (seen.liveFrame _ (.inr ⟨.walSegment start, rfl⟩)).1
  have bound := (received layout.keeper.first).trans seen.named
  have bytes := (List.cons.inj ((seen.liveFrame _ (.inr ⟨.walSegment layout.keeper.first, rfl⟩)).2 _ seen.named)).1
  have listed (start : Nat) (beyond : plan.through < start) :
      ((observe seen.prepared).files.names (directory.file (.walSegment start))).isSome = true → start ∈ plan.newer := by
    rw [received, Option.isSome_iff_exists]
    exact fun present => (seen.scanned start).mpr ⟨beyond, laterComplete start beyond present⟩
  have later (ordinal : Nat) (member : ordinal ∈ plan.newer) := ((seen.scanned ordinal).mp member).1
  have handles := effects.syncHandles seen.attached seen.named seen.remembered
  have dropRoot {issued reached : heap} (synced : (keeperCalls).sync cache.handle issued = .ok () reached) :=
    (effects.syncKeepsCache synced).2.2
  exact (effects.syncStorage state rfl seen.inode).readyAfterAlignedRepair plan source.remove
    (source.stage.stage cache.pendingRef (keeperCalls).modifyPending) source.rename valid
    (by simpa only [keeperStart] using handles) heldRoot seen.attached (by simpa only [keeperStart] using seen.remembered)
    dropRoot (fun member removed accepted =>
      effects.unlinkHandles seen.attached seen.named seen.remembered (later _ member) removed accepted)
    (fun member removed accepted name =>
      effects.unlinkStorage state rfl seen.inode (later _ member) removed accepted (keeperStart ▸ name))
    seen.getRoot seen.syncRoot seen.pruned seen.getPending (by simpa only [keeperStart] using seen.found)
    (by simpa only [keeperStart] using seen.clear) seen.syncKeeper protectedFiles marker rootSettled
    (by simpa only [keeperStart] using bound) (bytes.trans keeperBytes) noAlias
    (window.frame (fun start _ _ => congrArg Option.isSome (received start))) bounded
    (fun ordinal member => Nat.lt_of_le_of_lt (keeperStart.symm ▸ layout.target.firstCovered) (later ordinal member))
    later listed effects.walNames

/-- An aligned installation ties a valid writer and the live references
and descriptor projections to the actual returned table. -/
abbrev RawMarkedOpenInterpreter.LiteralAlignedReturn
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory)
    {image : FileImage} {history : List WAL.Write} (layout : CanonicalKeeperLayout image history)
    (published : CheckpointPublication.Image) (checkpoint : Option (PackedTable × UInt64))
    (wal : WalSegmentImage) (cache : HeldOpenCache heap) (view : OpenCloseHeapView heap FileImage)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    {repaired : heap} (writer : SegmentedWriterState)
    (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired)
    (returnedAt : heap) (table : DiskTable) : Prop :=
    let files := RawMarkedOpenInterpreter.makeCache directory cache.directoryRef cache.activeRef cache.pendingRef
    let state := allocation.readyState writer directory cache.owner cache.rootSlot
      cache.directoryRef cache.activeRef cache.pendingRef phaseIdentity tokenIdentity
    state.Valid ∧ LiteralOpenAuthority view directory cache repaired ∧ writer.history = history ∧ writer.checkpoint = checkpoint ∧
    writer.target = layout.target ∧ writer.published.durable = published.durable ∧
    writer.wal = {wal with directory := (view.files repaired).image.directory} ∧
    table = RawMarkedOpenInterpreter.assemble directory cache.lock files allocation.phase allocation.token ∧
    table.UsesOpenReferences directory cache.lock files allocation.phase allocation.token ∧
    allocation.afterToken = returnedAt ∧ view.phase returnedAt allocation.phase = some (.ready writer.installed) ∧
    view.files returnedAt = state.files ∧ view.descriptors returnedAt = state.census ∧
    view.cacheAt returnedAt cache.directoryRef cache.activeRef cache.pendingRef = state.cache ∧
    attachedReadSlot view cache.lock state.owner (state.census.inode state.owner.description) returnedAt ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok writer.installed.table

/-- The same literal worker that supplies the selected replay runs the
aligned repair and installs that writer into the returned table. The
physical fsync observations establish the logical file image. -/
theorem RawMarkedOpenInterpreter.retainsLiteralAlignedReturn
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory)
    {image : FileImage} {history : List WAL.Write} {published : CheckpointPublication.Image}
    (layout : CanonicalKeeperLayout image history) {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable image.directory.active.manifest checkpoint)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (walPair : wal.directory.active = layout.target.pair) (keeper : layout.keeper.first = wal.active.first)
    (aligned : layout.tail = .empty)
    (cache : HeldOpenCache heap) (authority : LiteralOpenAuthority view directory cache cache.ready)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (selectedPath : FilePath → Prop)
    {entry returnedAt : heap} {table : DiskTable}
    (opened : source.LiteralMarkedReturn directory layout checkpoint cache.lock cache.directoryRef cache.activeRef cache.pendingRef
      cache.ready view (fun atHeap => (observe atHeap).files.names) visible namespaceView root (managedPath directory)
      (observedOpenReadFrame view directory selectedPath cache observe) entry returnedAt table)
    (selectedPair : (view.files entry).image.directory.active = layout.target.pair)
    (selectedKeeper : (view.files entry).image.keeper.active = some layout.target.trimmed)
    (kept : (view.files entry).image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    (suffixNames : ∀ ordinal ∈ (view.files entry).image.later.visible, layout.range.through < ordinal ∧
      ∃ object, namespaceView.child root (renderWalSegmentName ordinal) = some object)
    (effects : source.LiteralAlignedFinishEffects (view := view) cache directory layout entry observe)
    (allocates : source.LiteralAllocationEffects view directory cache observe visible layout.keeper.first)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat) :
    ∃ (repaired : heap) (writer : SegmentedWriterState)
      (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired),
      source.LiteralAlignedReturn directory layout published checkpoint wal cache view
        phaseIdentity tokenIdentity writer allocation returnedAt table ∧
      Nonempty (source.LiteralAlignedSyncs directory layout cache view observe visible namespaceView root selectedPath entry repaired) := by
  let files := RawMarkedOpenInterpreter.makeCache directory cache.directoryRef cache.activeRef cache.pendingRef
  obtain ⟨count, markerBytes, patched, logical, file, slot, inode, readHeap, prepared, repaired, extent, newer,
    phase, afterPhase, token, markerName, decoded, _, replayed, named, attached, route, extentEq, laterNames,
    liveFrame, privateKeeper, readFrame, cacheFrame, rawFinish, phaseReturn, tokenReturn, actualTable, _⟩ := opened
  let calls := source.keeperCallbacks.withFileReads source.fileCalls
  let stage := source.stage.stage cache.pendingRef calls.modifyPending
  let plan : Plan := ⟨layout.range.through, layout.keeper.first, newer, layout.keeper.bytes⟩
  have extentExact : extent = layout.keeper.bytes.size := by simpa [aligned] using extentEq
  have remembered := route.resolve_right (fun released => Nat.lt_irrefl _ (extentExact ▸ released.1))
  have preparedAuthority := cacheFrame.2.2 authority
  have later (ordinal : Nat) (member : ordinal ∈ newer) := ((laterNames ordinal).mp member).1
  have suffix : calls.SuffixCacheEffects view directory plan cache.directoryRef cache.pendingRef cache.handle source.remove :=
    ⟨effects.readsRoot, fun synced => (effects.syncKeepsCache synced).1,
      fun member removed accepted => (effects.unlink (later _ member) removed accepted).2⟩
  rw [extentExact] at rawFinish
  obtain ⟨ready, sealed, repairFrame, rootIssued, authorized, keeperEntry, entries, loaded, consumed,
    getRoot, syncRoot, pruned, getPending, found, clear, syncKeeper⟩ :=
    (effects.repairEffects attached named remembered.2).readyAfterReturn plan layout.target.trimmedSize calls
      cache.directoryRef cache.activeRef cache.pendingRef source.remove stage source.rename
      (before := entry)
      (keeps := fun before after => LiteralOpenAuthority view directory cache before →
        LiteralOpenAuthority view directory cache after)
      (fun first second => second ∘ first) preparedAuthority.directoryCell remembered.2
      effects.recordsKeeper (fun loaded => ⟨(effects.readsRoot loaded).1, (effects.readsRoot loaded).2.2⟩)
      (fun synced => (effects.syncKeepsCache synced).2.1) effects.readsPending (fun _ => suffix)
      (fun member removed accepted => (effects.unlink (later _ member) removed accepted).1) rawFinish readFrame.2.1
      selectedKeeper (fun ordinal member => (laterNames ordinal).mpr (suffixNames ordinal member)) selectedPair
  have repairedAuthority := repairFrame preparedAuthority
  obtain ⟨retained, recovered, _, _⟩ := layout.retainedFromActualReplay selected accepted ordered markerName decoded rfl
    replayed walLayout walValid spans walPair keeper ready (sealed.trans kept) repairedAuthority.owned
  obtain ⟨phaseInitialized, phaseCache, _, _⟩ := allocates.allocatesPhase phaseReturn
  obtain ⟨tokenKeepsPhase, tokenCache, _, _⟩ := allocates.allocatesToken tokenReturn
  let installed := Reopened.installed ⟨logical, (checkpoint.getD (.empty, 0)).2, count, layout.keeper.first⟩
  let writer := SegmentedWriterState.ofReopen installed wal history published layout.target checkpoint (view.files repaired)
  let allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired :=
    ⟨phase, token, afterPhase, returnedAt, phaseReturn, phaseInitialized, tokenReturn, tokenKeepsPhase phase⟩
  let state := allocation.readyState writer directory cache.owner cache.rootSlot
    cache.directoryRef cache.activeRef cache.pendingRef phaseIdentity tokenIdentity
  have cached : state.cache.directory = some (cache.captured, cache.rootSlot, 0) :=
    repairedAuthority.cacheRoot.1
  obtain ⟨usesCache, atDirectory⟩ := RawMarkedOpenInterpreter.cacheReferences directory
    cache.directoryRef cache.activeRef cache.pendingRef
  let refs : OpenSyncCacheRefs files directory.path :=
    ⟨cache.directoryRef, cache.activeRef, cache.pendingRef, usesCache, atDirectory⟩
  obtain ⟨valid, _, used, initialized, sameFiles, census, sameCache, owner⟩ :=
    allocation.installsReadyState writer directory cache.owner cache.rootSlot
      (RawMarkedOpenInterpreter.assembles directory cache.lock files) refs phaseIdentity tokenIdentity
      rfl retained rfl repairedAuthority.ownerAttached.1 repairedAuthority.ownerAttached.2.1 repairedAuthority.rootAttached.2.1
      ⟨_, cached⟩
      ⟨phaseCache.files, phaseCache.census, phaseCache.cache, congrArg (fun handle => handle.2.1) (phaseCache.handles _)⟩
      ⟨tokenCache.files, tokenCache.census, tokenCache.cache, congrArg (fun handle => handle.2.1) (tokenCache.handles _)⟩
  have held : attachedReadSlot view cache.lock state.owner (state.census.inode state.owner.description) returnedAt :=
    ⟨owner, census.symm ▸ valid.ownerLive, congrFun (congrArg DescriptorInventory.inode census) _⟩
  exact ⟨repaired, writer, allocation,
    ⟨valid, repairedAuthority, rfl, rfl, rfl, rfl, rfl, actualTable, actualTable.symm ▸ used, rfl,
      initialized, sameFiles, census, sameCache, held, recovered⟩,
    ⟨file, slot, inode, readHeap, prepared, rootIssued, authorized, keeperEntry, loaded, consumed, entries, newer,
      named, attached, remembered.2, preparedAuthority, liveFrame, readFrame.1,
      (fun path inside => privateKeeper path inside inside), laterNames,
      getRoot, syncRoot, pruned, getPending, found, clear, syncKeeper⟩⟩

variable (source) in
/-- Callback laws specific to the executed keeper replacement. Reads of
the selected WAL and the returned table's allocations remain shared
with a repair that retains the existing keeper. -/
structure RawMarkedOpenInterpreter.LiteralKeeperReplacementEffects
    (cache : HeldOpenCache heap)
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) where
  buffered : heap → IO.FS.Handle → ByteArray
  image : ∀ newer, (∀ ordinal ∈ newer, plan.layout.range.through < ordinal) →
      Alvoki.Storage.DiskSession.LiteralKeeperReplacementEffects view dir
        ⟨plan.layout.range.through, plan.layout.keeper.first, newer, plan.layout.keeper.bytes⟩
        plan.layout.target source.remove (source.stage.stage cache.pendingRef (keeperCalls).modifyPending)
        ((keeperCalls).syncPaths (dir).path cache.directoryRef cache.activeRef cache.pendingRef) source.rename
        (fun before after => LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)
  storage : ∀ state : NativeReadyState, state.session.directory = dir →
      source.stage.ReplacementStorageEffects keeperCalls state view observe visible buffered
        cache.directoryRef cache.pendingRef cache.handle source.rename
  unlinks : ∀ state : NativeReadyState, state.session.directory = dir → ∀ {ordinal before after result},
      ¬ state.crashPath ((dir).file (.walSegment ordinal)) →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (observe before).Frames (fun path => state.crashPath path ∧ path ≠ (dir).file (.walSegment ordinal)) (observe after) ∧
      (CachedKeeperReplacementRoot state view cache.directoryRef cache.handle before →
        CachedKeeperReplacementRoot state view cache.directoryRef cache.handle after)
  records : ∀ {file before after},
      (keeperCalls).modifyPending cache.pendingRef (pushPending ((dir).file .stagedWal) file) before = .ok () after →
      view.pending after cache.pendingRef = pushPending ((dir).file .stagedWal) file (view.pending before cache.pendingRef)
  readsPending : ∀ {before entries loaded}, (keeperCalls).getPending cache.pendingRef before = .ok entries loaded →
      entries = view.pending before cache.pendingRef
  readsRoot : ∀ {before result issued}, (keeperCalls).getDirectory cache.directoryRef before = .ok result issued →
      result = view.directory before cache.directoryRef

  unlinkNames : ∀ {ordinal before after result}, plan.layout.range.through < ordinal →
    source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () →
    (observe after).files.names ((dir).file (.walSegment ordinal)) = none ∧
    ∀ start, start ≠ ordinal →
      (observe after).files.names ((dir).file (.walSegment start)) =
        (observe before).files.names ((dir).file (.walSegment start))

private theorem tailSizeOfTrimmedBytes {boundedBytes tail trimmed : ByteArray}
    (bounded : boundedBytes = trimmed) (live : trimmed = boundedBytes ++ tail) : tail.size ≤ 0 := by
  have lengths := congrArg ByteArray.size live
  rw [ByteArray.size_append, bounded] at lengths
  omega

/-- Interpret one literal marked open. Its reached keeper extent picks
a local physical repair. Each repair delivers the same selected
history, next write entry, and canonical WAL namespace. -/
theorem NativeReadPosition.SelectedWritePlan.returnsLiteralRepairedWriter
    (plan : current.SelectedWritePlan batch target (view.files reached).image)
    (cache : HeldOpenCache heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (request : WriteRequest) (cause : IO.Error)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (shared : source.LiteralOpenEffects cache namespaceView root plan observe visible)
    (aligns : plan.layout.tail.size = 0 → source.LiteralAlignedRepairEffects cache plan observe visible)
    (admissionFrame : alignedAdmissionFrame view current.state observe visible reached cache.ready)
    (authority : LiteralOpenAuthority view dir cache cache.ready)
    (rootNamed : (observe reached).files.names (dir).path = some (cache.captured.inode cache.rootSlot.description))
    (lockNamed : (observe reached).files.names ((dir).file .lock) = some (cache.captured.inode cache.owner.description))
    (entry : RawOpenRetryTrace.SelectedEntry view current.state target
      (fun atHeap => (observe atHeap).files.names) visible reached)
    (physical : plan.layout.VisibleWal dir (observe reached).files.names (visible reached))
    {firstOffset : Nat}
    (covers : ∀ start ∈ current.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ start)
    (window : current.state.writer.wal.NamespaceWindow dir firstOffset target.range.through (observe reached).files.names)
    (replaces : 0 < plan.layout.tail.size → source.LiteralKeeperReplacementEffects cache plan observe visible)
    (suffixAtEntry : RawOpenRetryTrace.LaterWalAt view dir target (fun atHeap => (observe atHeap).files.names) reached)
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
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) ∧
      start.current.ready.state.session.directory = dir ∧
      (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
      (∀ {inode}, (observe reached).files.names ((dir).file (.walSegment target.first)) = some inode →
        visible reached inode = target.trimmed →
        (observe start.reached).files.names ((dir).file (.walSegment target.first)) = some inode ∧
          visible start.reached inode = target.trimmed) ∧
      ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
        start.current.ready.state.session.directory firstOffset through (observe start.reached) := by
  have untilHeld := admissionFrame.entersReader authority
  have manifest := (congrArg (fun target : Target => target.pair.manifest) plan.targetEq).trans entry.manifest
  have childLater (start : Nat) (later : plan.layout.range.through < start) :=
    shared.child start (Nat.le_trans plan.layout.covers
      (Nat.le_trans (DirectoryPublication.Bindings.walRange_accounting plan.layout.decoded).2.1 (Nat.le_of_lt later)))
  obtain ⟨⟨count, markerBytes, patched, logical, keeper, slot, inode, readHeap, prepared, repaired, extent, newer,
    phase, afterPhase, token, markerName, decoded, _, replay, named, attached, route, extentEq, laterNames, liveFrame,
    privateKeeper, readFrame, cacheFrame, rawFinish, phaseReturn, tokenReturn, tableEq, _⟩, _⟩ :=
    source.readsLiteralMarkedOpen dir plan.layout plan.selected
      cache.lock cache.directoryRef cache.activeRef cache.pendingRef cache.ready
      (fun atHeap => (observe atHeap).files.names) visible namespaceView root
      (managedPath dir) observedOpenReadFrame.refl observedOpenReadFrame.trans untilHeld shared.readEffects
      (manifest.symm ▸ entry.protectedFiles.manifest)
      (fun bytes metadata named decoded index within payload stored =>
        entry.protectedFiles.runs bytes metadata (manifest.symm.trans named) decoded index within payload stored)
      (fun _ selected => entry.markerStored selected)
      (.inr ⟨.manifest, rfl⟩)
      (fun _ metadata _ _ index _ => .inr ⟨.run metadata.header.generation index, rfl⟩)
      (.inr ⟨.walBoundary, rfl⟩) plan.modeledWindow.2 (fun first _ _ => .inr ⟨.walSegment first, rfl⟩)
      (fun start lower _ => shared.child start lower)
      (fun _ fromEntry =>
        source.fileCalls.absenceOnFromNamePresence dir (fun atHeap => (observe atHeap).files.names) visible namespaceView root
          (managedPath dir) fromEntry (fun path before => (shared.readEffects.statFrame path before).1)
          shared.readEffects.statMissing (fun start _ => .inr ⟨.walSegment start, rfl⟩)
          (fun start later => by
            rw [← childLater start later, Option.isSome_map, Option.isSome_iff_exists]))
      physical workerReturn
  have cutoff : plan.layout.range.through = target.range.through :=
    congrArg (fun t : Target => t.range.through) plan.targetEq
  have sameSuffix := suffixAtEntry.scanNames namespaceView root (by simpa only [cutoff] using laterNames)
    (fun start later => childLater start (cutoff.symm ▸ later))
  obtain ⟨selectedNames, boundedStarts, later, listed⟩ := plan.walNamespaceAtPreparation (cutoff.symm ▸ window)
    (fun start => (liveFrame _ (.inr ⟨.walSegment start, rfl⟩)).1) namespaceView root childLater laterNames
  let repairPlan : Plan := ⟨plan.layout.range.through, plan.layout.keeper.first, newer, plan.layout.keeper.bytes⟩
  let stageWrite := source.stage.stage cache.pendingRef (keeperCalls).modifyPending
  let group := (keeperCalls).syncPaths (dir).path cache.directoryRef cache.activeRef cache.pendingRef
  have preparedAuthority := cacheFrame.2.2 authority
  let installed := Reopened.installed ⟨logical, (current.state.writer.checkpoint.getD (.empty, 0)).2, count,
    plan.layout.keeper.first⟩
  let wal := current.state.writer.wal.appendSelectedView (view.files reached).image.directory.active plan.history
  let writer := SegmentedWriterState.ofReopen installed wal plan.history current.state.writer.published
    plan.layout.target current.state.writer.checkpoint (view.files repaired)
  have keeperEq : writer.wal.active = plan.layout.keeper := plan.keeper.symm
  have keeperPathEq : (dir).file (.walSegment writer.wal.active.first) =
      (dir).file (.walSegment plan.layout.keeper.first) := congrArg (fun item : WalSegment => (dir).file (.walSegment item.first)) keeperEq
  have toTargetFirst := congrArg Target.first plan.targetEq
  change plan.layout.keeper.first = target.first at toTargetFirst
  have toTargetBytes := congrArg Target.trimmed plan.targetEq
  change plan.layout.keeper.bytes = target.trimmed at toTargetBytes
  let files := RawMarkedOpenInterpreter.makeCache dir cache.directoryRef cache.activeRef cache.pendingRef
  obtain ⟨uses, atDir⟩ := RawMarkedOpenInterpreter.cacheReferences dir cache.directoryRef cache.activeRef cache.pendingRef
  let refs : OpenSyncCacheRefs files (dir).path := ⟨cache.directoryRef, cache.activeRef, cache.pendingRef, uses, atDir⟩
  obtain ⟨initialized, phaseCache, phaseStorage, phaseVisible⟩ := shared.allocatesPhase phaseReturn
  obtain ⟨keepsPhase, tokenCache, tokenStorage, tokenVisible⟩ := shared.allocatesToken tokenReturn
  let allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase writer.installed repaired :=
    ⟨phase, token, afterPhase, returnedAt, phaseReturn, initialized, tokenReturn, keepsPhase phase⟩
  let state := allocation.readyState writer dir cache.owner cache.rootSlot refs.directory refs.active refs.pending
    phaseIdentity tokenIdentity
  have protectedRoot : current.state.selectedRetryPath (dir).path := .inr (.inl rfl)
  have protectedLock : current.state.selectedRetryPath ((dir).file .lock) := .inr (.inr (.inl rfl))
  have atRoot (after : LiteralOpenAuthority view dir cache repaired) :=
    (readFrame.1.visible _ protectedRoot).1.trans (rootNamed.trans (congrArg some after.rootAttached.2.2.symm))
  have atLock (after : LiteralOpenAuthority view dir cache repaired) :=
    (readFrame.1.visible _ protectedLock).1.trans (lockNamed.trans (congrArg some after.ownerAttached.2.2.symm))
  have preparedDurability := durable.frame readFrame.1.visible
    (readFrame.1.weaken (fun _ same => same.symm ▸ protectedRoot))
  have exactReturn : source.openTable input reached =
      .ok (RawMarkedOpenInterpreter.assemble dir cache.lock files allocation.phase allocation.token) allocation.afterToken :=
    returned.trans (congrArg (fun value => EStateM.Result.ok value returnedAt) tableEq)
  by_cases tail : 0 < plan.layout.tail.size
  · have longer : plan.layout.keeper.bytes.size < extent := by
      rw [extentEq, ByteArray.size_append]
      omega
    let replacement := replaces tail
    obtain ⟨retained, repairFrame⟩ :=
      plan.retainsLiteralLongerRepair newer source.remove stageWrite group source.rename
        (keeps := fun before after => LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)
        (fun first second => second ∘ first) (replacement.image newer later) longer rawFinish readFrame.2.1
        (fun start present => (sameSuffix start).mpr present) entry.kept preparedAuthority.owned
        (fun kept _ => (kept preparedAuthority).owned) markerName decoded replay
    have repairedAuthority := repairFrame preparedAuthority
    have valid : state.Valid := ⟨rfl, rfl, repairedAuthority.ownerAttached.2.1, repairedAuthority.rootAttached.2.1,
      ⟨cache.captured, repairedAuthority.cacheRoot.1⟩, retained⟩
    have kept := retained.sealedFiles.trans current.readPrefix.refines.1.retained.sealedFiles.symm
    obtain ⟨protectedFiles, markerStorage, rootSettled⟩ :=
      preparedDurability.forReopenedWriter current.readPrefix.refines.1 valid rfl plan.targetEq entry.manifest rfl kept (atRoot repairedAuthority) (atLock repairedAuthority)
    have oldNamed : (observe prepared).files.names ((dir).file (.walSegment repairPlan.keeper)) = some inode :=
      (liveFrame _ (.inr ⟨.walSegment repairPlan.keeper, rfl⟩)).1.trans named
    have laterOutside {ordinal : Nat} (member : ordinal ∈ repairPlan.newer) (path : FilePath)
        (inside : state.crashPath path) : path ≠ (dir).file (.walSegment ordinal) := by
      have afterKeeper : writer.wal.active.first < ordinal := by
        rw [keeperEq]
        exact Nat.lt_of_le_of_lt plan.layout.target.firstCovered (later ordinal member)
      rcases NativeReadyState.crashPath_iff_write.mp inside with mark | keep | immutable
      · exact state.protectedPathNeWalFromActive valid (.inl mark) (Nat.le_of_lt afterKeeper)
      · rw [keep]
        exact fun same => (Nat.ne_of_lt afterKeeper) ((dir).walSegment_path_injective same)
      · exact state.protectedPathNeWalFromActive valid (.inr immutable) (Nat.le_of_lt afterKeeper)
    have size : repairPlan.keeperBytes.size = repairPlan.keeperSize := plan.layout.target.trimmedSize
    have prefixBytes : repairPlan.keeperBytes.extract 0 repairPlan.keeperSize = state.writer.wal.active.bytes := by
      rw [← size, ByteArray.extract_zero_size]
      change plan.layout.keeper.bytes = writer.wal.active.bytes
      rw [keeperEq]
    obtain ⟨replacementInode, _, settled, replacementNamed, _, _, replacementBytes, repairedWindow⟩ :=
      source.stage.readyStorageOfFinishedReplacement keeperCalls state view observe visible replacement.buffered
        cache.directoryRef cache.activeRef cache.pendingRef source.remove source.rename cache.handle (replacement.storage state rfl)
        repairPlan extent (size ▸ longer) (congrArg WalSegment.first keeperEq.symm) prefixBytes
        ⟨preparedAuthority.directoryCell, repairedAuthority.rootAttached.2.2.symm ▸ preparedAuthority.rootAttached⟩
        protectedFiles oldNamed markerStorage rootSettled
        (fun ordinal member inside => laterOutside member ((dir).file (.walSegment ordinal)) inside rfl)
        (by
          intro ordinal before after result outside removed accepted
          obtain ⟨frame, rootFrame⟩ := replacement.unlinks state rfl outside removed accepted
          exact ⟨frame.weaken (fun path inside => ⟨inside, fun same => outside (same ▸ inside)⟩), rootFrame⟩)
        replacement.records replacement.readsPending replacement.readsRoot rawFinish
    have live (other : Nat)
        (namedAfter : (observe repaired).files.names ((dir).file (.walSegment writer.wal.active.first)) = some other) :
        visible repaired other = writer.wal.active.bytes := by
      rw [keeperEq] at namedAfter
      have same := Option.some.inj (namedAfter.symm.trans replacementNamed)
      exact same.symm ▸ replacementBytes
    obtain ⟨handle, start, nextCache, keptBatch, opened, history, ledger, replay, nextStorage, stateEq, afterToken⟩ :=
      plan.installsLiteralRepairedWriter (allocation := allocation) (cache := refs) request cause
        (RawMarkedOpenInterpreter.assembles dir cache.lock files) valid rfl repairedAuthority.ownerAttached.1 phaseCache tokenCache
        ⟨cache.captured, repairedAuthority.cacheRoot⟩ phaseEffects tokenEqual exactReturn observe visible settled live
        (phaseStorage.weaken fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected)
        (tokenStorage.weaken fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected)
        (fun other named => phaseVisible other (by simpa only [keeperEq] using named))
        (fun other named => tokenVisible other (by simpa only [keeperEq] using named))
    have sameDirectory : start.current.ready.state.session.directory = state.session.directory :=
      congrArg (fun next : NativeReadyState => next.session.directory) stateEq
    have lowerBound : ∀ offset ∈ state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset := by
      change ∀ start ∈ wal.segments.map WalSegment.first, firstOffset ≤ start
      simpa only [wal, WalSegmentImage.appendSelectedView_starts] using covers
    have names (through : Nat) :
        state.writer.wal.SettledNamespaceWindow dir firstOffset through (observe allocation.afterToken) := by
      have window := repairedWindow selectedNames boundedStarts later listed replacement.unlinkNames through
      exact allocation.walWindowAfterAllocations observe state.writer.wal dir window.1 window.2
        (fun _ => WalNamePresenceFrame.ofStorageFrame phaseStorage (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
        (fun _ => WalNamePresenceFrame.ofStorageFrame tokenStorage (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
    refine ⟨handle, start, nextCache, keptBatch, opened, history, ledger, replay, nextStorage, sameDirectory,
      stateEq.symm ▸ lowerBound, ?_, stateEq.symm ▸ afterToken.symm ▸ names⟩
    -- A marker-aligned live keeper cannot select the replacement branch.
    intro existing namedAtEntry bytesAtEntry
    have found := physical.keeper
    change ((observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first))).map (visible reached) =
      some (plan.layout.keeper.bytes ++ plan.layout.tail) at found
    rw [toTargetFirst, namedAtEntry, Option.map_some, bytesAtEntry] at found
    exact (Nat.not_lt_of_ge (tailSizeOfTrimmedBytes toTargetBytes (Option.some.inj found)) tail).elim
  · have emptySize : plan.layout.tail.size = 0 := by omega
    let effects := aligns emptySize
    have emptyTail : plan.layout.tail = .empty := ByteArray.size_eq_zero_iff.mp emptySize
    have alignedBytes : plan.layout.keeper.bytes ++ plan.layout.tail = plan.layout.keeper.bytes := by
      rw [emptyTail, ByteArray.append_empty]
    have size : extent = plan.layout.keeper.bytes.size := extentEq.trans (congrArg ByteArray.size alignedBytes)
    have exactKeeper : (view.files reached).image.keeper.active = some target.trimmed :=
      plan.layout.visible.trans (congrArg some (alignedBytes.trans (congrArg Target.trimmed plan.targetEq)))
    have cacheEffects : (keeperCalls).SuffixCacheEffects view dir repairPlan cache.directoryRef cache.pendingRef
        cache.handle source.remove :=
      ⟨effects.readsRoot, fun synced => (effects.syncKeepsCache synced).1,
        fun member removed accepted => (effects.unlink (later _ member) removed accepted).2⟩
    have remembered := route.resolve_right (fun released => Nat.lt_irrefl _ (size ▸ released.1))
    have finish := rawFinish
    rw [size] at finish
    obtain ⟨ready, sealed, repairFrame, rootIssued, afterDirectory, keeperEntry, entries, loaded, consumed,
      getRoot, syncRoot, pruned, getPending, findKeeper, clear, syncKeeper⟩ :=
      (effects.repairEffects attached named remembered.2).readyAfterReturn repairPlan plan.layout.target.trimmedSize
        keeperCalls cache.directoryRef cache.activeRef cache.pendingRef source.remove stageWrite source.rename
        (before := reached)
        (keeps := fun before after => LiteralOpenAuthority view dir cache before → LiteralOpenAuthority view dir cache after)
        (fun first second => second ∘ first) preparedAuthority.directoryCell remembered.2 effects.recordsKeeper
        (fun loaded => ⟨(effects.readsRoot loaded).1, (effects.readsRoot loaded).2.2⟩)
        (fun synced => (effects.syncKeepsCache synced).2.1) effects.readsPending (fun _ => cacheEffects)
        (fun member removed accepted => (effects.unlink (later _ member) removed accepted).1) finish readFrame.2.1
        (exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm))
        (fun start present => (sameSuffix start).mpr present) rfl
    have repairedAuthority := repairFrame preparedAuthority
    have kept := sealed.trans (entry.kept.trans current.readPrefix.refines.1.retained.sealedFiles)
    obtain ⟨retained, _, _, _⟩ := plan.layout.retainedFromActualReplay plan.selected plan.accepted plan.ordered markerName decoded rfl
      replay plan.walLayout plan.walValid current.readPrefix.refines.1.retained.spans rfl
      (congrArg WalSegment.first plan.keeper) ready kept repairedAuthority.owned
    have keeperScope : managedPath dir ((dir).file (.walSegment plan.layout.keeper.first)) := .inr ⟨_, rfl⟩
    obtain ⟨preservedName, preservedBytes⟩ := liveFrame _ keeperScope
    have keeperBound := preservedName.trans named
    have exactBytes : visible reached inode = plan.layout.keeper.bytes := by
      have contents := physical.keeper
      change (observe reached).files.names ((dir).file (.walSegment plan.layout.keeper.first)) = some inode at named
      rw [named, Option.map_some] at contents
      apply Option.some.inj (contents.trans ?_)
      exact plan.layout.visible.symm.trans (exactKeeper.trans (congrArg some (congrArg Target.trimmed plan.targetEq).symm))
    have preparedBytes := (List.cons.inj (preservedBytes inode named)).1.trans exactBytes
    have valid : state.Valid := ⟨rfl, rfl, repairedAuthority.ownerAttached.2.1, repairedAuthority.rootAttached.2.1,
      ⟨cache.captured, repairedAuthority.cacheRoot.1⟩, retained⟩
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
    have keeperAtEntry : (observe reached).files.names ((dir).file (.walSegment target.first)) = some inode := by
      rw [← toTargetFirst]
      exact named
    exact plan.continuesLiteralAligned (allocation := allocation) (cache := refs)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      request cause (RawMarkedOpenInterpreter.assembles dir cache.lock files) retained rfl plan.targetEq entry.manifest rfl
      keepsSeals repairedAuthority.ownerAttached.1 repairedAuthority.ownerAttached.2.1 repairedAuthority.rootAttached.2.1
      phaseCache tokenCache ⟨cache.captured, repairedAuthority.cacheRoot⟩ phaseEffects tokenEqual exactReturn observe visible
      preparedDurability (atRoot repairedAuthority) (atLock repairedAuthority) (keeperInode := inode)
      (by simpa only [keeperPathEq] using keeperBound) (keeperEq.symm ▸ preparedBytes) keeperAtEntry
      ((congrArg WalSegment.bytes keeperEq).trans toTargetBytes) noAlias
      (effects.syncStorage state rfl inode) (by simpa only [keeperPathEq] using effects.syncHandles attached named remembered.2)
      (repairedAuthority.rootAttached.2.2.symm ▸ preparedAuthority.rootAttached) attached
      (by simpa only [keeperPathEq] using remembered.2)
      repairPlan source.remove stageWrite source.rename
      (fun ordinal member => by
        rw [keeperEq]
        exact Nat.lt_of_le_of_lt plan.layout.target.firstCovered (later ordinal member))
      later
      (fun synced => (effects.syncKeepsCache synced).2.2)
      (fun member removed accepted => effects.unlinkHandles attached named remembered.2 (later _ member) removed accepted)
      (fun member removed accepted bound => effects.unlinkStorage state rfl inode (later _ member) removed accepted
        (by simpa only [keeperPathEq] using bound))
      getRoot syncRoot pruned getPending
      (by simpa only [keeperPathEq] using findKeeper) (by simpa only [keeperPathEq] using clear) syncKeeper
      (by
        change ∀ start ∈ wal.segments.map WalSegment.first, firstOffset ≤ start
        simpa only [wal, WalSegmentImage.appendSelectedView_starts] using covers)
      selectedNames boundedStarts (fun start beyond => (listed start beyond).mp) effects.walNames
      (fun _ => WalNamePresenceFrame.ofStorageFrame phaseStorage (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
      (fun _ => WalNamePresenceFrame.ofStorageFrame tokenStorage (fun start _ _ => .inr ⟨.walSegment start, rfl⟩))
      (phaseStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
      (tokenStorage.weaken (fun _ selected => NativeReadyState.crashPath_rootOrChild (state := state) selected))
      (fun other named => phaseVisible other (by simpa only [keeperEq] using named))
      (fun other named => tokenVisible other (by simpa only [keeperEq] using named))

/-- Carry the selected reboot entry through the failed opens, then
interpret one literal successful open at the resulting heap. An earlier
write can select either marker independently of these recovery calls. -/
theorem NativeReadPosition.opensLiteralRepairedAfterWriteRetries
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (request : WriteRequest) (cause : IO.Error) {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table request.rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {firstOffset : Nat} (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target (fun atHeap => (observe atHeap).files.names) visible first)
    (recovery : RawOpenRetryTrace.RecoveryObservations view current.state target observe visible firstOffset
      target.range.through first)
    {attempts : source.FailedCalls first returns reached}
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun atHeap => ⟨(observe atHeap).files.names, fun inode => [visible atHeap inode]⟩)
      current.state.selectedRetryPath
      (RawOpenRetryTrace.RecoveryObservations view current.state target observe visible firstOffset
        target.range.through) attempts)
    (admission : source.AlignedAdmissionEffects view current.state input reached observe visible)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootBinding : (observe reached).files.names (dir).path = some (namespaceView.modelObject root))
    (shared : ∀ (cache : HeldOpenCache heap) (plan : current.SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      source.LiteralOpenEffects cache namespaceView root (current := current) (batch := batch) (target := target)
        plan observe visible)
    (aligns : ∀ (cache : HeldOpenCache heap) (plan : current.SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      plan.layout.tail.size = 0 →
      source.LiteralAlignedRepairEffects cache (current := current) plan observe visible)
    (replaces : ∀ (cache : HeldOpenCache heap) (plan : current.SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      0 < plan.layout.tail.size →
      source.LiteralKeeperReplacementEffects cache (current := current) plan observe visible)
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
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) ∧
      start.current.ready.state.session.directory = dir ∧
      (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
      (∀ {inode}, (observe reached).files.names ((dir).file (.walSegment target.first)) = some inode →
        visible reached inode = target.trimmed →
        (observe start.reached).files.names ((dir).file (.walSegment target.first)) = some inode ∧
          visible start.reached inode = target.trimmed) ∧
      ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
        start.current.ready.state.session.directory firstOffset through (observe start.reached) := by
  obtain ⟨plan, physical, entry, namesAtReached, _, settled, suffix⟩ :=
    current.preparesDurableVisibleWriteRetry prepared fits admitted observe visible covers initial recovery retryEffects
  obtain ⟨held, framed, authority, rootNamed, lockNamed, _, _, worker⟩ :=
    RawMarkedOpenInterpreter.reachesAlignedCache admission settled.protectedFiles.lockBound returned
  have rootObject := Option.some.inj (rootBinding.symm.trans rootNamed)
  obtain ⟨handle, start, cache, keptBatch, opened, history, ledger, replay, writeEntry, sameDirectory, covered,
    retainedKeeper, settledNames⟩ :=
    plan.returnsLiteralRepairedWriter held namespaceView root request cause observe visible
      (shared held plan authority rootObject) (aligns held plan authority rootObject) framed authority rootNamed lockNamed entry physical covers namesAtReached
      (replaces held plan authority rootObject) suffix settled phaseIdentity tokenIdentity phaseEffects tokenEqual returned worker
  exact ⟨plan, handle, start, cache, keptBatch, opened, history, ledger, replay, writeEntry, sameDirectory, covered,
    retainedKeeper, settledNames⟩

end LiteralContinuation

/-- Interpret the local effects of a successful checkpoint-free open on its literal returned handle and heap. -/
abbrev RawMarkedOpenInterpreter.AfterWalOpen
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (entry : heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (through : Nat) (post : DiskTable → heap → Prop) : Prop :=
  let names := fun h => (storage h).files.names
  let samples := fun h => CheckpointSurvivingFiles.mk (names h) (fun inode => [visible h inode])
  ∀ {input : FilePath} {returnedAt : heap} {table : DiskTable}
    (_admission : source.ObservedAdmissionEffects view directory (fun _ => False) input entry storage visible)
    (_reads : ∀ held : HeldOpenCache heap, LiteralOpenAuthority view directory held held.ready →
      source.AlignedReadEffects view directory held.pendingRef names visible namespaceView root
        (managedPath directory) (fun _ _ => True))
    (_child : ∀ start ≤ through,
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names entry (directory.file (.walSegment start)))
    (_laterAbsent : ∀ {before entries listed}, source.directoryCalls.run directory.path before = .ok entries listed →
      (samples entry).Frames (managedPath directory) (samples listed) →
      MarkedWalExtentReports.TruthfulAbsenceOn (through < ·) source.fileCalls directory
        namespaceView root (entries.toList.map (·.fileName)) listed)
    (_initializesPhase : ∀ {value before ref after}, source.allocatePhase (.ready value) before = .ok ref after →
      view.phase after ref = some (.ready value))
    (_tokenKeepsPhase : ∀ {before token after}, source.allocateToken () before = .ok token after →
      ∀ ref, view.phase after ref = view.phase before ref)
    (_returned : source.openTable input entry = .ok table returnedAt),
    post table returnedAt

/-- Local effects needed to interpret a successful checkpoint-free open
from the reached entry. The returned table and initialized phase
implement the given history. -/
abbrev RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory) (keeperFirst : Nat)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (entry : heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (history : List WAL.Write) : Prop :=
  source.AfterWalOpen view directory storage visible entry namespaceView root history.length fun table returnedAt =>
    ∃ (logical : PackedTable) (count : UInt64) (held : HeldOpenCache heap)
      (phase : IO.Ref (Phase Installed)) (token : IO.Ref Unit) (repaired afterPhase : heap),
      recoverSelected .empty (WAL.encode history) = .ok logical ∧
      logical.committed.toNat = history.length ∧
      source.allocatePhase (.ready (Reopened.installed ⟨logical, 0, count, keeperFirst⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token returnedAt ∧
      view.phase returnedAt phase =
        some (.ready (Reopened.installed ⟨logical, 0, count, keeperFirst⟩)) ∧
      table = RawMarkedOpenInterpreter.assemble directory held.lock
        (RawMarkedOpenInterpreter.makeCache directory held.directoryRef held.activeRef held.pendingRef) phase token ∧
      ∀ {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
        {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
        (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
        OpenPhaseCellEffects view.phase get set →
        (∀ {pinned : PackedTable} {after},
          set phase (.ready { (Reopened.installed ⟨logical, 0, count, keeperFirst⟩)
            with table := pinned }) returnedAt = .ok () after → ptrEq token token after = .ok true after) →
        ∀ key, table.LatestWalLookup phase token get set ptrEq returnedAt history key

/-- Every latest lookup through the returned session extends the same client ledger. -/
abbrev RawMarkedOpenInterpreter.ReadsClientHistoryAtOpen
    {heap stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (entry : heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead) (history : List WAL.Write) : Prop :=
  source.AfterWalOpen view directory storage visible entry namespaceView root history.length fun table returnedAt =>
    ∃ (installed : Installed) (phase : IO.Ref (Phase Installed)) (token : IO.Ref Unit),
      view.phase returnedAt phase = some (.ready installed) ∧
      (∃ lock files, table.UsesOpenReferences directory lock files phase token) ∧
      ∀ {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
        {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
        (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
        OpenPhaseCellEffects view.phase get set →
        (∀ {pinned : PackedTable} {after}, set phase (.ready { installed with table := pinned }) returnedAt = .ok () after →
          ptrEq token token after = .ok true after) →
        ∀ key, ∃ sequence value, table.ReadsLatest phase token get set ptrEq returnedAt key sequence value ∧
          sequence.toNat = history.length ∧ PendingClientReplay log (reads ++ [.lookup sequence key value]) history

/-- A successful literal open extends the selected client history with its actual lookup. -/
theorem RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen.recordsReads
    {directory : DiskDirectory} {keeperFirst : Nat} {storage visible rebooted namespaceView root history log reads}
    (opened : source.ReplaysWalBeforeCheckpointAtOpen view directory keeperFirst
      storage visible rebooted namespaceView root history)
    (pending : PendingClientReplay log reads history) :
    source.ReadsClientHistoryAtOpen view directory storage visible rebooted namespaceView root log reads history := by
  intro input returnedAt table admission effects child absent initializes keeps returned
  obtain ⟨logical, count, held, phase, token, repaired, afterPhase, _, _, _, _, stored, assembled, lookup⟩ :=
    opened admission effects child absent initializes keeps returned
  refine ⟨_, phase, token, stored, ?_, ?_⟩
  · rw [assembled]
    exact ⟨_, _, (RawMarkedOpenInterpreter.assembles _ _ _).usesReferences phase token⟩
  intro get set ptrEq cells compare key
  exact (lookup ptrEq cells compare key).recordsRead pending

section WalOnly

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage}
  {state : NativeReadyState} {source : RawMarkedOpenInterpreter heap stream}
  {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {acknowledged rebooted : heap}
  {namespaceView : DirectoryReadNamespace} {root : DeviceInode}

local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "samples" => fun h => CheckpointSurvivingFiles.mk (names h) (fun inode => [visible h inode])

/-- A successful literal open uses the live selected files at its entry.
The visible layout determines which keeper is installed. -/
theorem RawMarkedOpenInterpreter.replaysVisibleWalBeforeCheckpointAtOpen
    {directory : DiskDirectory} {entry : heap} {history : List WAL.Write} {lockInode : Nat}
    (layout : CanonicalKeeperLayout (view.files entry).image history)
    (lockBound : names entry (directory.file .lock) = some lockInode)
    (missing : layout.target.pair.manifest = none)
    (manifestAbsent : names entry (directory.file .manifest) = none)
    (markerBytes : (names entry (directory.file .walBoundary)).map (visible entry) = layout.target.pair.walBoundary)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (ordered : WAL.OrdinalsFrom 1 history)
    (wal : layout.VisibleWal directory (names entry) (visible entry)) :
    source.ReplaysWalBeforeCheckpointAtOpen view directory layout.keeper.first
      storage visible entry namespaceView root history := by
  intro input returnedAt table admission effects child laterAbsent initializesPhase tokenKeepsPhase returned
  let published : CheckpointPublication.Image := ⟨.settled none, fun _ _ => none⟩
  have noCheckpoint : SelectedIntegrityCheckpoint published.durable layout.target.pair.manifest none :=
    missing.symm ▸ .absent
  have accepted : published.AcceptsVersioned history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix history) layout.target.pair.manifest := by
    rw [missing]
    trivial
  have manifest : (samples entry).StoresManifest directory layout.target.pair.manifest := by
    rw [missing, CheckpointSurvivingFiles.StoresManifest]
    exact manifestAbsent
  have marker (marker : ByteArray) (present : layout.target.pair.walBoundary = some marker) :
      (samples entry).Stored (directory.file .walBoundary) marker := by
    obtain ⟨inode, named, payload⟩ := Option.map_eq_some_iff.mp (markerBytes.trans present)
    exact ⟨inode, named, congrArg List.singleton payload⟩
  obtain ⟨held, frame, authority, _, _, _, _, worker⟩ :=
    source.reachesAlignedCache admission lockBound returned
  have literal := (source.readsLiteralMarkedOpen directory layout noCheckpoint held.lock held.directoryRef held.activeRef
    held.pendingRef held.ready names visible
    namespaceView root (managedPath directory) (fun _ => trivial) (fun _ _ => trivial)
    ⟨frame.1, trivial⟩ (effects held authority) manifest
    (fun _ _ present _ _ _ _ _ => by simp [missing] at present)
    marker (.inr ⟨.manifest, rfl⟩)
    (fun _ _ present _ _ _ => by simp [missing] at present)
    (.inr ⟨.walBoundary, rfl⟩) following
    (fun start _ _ => .inr ⟨.walSegment start, rfl⟩) (fun start _ bound => child start (layout.through ▸ bound))
    (fun {before entries listed} scan frame => by
      rw [layout.through]
      exact @laterAbsent before entries listed scan frame) wal worker).1

  obtain ⟨count, markerBytes, patched, logical, _, _, _, _, _, repaired, _, _, phase, afterPhase, token,
    markerName, decoded, _, applied, _, _, _, _, _, _, _, _, _, _, allocation, tokenReturn, assembled, _⟩ := literal
  obtain ⟨replayed, _, sameRows, full, _, committed, _⟩ := layout.replaysSelected noCheckpoint accepted ordered
    markerName decoded (files := (layout.sealed ++ [layout.keeper]).map (fun item => (item.first, item.bytes)))
      (by simp [List.map_append])
  have equal : logical = replayed := congrArg Prod.snd (Except.ok.inj (applied.symm.trans sameRows))
  subst replayed
  let installed := Reopened.installed ⟨logical, 0, count, layout.keeper.first⟩
  have stored : view.phase returnedAt phase = some (.ready installed) :=
    (tokenKeepsPhase tokenReturn phase).trans (initializesPhase allocation)
  refine ⟨logical, count, held, phase, token, repaired, afterPhase, full, committed,
    allocation, tokenReturn, stored, assembled, ?_⟩
  intro get set ptrEq cells compare key
  have uses := (RawMarkedOpenInterpreter.assembles directory held.lock
    (RawMarkedOpenInterpreter.makeCache directory held.directoryRef held.activeRef held.pendingRef)).usesReferences phase token
  rw [← assembled] at uses
  exact uses.lookupLatestAfterWalReplay cells stored full ptrEq compare key

/-- Live close and reboot both expose a retained WAL through the same
named files. Only the active pair and keeper of the opener's image matter. -/
theorem RawMarkedOpenInterpreter.replaysRetainedWalAtOpen
    {directory : DiskDirectory} {entry : heap} {writer : SegmentedWriterState} {descriptor lockInode : Nat}
    (ready : writer.RetainedReady directory descriptor)
    (lockBound : names entry (directory.file .lock) = some lockInode)
    (missing : writer.target.pair.manifest = none)
    (absent : names entry (directory.file .manifest) = none)
    (marker : (names entry (directory.file .walBoundary)).map (visible entry) = writer.target.pair.walBoundary)
    (pair : (view.files entry).image.directory.active = writer.target.pair)
    (keeper : (view.files entry).image.keeper.active = some writer.target.trimmed)
    (window : writer.wal.NamespaceWindow directory 0 writer.history.length (names entry))
    (seals : ∀ segment ∈ writer.wal.sealed,
      (names entry (directory.file (.walSegment segment.first))).map (visible entry) = some segment.bytes)
    (active : (names entry (directory.file (.walSegment writer.wal.active.first))).map (visible entry) =
      some writer.wal.active.bytes) :
    source.ReplaysWalBeforeCheckpointAtOpen view directory writer.wal.active.first
      storage visible entry namespaceView root writer.history := by
  obtain ⟨layout, target, atKeeper, tail, descriptors, offsets⟩ := ready.visibleReopenLayout pair keeper
  have modeled := layout.modeledWindow _ offsets
  have wal : layout.VisibleWal directory (names entry) (visible entry) := by
    refine ⟨fun start low high => (window start (Nat.zero_le _) (layout.through ▸ high)).trans (modeled.1 start low),
      fun segment member => seals segment (WalSegmentImage.selectedSeals_subset descriptors member), ?_⟩
    rw [atKeeper, tail, ByteArray.append_empty]
    exact active
  rw [← atKeeper]
  exact @RawMarkedOpenInterpreter.replaysVisibleWalBeforeCheckpointAtOpen
    (source := source) (namespaceView := namespaceView) (root := root)
    (layout := layout) (lockBound := lockBound)
    (missing := (congrArg (fun t : Target => t.pair.manifest) target).trans missing) (manifestAbsent := absent)
    (markerBytes := marker.trans (congrArg (fun t : Target => t.pair.walBoundary) target).symm)
    (following := modeled.2) (ordered := ready.resumed.ordered) (wal := wal)

local notation "directory" => state.session.directory

/-- Read the visible files chosen by an exact retry entry. -/
theorem RawOpenRetryTrace.SelectedEntry.replaysWalBeforeCheckpointAtOpen
    {target : Target} {history : List WAL.Write}
    (selected : RawOpenRetryTrace.SelectedEntry view state target names visible rebooted)
    (layout : CanonicalKeeperLayout (view.files rebooted).image history)
    (noManifest : state.writer.target.pair.manifest = none)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (ordered : WAL.OrdinalsFrom 1 history)
    (wal : layout.VisibleWal directory (names rebooted) (visible rebooted)) :
    source.ReplaysWalBeforeCheckpointAtOpen view directory layout.keeper.first
      storage visible rebooted namespaceView root history := by
  have missing : layout.target.pair.manifest = none :=
    (congrArg DirectoryPublication.Bindings.manifest selected.valid.selected).trans (selected.manifest.trans noManifest)
  have manifestAbsent := selected.protectedFiles.manifest
  rw [noManifest] at manifestAbsent
  have marker := selected.marker.trans (congrArg DirectoryPublication.Bindings.walBoundary selected.valid.selected).symm
  exact @RawMarkedOpenInterpreter.replaysVisibleWalBeforeCheckpointAtOpen
    (source := source) (namespaceView := namespaceView) (root := root)
    (layout := layout) (lockBound := selected.protectedFiles.lockBound) (missing := missing)
    (manifestAbsent := manifestAbsent) (markerBytes := marker) (following := following)
    (ordered := ordered) (wal := wal)

/-- Before the first checkpoint, the sampled files determine the history
installed in the phase of the table returned by a successful public open. -/
theorem RawWriteRebootEntry.replaysWalBeforeCheckpointAtOpen
    (seen : RawWriteRebootEntry state view storage names visible acknowledged rebooted)
    (valid : state.Valid) (physical : NativeReadyStorage state (storage acknowledged))
    (reset : seen.DurableReset)
    (catalog : state.writer.wal.SettledNamespaceWindow directory 0 state.writer.target.range.through (storage acknowledged))
    (noManifest : state.writer.target.pair.manifest = none) :
    source.ReplaysWalBeforeCheckpointAtOpen view state.session.directory state.writer.wal.active.first
      storage visible rebooted namespaceView root state.writer.history := by
  obtain ⟨selected, recovery, _, _, layout, target, sameKeeper, _, descriptors, offsets, _⟩ :=
    seen.startsReadyRecovery valid physical reset catalog
  have through := congrArg (fun t : Target => t.range.through) target
  have window := recovery.1.restrict (Nat.zero_le layout.first) (Nat.le_of_eq through)
  have wal := selected.visibleReadyWal layout target descriptors offsets window
  have sameFirst := congrArg WalSegment.first sameKeeper
  rw [← sameFirst]
  exact @RawOpenRetryTrace.SelectedEntry.replaysWalBeforeCheckpointAtOpen
    (source := source) (namespaceView := namespaceView) (root := root)
    (selected := selected) (layout := layout)
    (noManifest := noManifest) (following := (layout.modeledWindow _ offsets).2)
    (ordered := valid.retained.resumed.ordered) (wal := wal)

/-- An uncertain write uses the same literal reopen and latest read as
an acknowledged write. Its sampled marker fixes the old or whole-batch
history carried by the selected plan. -/
theorem NativeReadPosition.SelectedWritePlan.replaysWalBeforeCheckpointAtOpen
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition prior log} {batch : List WAL.Write} {target : Target}
    (plan : current.SelectedWritePlan batch target (view.files rebooted).image)
    (selected : RawOpenRetryTrace.SelectedEntry view current.state target names visible rebooted)
    {firstOffset : Nat}
    (recovery : RawOpenRetryTrace.RecoveryObservations view current.state target storage visible firstOffset
      target.range.through rebooted)
    (covers : ∀ offset ∈ current.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset)
    (noManifest : current.state.writer.target.pair.manifest = none) :
    source.ReplaysWalBeforeCheckpointAtOpen view current.state.session.directory current.state.writer.wal.active.first
      storage visible rebooted namespaceView root plan.history := by
  have sameFirst := congrArg WalSegment.first plan.keeper
  change plan.layout.keeper.first = current.state.writer.wal.active.first at sameFirst
  rw [← sameFirst]
  exact @RawOpenRetryTrace.SelectedEntry.replaysWalBeforeCheckpointAtOpen
    (source := source) (namespaceView := namespaceView) (root := root)
    (selected := selected) (layout := plan.layout)
    (noManifest := noManifest) (following := plan.modeledWindow.2)
    (ordered := plan.ordered)
    (wal := plan.visibleWal names visible covers recovery.1 selected.protectedFiles recovery.2.1)

end WalOnly

end Alvoki.Storage.DiskSession
