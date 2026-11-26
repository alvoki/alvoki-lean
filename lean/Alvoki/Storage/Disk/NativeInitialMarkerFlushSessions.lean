import Alvoki.Storage.Disk.NativeInitialMarkerFlushError
import Alvoki.Storage.Disk.NativeBootstrapFlushReopen
import Alvoki.Storage.Disk.NativeOpenedRestartSessions

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {input nextInput : FilePath} {directory : DiskDirectory}
  {before : LockedFileState WalSegmentRotation.State}
  {previous : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {capture : BootstrapCacheOpen previous.toBootstrapAdmissionCalls} {listing : BootstrapCheckedListing capture}
  {initial : BootstrapZeroKeeperRoute listing} {source : BootstrapMarkerFlushError initial}
  {view : OpenCloseHeapView heap WalSegmentRotation.State}

/-- The exact raw return and file observation established by the
reported cleanup of the first failed public open. -/
structure BootstrapFlushCallerReturn (source : BootstrapMarkerFlushError initial)
    (view : OpenCloseHeapView heap WalSegmentRotation.State) (input : FilePath) where
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
    IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles
  held : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable
  release : IO.FS.Handle → heap → heap
  lock : IO.FS.Handle
  entry : heap
  reached : heap
  names : heap → DirectoryReadNamespace
  inodes : heap → WalInodeImage
  returned : finishFailedOpen (calls.runOpen input init makeCache held) release lock entry =
    .error source.returnedError reached
  files : view.files reached = source.final
  directoryView : names reached = source.reachedView
  payloads : inodes reached = source.reachedInodes

section

variable {firstSelected : BootstrapReusedZeroKeeper listing}
  {firstError : BootstrapMarkerFlushError (.reused firstSelected)} {firstInventory : DescriptorInventory}
  {firstAdmission : CensusOpenAdmissionReports input directory firstInventory before}
  {firstCalls : RawOpenAdmissionCallbacks heap} {firstInit : OpenSyncCacheCallbacks heap} {firstEntry : heap}
  {firstRaw : RawOpenAdmissionReport firstAdmission view firstCalls firstEntry}
  {firstSeed : OpenSyncCacheAllocations capture.opened view firstInit firstRaw.afterFlock}
  {firstBootstrap : FreshBootstrapCacheCalls heap}
  {firstGuards : ReusedBootstrapKeeperGuards firstSelected firstSeed firstBootstrap}
  {firstKeeper : ReusedBootstrapKeeperHeap firstGuards}
  {failed : RawBootstrapMarkerFlushError firstKeeper firstError} {release : IO.FS.Handle → heap → heap}

theorem RawBootstrapMarkerFlushCleanup.callerReturn
    (cleanup : RawBootstrapMarkerFlushCleanup firstRaw failed release)
    (model : OpenAdmissionReports input directory previous.slot) (valid : BootstrapValid before.image)
    (owner : firstAdmission.owner = previous.slot)
    (metadata : ∀ path, firstBootstrap.metadata path = optionalMetadataWith (firstCalls.lookup path))
    (keeperLookup : firstGuards.metadataLookup (directory.file (.walSegment 0)) =
      firstCalls.lookup (directory.file (.walSegment 0)))
    (flat : firstBootstrap.metadata (directory.file .wal) firstSeed.afterPending = .ok none firstSeed.afterPending)
    (absent : firstBootstrap.metadata (directory.file .walBoundary) firstSeed.afterPending = .ok none firstSeed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    ∃ earlier : BootstrapFlushCallerReturn firstError view input, earlier.reached = cleanup.finalized.reached := by
  obtain ⟨_, makeCache, _, _, _, _, _, _, returned, _, files, _, _, _, _, _, payloads, directoryView⟩ :=
    cleanup.returns model valid owner metadata keeperLookup flat absent marked install
  exact ⟨⟨firstCalls, firstInit, makeCache, _, release, firstRaw.lock, firstEntry, cleanup.finalized.reached,
    failed.names, firstKeeper.inodes, returned, files, directoryView, payloads⟩, rfl⟩

end

variable {survivor : BootstrapMarkerFlushSurvivor source}
  {next : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory survivor.state}
  {nextCapture : BootstrapCacheOpen next.toBootstrapAdmissionCalls} {nextListing : BootstrapCheckedListing nextCapture}
  {selected : BootstrapReusedZeroKeeper nextListing} {nextMarker : BootstrapMarkerCustody nextListing}
  {handoff : BootstrapKeeperMarkerHandoff (.reused selected) nextMarker}
  {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus nextMarker}
  {init : OpenSyncCacheCallbacks heap} {entry : heap} {inventory : DescriptorInventory}
  {nextAdmission : CensusOpenAdmissionReports nextInput directory inventory survivor.state}
  {calls : RawOpenAdmissionCallbacks heap} {bootstrap : FreshBootstrapCacheCalls heap}
  {admitted : RawOpenAdmissionReport nextAdmission view calls entry}
  {seed : OpenSyncCacheAllocations nextCapture.opened view init admitted.afterFlock}
  {guards : ReusedBootstrapKeeperGuards selected seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}
  {publication : keeper.MarkerPublication handoff effects} {staging : BootstrapMarkerStageCalls heap}
  {collision : BootstrapMarkerCollisionHeap publication.raw (.reused selected) nextMarker staging keeper.inodes}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- A known raw flush failure and its reported scratch survivor precede
the first ready table. The finite session trace starts at the table and
heap returned by that same admitted retry. -/
theorem BootstrapFlushRetryReader.executesAfterCallerError
    (older : BootstrapFlushCallerReturn source view input)
    (reader : BootstrapFlushRetryReader admitted publication collision)
    (firstAdmission : OpenAdmissionReports input directory previous.slot) (valid : BootstrapValid before.image)
    (unlock : previous.unlock.LocalFlock) (modelAdmission : OpenAdmissionReports nextInput directory next.slot)
    (owner : nextAdmission.owner = next.slot)
    (metadata : ∀ path, bootstrap.metadata path = optionalMetadataWith (calls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) = calls.lookup (directory.file (.walSegment 0)))
    (flat : bootstrap.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : bootstrap.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : Reopened).installed publication.raw.markerDirectory.reached)
    (phaseID : phaseIdentity allocation.phase = next.nextRef)
    (tokenID : tokenIdentity allocation.token = next.nextRef + 1)
    (phaseFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      publication.raw.markerDirectory.reached allocation.afterPhase)
    (tokenFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      allocation.afterPhase allocation.afterToken)
    (phaseInodes : keeper.inodes allocation.afterPhase = keeper.inodes publication.raw.markerDirectory.reached)
    (tokenInodes : keeper.inodes allocation.afterToken = keeper.inodes allocation.afterPhase)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (files : heap → LockedFileState FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    let clientView := view.withFileProjection files
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved seed.directoryRef seed.activeRef seed.pendingRef)
    finishFailedOpen (older.calls.runOpen input older.init older.makeCache older.held) older.release older.lock older.entry =
      .error source.returnedError older.reached ∧
    view.files older.reached = source.final ∧ view.files entry = survivor.state ∧
    collision.stale.child = source.child.child ∧
    survivor.scratchBytes ∈ (older.inodes older.reached).crashBytes
      ((older.names older.reached).modelObject collision.stale.child) ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (start : NativeOpenedSessionPoint heap),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      calls.runOpen nextInput init makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry =
        .ok start.handle.table start.position.reached ∧
      start.position.current.history = [] ∧ start.position.current.submissions = [] ∧
      start.position.current.ready.reads = [] ∧ start.position.pins = [] ∧
      ∀ actions, NativeOpenedSessionTrace.Reports clientView names bytes start actions →
        ∃ events last, NativeOpenedSessionTrace clientView names bytes start actions events last ∧
          last.position.current.history = events.flatMap NativeExecutionEvent.writes ∧
          last.position.current.submissions = events.flatMap NativeExecutionEvent.submissions ∧
          last.position.current.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
          InstalledClientReplay last.position.current.submissions last.position.current.ready.reads last.position.current.history
            last.position.current.ready.state.writer.installed last.position.current.ready.state.session := by
  intro clientView recover
  obtain ⟨_, rebootFiles, _, _, _, _, stale, _, fromScratch, _, cacheOpen, makeCache, handle, position, _,
    action, cacheSource, ran, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, history, submissions, reads, pins⟩ :=
    reader.opens firstAdmission valid unlock modelAdmission owner metadata keeperLookup flat absent
      marked assemble constructs allocation phaseID tokenID phaseFrame tokenFrame phaseInodes tokenInodes phaseEffects ptrEq
  have actualChoice : survivor.scratchBytes ∈ (older.inodes older.reached).crashBytes
      ((older.names older.reached).modelObject collision.stale.child) := by
    rw [older.payloads, older.directoryView, stale, ← source.reachedMarkerInode]
    exact fromScratch
  let start : NativeOpenedSessionPoint heap := ⟨handle, position⟩
  refine ⟨older.returned, older.files, rebootFiles, stale, actualChoice,
    cacheOpen, makeCache, start, action, cacheSource, ran, history, submissions, reads, pins, ?_⟩
  intro actions localReports
  obtain ⟨events, last, trace, ledger, replay⟩ := NativeOpenedSessionTrace.executes start actions localReports
  refine ⟨events, last, trace, ?_, ?_, ?_, replay⟩
  · simpa only [start, history, List.nil_append] using ledger.history
  · simpa only [start, submissions, List.nil_append] using ledger.submissions
  · simpa only [start, reads, List.nil_append] using ledger.reads

end Alvoki.Storage.DiskSession
