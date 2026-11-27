import Alvoki.Storage.Disk.NativeCheckpointFinalManifest
import Alvoki.Storage.Disk.NativeCheckpointSourceReopen
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace
import Alvoki.Storage.Disk.NativeAlignedMarkedReady
import Alvoki.Storage.Disk.NativeAlignedReadyCalls

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)
open Sequential (SnapshotTable)

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {cause : IO.Error} {reached : CheckpointWorld heap}

local notation "dbDir" => current.current.ready.state.session.directory
local notation "ready" => current.current.ready

variable {view : OpenCloseHeapView heap FileImage}
  {rebooted entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

/-- The reopened writer's footprint uses the selected manifest, the same
WAL files, and the same canonical directory as the checkpoint reset. -/
theorem NativeReadyState.crashPath_forSelectedCheckpoint
    (state : NativeReadyState) (directory : DiskDirectory) (previous : SegmentedWriterState)
    (manifest : Option ByteArray)
    (sameDirectory : state.session.directory = directory)
    (sameKeeper : state.writer.wal.active.first = previous.wal.active.first)
    (sameSeals : state.writer.wal.sealed = previous.wal.sealed)
    (sameManifest : state.writer.target.pair.manifest = manifest) :
    state.crashPath = (fun path => path = directory.path ∨ path = directory.file .lock ∨
      checkpointSurvivorPath directory previous manifest path) := by
  funext path
  simp only [NativeReadyState.crashPath, checkpointSurvivorPath, checkpointWalPath,
    sameDirectory, sameKeeper, sameSeals, sameManifest]


section

variable (inodes : heap → WalInodeImage)

local notation "readBytes" => (fun atHeap => WalInodeImage.visible (inodes atHeap))

/-- Read the selected old or new checkpoint after the literal successful
open acquires the sampled directory and LOCK. The same sample fixes the
manifest, runs and WAL bytes. The live catalog also fixes which canonical
WAL names are absent through the cutoff. The actual aligned repair and
reference allocations can then supply the retained writer of that table.
Use the cumulative failed-call frame at the entry heap. The reader uses
its live projections. `FailedCalls.framesSampledCheckpoint` can also
supply the durable files and parent settlement for the ready continuation. -/
theorem NativeCheckpointSourcePrefix.readsLiteralSampledCheckpoint
    (prior : NativeCheckpointSourcePrefix current primitives fsync stage)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (selectedSample : prior.SampledReplay names contents)
    (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootObject : namespaceView.modelObject root =
      current.current.ready.state.census.inode current.current.ready.state.directorySlot.description)
    (resetFiles : (⟨names, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      (fun path => path = (dbDir).path ∨ path = (dbDir).file .lock ∨
        checkpointSurvivorPath dbDir current.current.ready.state.writer
          ((names ((dbDir).file .manifest)).map contents) path)
      ⟨(observe rebooted).files.names, fun inode => [readBytes rebooted inode]⟩)
    (sampledWindow : current.current.ready.state.writer.wal.NamespaceWindow dbDir 0
      current.current.ready.state.writer.history.length names)
    (resetWindow : ∀ start ≤ current.current.ready.state.writer.history.length,
      ((observe rebooted).files.names ((dbDir).file (.walSegment start))).isSome =
        (names ((dbDir).file (.walSegment start))).isSome)
    (retryFiles :
      (⟨(observe rebooted).files.names, fun inode => [readBytes rebooted inode]⟩ : CheckpointSurvivingFiles).Frames
        (fun path => path = (dbDir).path ∨ path = (dbDir).file .lock ∨
          checkpointSurvivorPath dbDir current.current.ready.state.writer
            ((names ((dbDir).file .manifest)).map contents) path)
        ⟨(observe entry).files.names, fun inode => [readBytes entry inode]⟩)
    (retryWindow : ∀ start ≤ current.current.ready.state.writer.history.length,
      ((observe entry).files.names ((dbDir).file (.walSegment start))).isSome =
        ((observe rebooted).files.names ((dbDir).file (.walSegment start))).isSome)
    (readScope : FilePath → Prop)
    (admission : source.ObservedAdmissionEffects view dbDir readScope input entry observe readBytes)
    (effects : ∀ cache : HeldOpenCache heap, LiteralOpenAuthority view dbDir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      source.AlignedReadEffects view dbDir cache.pendingRef (fun atHeap => (observe atHeap).files.names) readBytes
        namespaceView root (managedPath dbDir)
        (observedOpenReadFrame view dbDir readScope cache observe))
    (child : ∀ start ≤ current.current.ready.state.writer.history.length,
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        (observe entry).files.names ((dbDir).file (.walSegment start)))
    (physicalScan : ∀ (cache : HeldOpenCache heap) (held : LiteralOpenAuthority view dbDir cache cache.ready)
      (bound : namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description),
      source.directoryCalls.ObservesWalNames dbDir (effects cache held bound).streamObject root
        (fun atHeap => (observe atHeap).files.names) (current.current.ready.state.writer.history.length < ·))
    {table : DiskTable} {returnedAt : heap}
    (returned : source.openTable input entry = .ok table returnedAt) :
    let dir := dbDir
    let writer := current.current.ready.state.writer
    let pair : DirectoryPublication.Bindings :=
      ⟨(names (dir.file .manifest)).map contents, (names (dir.file .walBoundary)).map contents⟩
    let wal : WalSegmentImage := { writer.wal with directory := .settled pair }
    let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
    let retry := wal.checkpointReopenFiles wal.directory none
    let selectedPath := checkpointSurvivorPath dir writer pair.manifest
    let footprint := fun path => path = dir.path ∨ path = dir.file .lock ∨ selectedPath path
    let sampleFiles : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
    ∃ (cache : HeldOpenCache heap) (published : CheckpointPublication.Image)
      (layout : CanonicalKeeperLayout retry writer.history)
      (checkpoint : Option (PackedTable × UInt64)),
      LiteralOpenAuthority view dir cache cache.ready ∧
      names dir.path = some (cache.captured.inode cache.rootSlot.description) ∧
      names (dir.file .lock) = some (cache.captured.inode cache.owner.description) ∧
      view.active cache.ready cache.activeRef = none ∧ view.pending cache.ready cache.pendingRef = [] ∧
      layout.keeper = wal.active ∧ layout.tail = .empty ∧
      SelectedIntegrityCheckpoint actual pair.manifest checkpoint ∧
      wal.NamespaceWindow dir 0 layout.range.through (observe entry).files.names ∧
      layout.VisibleWal dir (observe entry).files.names (readBytes entry) ∧
      source.LiteralMarkedReturn dir layout checkpoint cache.lock cache.directoryRef cache.activeRef cache.pendingRef
        cache.ready view (fun atHeap => (observe atHeap).files.names) readBytes namespaceView root (managedPath dir)
        (observedOpenReadFrame view dir readScope cache observe) entry returnedAt table ∧
      (source.LiteralAlignedFinishEffects (view := view) cache dir layout entry observe →
        source.LiteralAllocationEffects view dir cache observe readBytes layout.keeper.first →
        ∀ (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat),
        (view.files entry).image.directory.active = pair →
        (view.files entry).image.keeper.active = some wal.active.bytes →
        (view.files entry).image.kept = retry.kept →
        (∀ ordinal ∈ (view.files entry).image.later.visible, writer.history.length < ordinal ∧
          ∃ object, namespaceView.child root (renderWalSegmentName ordinal) = some object) →
        ∃ (repaired : heap) (reopened : SegmentedWriterState)
          (allocation : OpenReferenceAllocations source.allocatePhase source.allocateToken view.phase reopened.installed repaired),
            source.LiteralAlignedReturn dir layout { published with durable := actual } checkpoint wal cache view
              phaseIdentity tokenIdentity reopened allocation returnedAt table ∧
            (source.ObservedAlignedRepairEffects (view := view) cache dir layout entry observe readBytes →
              (∀ path, footprint path → readScope path) →
              sampleFiles.Frames footprint (observe rebooted).files →
              (∀ surviving ∈ (observe rebooted).crashNames, surviving dir.path = names dir.path) →
              (observe rebooted).files.Frames footprint (observe entry).files →
              (observe rebooted).Frames (· = dir.path) (observe entry) →
              ∀ (origin : NativeExecutionPosition) (earlier : List NativeExecutionEvent),
                origin.LedgerSuffix earlier current.current → OpenPhaseCellEffects view.phase get set →
                ∀ _ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool,
                  source.AlignedReadyCalls input entry returnedAt table dir cache view reopened allocation
                    phaseIdentity tokenIdentity origin earlier inodes runs observe 0)) := by
  intro dir writer pair wal actual retry selectedPath footprint sampleFiles
  let live := fun atHeap => (observe atHeap).files.names
  let filesAt : heap → CheckpointSurvivingFiles := fun atHeap => ⟨live atHeap, fun inode => [readBytes atHeap inode]⟩
  have sampled := resetFiles.trans retryFiles
  have window := sampledWindow.frame (fun start _ bound => (retryWindow start bound).trans (resetWindow start bound))
  obtain ⟨sampledAuthority, marker, segments, published, layout, _, walLayout, walValid, keeper, aligned, descriptors, offsets,
    _, _, accepted, _, _, _, checkpoint, _, _, selected, _, _, _, _, _⟩ := selectedSample
  have liveRoot := (sampled _ (.inl rfl)).1.trans sampledAuthority.directory
  have liveLock := (sampled _ (.inr (.inl rfl))).1.trans sampledAuthority.lock
  obtain ⟨cache, admitted, authority, rootNamed, lockNamed, emptyActive, emptyPending, worker⟩ :=
    source.reachesAlignedCache admission liveLock returned
  have heldRoot := (sampled _ (.inl rfl)).1.symm.trans rootNamed
  have heldLock := (sampled _ (.inr (.inl rfl))).1.symm.trans lockNamed
  have rootMatches := (congrArg some rootObject).trans (liveRoot.symm.trans rootNamed)
  have bound := Option.some.inj rootMatches
  let readEffects := effects cache authority bound
  have laterAtScan {before listed : heap} {entries : Array IO.FS.DirEntry}
      (returned : source.directoryCalls.run dir.path before = .ok entries listed) :
      ∀ start, layout.range.through < start →
        ((∃ object, namespaceView.child root (renderWalSegmentName start) = some object) ↔
          ((observe listed).files.names (dir.file (.walSegment start))).isSome = true) := by
    intro start beyond
    exact source.directoryCalls.liveWalChildren dir namespaceView root readEffects.streamObject
      (physicalScan cache authority bound) returned (fun _ _ opened => readEffects.streamRoot opened)
      (fun _ _ _ _ opened scanned closed => readEffects.complete opened scanned closed) start (layout.through ▸ beyond)
  have sampledFiles : (⟨names, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      selectedPath (filesAt entry) := fun path selected => sampled path (.inr (.inr selected))
  let files : CheckpointSurvivingFiles := ⟨(observe entry).files.names, fun inode => [readBytes entry inode]⟩
  have manifest : files.StoresManifest dir pair.manifest := by
    cases named : names (dir.file .manifest) with
    | none => exact (by
        simpa [CheckpointSurvivingFiles.StoresManifest, pair, named] using
          (sampledFiles _ (.inl rfl)).1.trans named)
    | some inode =>
      have fromSample : (⟨names, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Stored
          (dir.file .manifest) (contents inode) := ⟨inode, named, rfl⟩
      simpa [CheckpointSurvivingFiles.StoresManifest, pair, named] using sampledFiles.stored (.inl rfl) fromSample
  have selectedRuns (bytes metadata) (named : pair.manifest = some bytes)
      (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
      (index : Nat) (within : index < metadata.header.runCount.toNat) (payload : ByteArray)
      (stored : actual metadata.header.generation index = some payload) :
      files.Stored (dir.file (.run metadata.header.generation index)) payload := by
    obtain ⟨inode, bound, value⟩ := Option.map_eq_some_iff.mp stored
    exact sampledFiles.stored (.inr (.inr ⟨bytes, metadata, index, named, decoded, within, rfl⟩))
      ⟨inode, bound, congrArg List.singleton value⟩
  have markerBytes (bytes) (bound : pair.walBoundary = some bytes) :
      files.Stored (dir.file .walBoundary) bytes := by
    have sampledMarker := sampledFiles.stored (.inr (.inl (.inl rfl))) marker
    obtain ⟨inode, named, contentsAt⟩ := marker
    have value : pair.walBoundary = some (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64) := by
      change names (dir.file .walBoundary) = some inode at named
      change [contents inode] = _ at contentsAt
      change (names (dir.file .walBoundary)).map contents = _
      rw [named, Option.map_some, (List.cons.inj contentsAt).1]
    exact (Option.some.inj (value.symm.trans bound)) ▸ sampledMarker
  have segmentBytes (segment : WalSegment) (member : segment ∈ writer.wal.segments) :
      ((observe entry).files.names (dir.file (.walSegment segment.first))).map (readBytes entry) = some segment.bytes := by
    have scope : checkpointWalPath dir writer (dir.file (.walSegment segment.first)) := by
      rcases List.mem_append.mp member with sealed | current
      · exact .inr (.inr ⟨segment, sealed, rfl⟩)
      · obtain rfl := List.mem_singleton.mp current
        exact .inr (.inl rfl)
    obtain ⟨inode, named, payload⟩ := sampledFiles.stored (.inr (.inl scope)) (segments segment member)
    change (observe entry).files.names (dir.file (.walSegment segment.first)) = some inode at named
    change [readBytes entry inode] = [segment.bytes] at payload
    rw [named, Option.map_some, (List.cons.inj payload).1]
  have selectedOffsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (layout.sealed ++ [layout.keeper]).map WalSegment.first) := by
    rw [descriptors]
    exact offsets
  have modeled := layout.modeledWindow (wal.segments.map WalSegment.first) selectedOffsets
  have physical : layout.VisibleWal dir ((observe entry).files.names) (readBytes entry) := by
    refine ⟨fun start lower upper =>
      (window start (Nat.zero_le start) (layout.through ▸ upper)).trans (modeled.1 start lower), ?_, ?_⟩
    · intro segment member
      have read : segment ∈ layout.sealed ++ [layout.keeper] := List.mem_append_left _ member
      rw [descriptors, WalSegmentImage.readDescriptors] at read
      split at read
      · exact segmentBytes segment (List.mem_filter.mp read).1
      · exact segmentBytes segment (List.mem_append_right _ read)
    · simpa [aligned, keeper] using segmentBytes writer.wal.active (by simp [WalSegmentImage.segments])
  obtain ⟨literal, ⟨_, listed, _, scan, entryToScan⟩⟩ := source.readsLiteralMarkedOpen dir layout selected cache.lock cache.directoryRef cache.activeRef cache.pendingRef
    cache.ready (fun atHeap => (observe atHeap).files.names) readBytes namespaceView root (managedPath dir)
    observedOpenReadFrame.refl observedOpenReadFrame.trans (admitted.entersReader authority) readEffects
    manifest selectedRuns markerBytes (.inr ⟨.manifest, rfl⟩)
    (fun _ metadata _ _ index _ => .inr ⟨.run metadata.header.generation index, rfl⟩)
    (.inr ⟨.walBoundary, rfl⟩) modeled.2 (fun start _ _ => .inr ⟨.walSegment start, rfl⟩)
    (fun start _ bound => child start (layout.through ▸ bound))
    (fun scanned _ =>
      source.fileCalls.absenceOnFromNamePresence dir live readBytes namespaceView root (managedPath dir)
        (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun path before => (readEffects.statFrame path before).1)
        readEffects.statMissing (fun start _ => .inr ⟨.walSegment start, rfl⟩) (laterAtScan scanned))
    physical worker
  have laterComplete (start : Nat) (beyond : layout.range.through < start)
      (present : ∃ inode, (observe entry).files.names (dir.file (.walSegment start)) = some inode) :
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object := by
    apply (laterAtScan scan start beyond).mpr
    change (live listed (dir.file (.walSegment start))).isSome = true
    have kept : live listed (dir.file (.walSegment start)) = live entry (dir.file (.walSegment start)) :=
      (entryToScan _ (.inr ⟨.walSegment start, rfl⟩)).1
    rw [kept]
    exact Option.isSome_iff_exists.mpr present
  refine ⟨cache, published, layout, checkpoint, authority, heldRoot, heldLock, emptyActive, emptyPending,
    keeper, aligned, selected, (fun start lower upper => window start lower (layout.through ▸ upper)), physical, literal, ?_⟩
  intro repair allocate phaseId tokenId selectedPair selectedKeeper sealed suffix
  have retained := current.current.ready.readPrefix.refines.1.retained
  obtain ⟨repaired, reopened, allocation, installed, ⟨seen⟩⟩ :=
    source.retainsLiteralAlignedReturn dir layout (published := { published with durable := actual })
    selected accepted retained.resumed.ordered walLayout walValid retained.spans rfl (congrArg WalSegment.first keeper)
    aligned cache authority observe readBytes namespaceView root readScope literal selectedPair
    (by simpa only [CanonicalKeeperLayout.target, keeper] using selectedKeeper) sealed
    (fun ordinal member => (suffix ordinal member).imp_left (fun after => layout.through.symm ▸ after))
    repair allocate phaseId tokenId
  refine ⟨repaired, reopened, allocation, installed, ?_⟩
  intro observed included restored rootReset retryDurable retryParent origin earlier carried phaseEffects ptrEq
  have readDurable := seen.storageFrame.weaken included
  have durableAtPrepare := restored.trans (retryDurable.trans readDurable.visible)
  have rootFrame : (observe rebooted).Frames (· = dir.path) (observe seen.prepared) :=
    retryParent.trans (readDurable.weaken (fun _ same => .inl same))
  have rootAtReset := (restored dir.path (.inl rfl)).1
  have rootSettled := rootFrame.settledFrom
    (fun surviving possible path same => same.symm ▸ (rootReset surviving possible).trans rootAtReset.symm)
  let next := allocation.readyState reopened dir cache.owner cache.rootSlot
    cache.directoryRef cache.activeRef cache.pendingRef phaseId tokenId
  have fromInstall := installed
  obtain ⟨_, heldRepair, sameHistory, _, sameTarget, sameRuns, sameWal, _⟩ := fromInstall
  have scope : next.crashPath = footprint := by
    apply NativeReadyState.crashPath_forSelectedCheckpoint next dir writer pair.manifest rfl
    · have first := congrArg (fun image : WalSegmentImage => image.active.first) sameWal
      exact first
    · have sealed := congrArg WalSegmentImage.sealed sameWal
      exact sealed
    · exact congrArg (fun target : Target => target.pair.manifest) sameTarget
  have sameAuthority : RebootDirectoryBindings next names :=
    ⟨heldRoot.trans (congrArg some heldRepair.rootAttached.2.2.symm),
      heldLock.trans (congrArg some heldRepair.ownerAttached.2.2.symm)⟩
  have seals (segment : WalSegment) (member : segment ∈ next.writer.wal.sealed) :
      (names (dir.file (.walSegment segment.first))).map contents = some segment.bytes := by
    change segment ∈ reopened.wal.sealed at member
    rw [sameWal] at member
    obtain ⟨inode, bound, bytes⟩ := segments segment (List.mem_append_left _ member)
    change names (dir.file (.walSegment segment.first)) = some inode at bound
    change [contents inode] = [segment.bytes] at bytes
    rw [bound, Option.map_some, (List.cons.inj bytes).1]
  have preparedFiles : sampleFiles.Frames next.writeFramePath (observe seen.prepared).files := by
    intro path pathProtected
    have tracked : next.crashPath path := NativeReadyState.crashPath_iff_write.mpr (.inr (.inr pathProtected))
    exact durableAtPrepare path (scope ▸ tracked)
  have protectedFiles : NativeReadyProtectedStorage next (observe seen.prepared).files :=
    NativeReadyProtectedStorage.ofCheckpointSample names contents preparedFiles sameAuthority
      (congrArg (fun target : Target => target.pair.manifest) sameTarget).symm seals
      (fun generation index => congrFun (congrFun sameRuns generation) index)
  have durableMarker : (observe seen.prepared).files.Stored (dir.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode reopened.history).size.toUInt64) := by
    rw [sameHistory]
    exact durableAtPrepare.stored (.inr (.inr (.inr (.inl (.inl rfl))))) marker
  have boundedStarts : ∀ start ∈ wal.segments.map WalSegment.first, start ≤ layout.range.through := by
    intro start member
    obtain ⟨segment, occurs, rfl⟩ := List.mem_map.mp member
    have activeFirst : wal.active.first ≤ layout.range.through := keeper ▸ layout.target.firstCovered
    rcases List.mem_append.mp occurs with sealed | active
    · exact Nat.le_trans
        (Nat.le_of_lt ((List.pairwise_append.mp walLayout.ordered).2.2 _ sealed _ (List.mem_singleton_self _)).1) activeFirst
    · simpa only [List.mem_singleton.mp active] using activeFirst
  exact installed.refinesReadyCalls returned current.current.ready.readPrefix.refines.2.1 carried inodes runs observe
    namespaceView root seen observed allocate protectedFiles durableMarker
    (fun surviving possible => rootSettled surviving possible dir.path rfl) aligned keeper physical.keeper
    (fun start lower upper => window start lower (layout.through ▸ upper)) boundedStarts laterComplete phaseEffects ptrEq

end

/-- A physical checkpoint selection and its subsequent calls share one
client ledger across restart. The prefix can belong to a fresh caller or
to an already opened writer. -/
def NativeOpenedPosition.SampledCheckpointRecovery (current : NativeOpenedPosition opened)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (newManifest : ByteArray) (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (origin : NativeExecutionPosition) (earlier : List NativeExecutionEvent)
    (errors : List (FilePath × IO.Error)) : Prop :=
    let dir := dbDir
    let state := (ready).state
    let pair : DirectoryPublication.Bindings :=
      ⟨(names (dir.file .manifest)).map contents, (names (dir.file .walBoundary)).map contents⟩
    let wal : WalSegmentImage := { state.writer.wal with directory := .settled pair }
    let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
    let retry : LockedFileState FileImage :=
      ⟨wal.checkpointReopenFiles wal.directory none, state.files.owners.set (dir.file .lock) none⟩
    let vacant : TryLockObserves retry.owners dir (.ok true) := fun _ => by simp [retry, LockOwners.set]
    let selectedPath : FilePath → Prop := fun path =>
      path = dir.path ∨ path = dir.file .lock ∨ checkpointSurvivorPath dir state.writer pair.manifest path
    let physical : heap → CheckpointStorageObservation := fun heap => (observe heap).storageObservation
    let filesAt : heap → CheckpointSurvivingFiles := fun heap =>
      ⟨(physical heap).files.names, fun inode => [(inodes heap).visible inode]⟩
    let checkpointFiles : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
    (checkpointFiles.Frames selectedPath (filesAt rebooted)) →
    (∀ {prior : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
      source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(path, cause)]) errors →
      source.openTable path before = .error cause after →
      (filesAt before).Frames selectedPath (filesAt after) ∧ (view.files after).image = (view.files before).image) →
    (∀ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history),
      Prepared retry.image layout.target layout.plan →
      ∀ {checkpoint}, ∀ selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
          retry.image.directory.active.manifest checkpoint,
      ∃ (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
          { published with durable := actual } vacant selected names)
        (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
        (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
          phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
        raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧
        raw.callbacks = source.keeperCallbacks ∧
        ∀ path, path = dir.path ∨ path = dir.file .lock → opening.reads.bindings path = (physical entry).files.names path) →
    ∃ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history)
      (checkpoint : Option (PackedTable × UInt64))
      (selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
        retry.image.directory.active.manifest checkpoint)
      (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
        { published with durable := actual } vacant selected names)
      (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
      (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
        phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream)
      (next : NativeReadPosition current.current.history current.current.submissions)
      (returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
        RawMarkedOpenInterpreter.assemble get set ptrEq),
      source.FailedCalls rebooted errors entry ∧
      (view.descriptors rebooted).slots = [] ∧
      (view.files rebooted).owners (dir.file .lock) = none ∧
      (view.files rebooted).image = retry.image ∧
      checkpointFiles.Frames selectedPath (filesAt entry) ∧
      view.files entry = retry ∧
      source.openTable input entry = .ok returned.handle.table returned.start.reached ∧
      (view.handle raw.seed.afterPending raw.seed.handle).1.inode
        (view.handle raw.seed.afterPending raw.seed.handle).2.1.description =
        state.census.inode state.directorySlot.description ∧
      (view.handle raw.raw.afterFlock raw.raw.lock).1.inode
        (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description = state.census.inode state.owner.description ∧
      (pair.manifest = none → names (dir.file .manifest) = none ∧
        ∃ filename message, opening.reads.reads.stat (dir.file .manifest) =
          .error (.noFileOrDirectory filename 2 message)) ∧
      (∀ bytes, pair.manifest = some bytes → opening.ReadsSample contents (dir.file .manifest) bytes) ∧
      opening.ReadsSample contents (dir.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
      (∀ bytes metadata, pair.manifest = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat, ∀ payload, actual metadata.header.generation index = some payload →
        opening.ReadsSample contents (dir.file (.run metadata.header.generation index)) payload) ∧
      (∀ segment ∈ layout.sealed ++ [layout.keeper],
        opening.ReadsSample contents (dir.file (.walSegment segment.first)) segment.bytes) ∧
      returned.start.current.ready.state.writer.checkpoint = checkpoint ∧
      returned.start.current.ready.reads = (ready).reads ∧
      (state.session.phaseRef ∈ opening.callbacks.liveRefs → next.state.session.phaseRef ≠ state.session.phaseRef) ∧
      (state.session.sessionRef ∈ opening.callbacks.liveRefs → next.state.session.sessionRef ≠ state.session.sessionRef) ∧
      state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      (pair.manifest = state.writer.target.pair.manifest → next.state.writer.target.range.watermark = state.writer.target.range.watermark) ∧
      (pair.manifest = some newManifest → next.state.writer.target.range.watermark = state.writer.history.length) ∧
      origin.LedgerSuffix earlier returned.start.current ∧
      RebootDirectoryBindings next.state names ∧
      next.state.writer.target = layout.target ∧ next.state.writer.published.durable = actual ∧
      next.state.writer.wal = { wal with directory := next.state.files.image.directory } ∧
      (∀ segment ∈ wal.segments, checkpointFiles.Stored (dir.file (.walSegment segment.first)) segment.bytes) ∧
      (checkpointFiles.Frames selectedPath (physical rebooted).files →
        (∀ names ∈ (physical rebooted).crashNames, names dir.path = checkpointFiles.names dir.path) →
        (∀ {prior : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
          source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(path, cause)]) errors →
          source.openTable path before = .error cause after →
          (physical before).files.Frames selectedPath (physical after).files ∧
          (physical before).Frames (· = dir.path) (physical after)) →
        AlignedCheckpointWriteEffects raw next.state physical (fun heap => (inodes heap).visible) →
        ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
          cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
          returned.start.WriteStorageEntry view cache (physical returned.start.reached) (inodes returned.start.reached).visible ∧
          (∀ {α : Type} (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
            (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
            (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
            (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
            {sequence : UInt64} {writeReached : heap}, request.rows ≠ [] →
            returned.start.ObservesPublishedWrite appender stager syncer view cache inodes runs physical
              inode buffered request lookup rename sequence writeReached →
            ∀ (read : SnapshotReadRequest α), returned.handle.ObservesSnapshotToken writeReached →
            let directory := returned.start.current.ready.state.session.directory
            request.runOnRawOpenPhase directory lookup (appender.run cache.active) (stager.run cache.pending)
              (syncer.group directory.path cache.directory cache.active cache.pending) rename
              returned.handle.phase returned.handle.get returned.handle.set returned.start.reached = .ok sequence writeReached ∧
            ∃ (batch : List WAL.Write) (table : PackedTable) (written last : NativeOpenedPosition returned.handle)
              (reference : SnapshotTable UInt64) (events : List NativeExecutionEvent),
              prepareBatch returned.start.current.ready.state.writer.installed.table request.rows = some (batch, table) ∧
              sequence = table.committed ∧ written.reached = writeReached ∧
              NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
              origin.LedgerSuffix (earlier ++ (.acknowledged request batch :: events)) last.current ∧
              SnapshotWalReplay .empty (current.current.history ++ batch) reference ∧
              ∀ observation ∈ last.current.ready.reads, observation.agrees reference)) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode current.current.history) =
        .ok returned.start.current.ready.state.writer.installed.table ∧
      InstalledClientReplay current.current.submissions (ready).reads current.current.history
        returned.start.current.ready.state.writer.installed returned.start.current.ready.state.session ∧
      (∀ {α : Type} (request : SnapshotReadRequest α),
        returned.handle.ObservesSnapshotToken returned.start.reached →
        ∃ (last : NativeOpenedPosition returned.handle) (events : List NativeExecutionEvent)
          (reference : SnapshotTable UInt64),
          NativeOpenedTrace returned.start [.acquire, .readAt returned.start.pins.length request] events last ∧
          origin.LedgerSuffix (earlier ++ events) last.current ∧
          SnapshotWalReplay .empty current.current.history reference ∧
          last.current.ready.reads = (ready).reads ++
            [request.record returned.start.current.ready.state.writer.installed.table.committed
              (request.replay reference returned.start.current.ready.state.writer.installed.table.committed)] ∧
          ∀ read ∈ last.current.ready.reads, read.agrees reference)

/-- An admitted physical checkpoint sample supplies the same aligned
reader, failed-open lineage, and exact returned table for either exit. -/
theorem NativeCheckpointSourcePrefix.reopensSampledCheckpoint
    (prior : NativeCheckpointSourcePrefix current primitives fsync stage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (selection : prior.SampledReplay names contents)
    (resetCensus : (view.descriptors rebooted).slots = [])
    (resetLock : (view.files rebooted).owners ((dbDir).file .lock) = none)
    {errors : List (FilePath × IO.Error)} (attempts : source.FailedCalls rebooted errors entry)
    (effects : OpenPhaseCellEffects view.phase get set)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prefixLedger : origin.LedgerSuffix earlier current.current) :
    NativeOpenedPosition.SampledCheckpointRecovery (view := view) (source := source) (input := input)
      (rebooted := rebooted) (entry := entry) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      (write := write) (get := get) (set := set) (ptrEq := ptrEq) current inodes observe prior.manifest names contents origin earlier errors := by
  unfold NativeOpenedPosition.SampledCheckpointRecovery
  intro dir state pair wal actual retry vacant selectedPath physical filesAt checkpointFiles reset each observeReads
  obtain ⟨sameFilesAt, sameImage⟩ := attempts.framesAfter .empty
    (fun before after => (filesAt before).Frames selectedPath (filesAt after) ∧
      (view.files after).image = (view.files before).image)
    (fun _ => ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl⟩)
    (fun earlier later => ⟨earlier.1.trans later.1, later.2.trans earlier.2⟩)
    (fun prior inside returned => each prior (by simpa only [List.nil_append] using inside) returned)
  have survivor := reset.trans sameFilesAt
  have entryKeeps : ∀ path, path = dir.path ∨ path = dir.file .lock → (physical entry).files.names path = names path := by
    intro path authority
    exact (survivor path (authority.imp_right Or.inl)).1
  obtain ⟨authority, marker, segments, published, layout, _, walLayout, walValid, keeper, aligned,
    descriptors, offsets, prepared, _, accepted, _, _, _, checkpoint, _, _, selected, generation, _, _, _, _⟩ :=
    selection
  obtain ⟨opening, chronology, raw, sameFiles, sameDirectory, sameKeeper, readsAtEntry⟩ :=
    observeReads published layout prepared selected
  have captures := raw.capturesRebootAuthority rfl (fun atHeap => (physical atHeap).files.names) names authority entryKeeps readsAtEntry
  have markerSelected : retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, payload⟩ := marker
    change names (dir.file .walBoundary) = some inode at bound
    change [contents inode] = _ at payload
    change (names (dir.file .walBoundary)).map contents = _
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  have readSegments : ∀ segment ∈ layout.sealed ++ [layout.keeper],
      (names (dir.file (.walSegment segment.first))).map contents = some segment.bytes := by
    intro segment included
    have member : segment ∈ state.writer.wal.segments := by
      rw [descriptors, WalSegmentImage.readDescriptors] at included
      split at included
      · exact (List.mem_filter.mp included).1
      · exact List.mem_append_right _ included
    obtain ⟨inode, bound, payload⟩ := segments segment member
    change names (dir.file (.walSegment segment.first)) = some inode at bound
    change [contents inode] = _ at payload
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  obtain ⟨missing, manifestRead, markerRead, runRead, walReads⟩ :=
    opening.readsSelectedSamples contents rfl rfl markerSelected (fun _ _ _ _ _ _ _ stored => stored) aligned readSegments
  have following := opening.reads.walReads.selectedAfterWatermark offsets descriptors
  obtain ⟨valid, history, pending⟩ := (ready).readPrefix.refines
  have first : layout.target.first = wal.active.first := congrArg WalSegment.first keeper
  obtain ⟨next, returned, opened, selectedAgain, priorReads, sameTarget, sameRuns, sameWal, replay, ledger⟩ :=
    raw.returnsSelectedFromFixedInterpreter sameFiles sameDirectory sameKeeper prepared following accepted
      valid.retained.resumed.ordered walLayout walValid valid.retained.spans rfl first rfl
      history pending (ready).readPrefix.readsBounded write effects ptrEq
  have unchanged : current.current.LedgerSuffix [] returned.start.current :=
    ⟨by rw [returned.position]; simp, by rw [returned.position]; simp, by simpa using priorReads, by simp⟩
  have afterRestart : origin.LedgerSuffix earlier returned.start.current := by
    simpa only [List.append_nil] using prefixLedger.append unchanged
  have newState := congrArg (fun position : NativeExecutionPosition => position.ready.state) returned.position
  rw [newState] at sameTarget sameRuns sameWal
  have readNames (path : FilePath) (inside : path = dir.path ∨ path = dir.file .lock) :
      opening.reads.bindings path = names path :=
    (readsAtEntry path inside).trans (entryKeeps path inside)
  have newAuthority : RebootDirectoryBindings next.state names := by
    constructor
    · rw [returned.resolvedDirectory, returned.repairCensus, returned.directorySlot, opening.finish.sameCensusObjects]
      exact (readNames _ (.inl rfl)).symm.trans opening.reads.sameObjects.1
    · rw [returned.resolvedDirectory, returned.repairCensus, returned.lockOwner, opening.finish.sameCensusObjects]
      exact (readNames _ (.inr rfl)).symm.trans opening.reads.sameObjects.2.1
  have sameScope : next.state.crashPath = selectedPath := by
    apply NativeReadyState.crashPath_forSelectedCheckpoint _ dir state.writer pair.manifest returned.resolvedDirectory
    · rw [sameWal]
    · rw [sameWal]
    · exact congrArg (fun target : Target => target.pair.manifest) sameTarget
  have paired : next.state.writer.target.pair = pair :=
    (congrArg Target.pair sameTarget).trans prepared.pair.symm
  have phaseFresh (oldLive : state.session.phaseRef ∈ opening.callbacks.liveRefs)
      (same : next.state.session.phaseRef = state.session.phaseRef) : False :=
    returned.phaseFresh ((returned.phaseRef.trans same).symm ▸ oldLive)
  have sessionFresh (oldLive : state.session.sessionRef ∈ opening.callbacks.liveRefs)
      (same : next.state.session.sessionRef = state.session.sessionRef) : False :=
    returned.tokenFresh ((returned.tokenRef.trans same).symm ▸ oldLive)
  have checked : CheckpointPreflight (.ready state.writer.installed) (.ok (prior.next, prior.manifest)) :=
    valid.phase ▸ prior.prepared
  have chosen : next.state.writer.target.pair.manifest = state.writer.target.pair.manifest ∨
      next.state.writer.target.pair.manifest = some prior.manifest := by
    rw [paired]
    exact generation.imp (fun old => old.2.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair))
      And.right
  have watermark := checked.reopenedWatermark valid.retained chosen
  rw [paired] at watermark
  refine ⟨published, layout, checkpoint, selected, opening, chronology, raw, next, returned,
    attempts, resetCensus, resetLock, sameImage.symm.trans (congrArg LockedFileState.image raw.raw.entryFiles), survivor,
    raw.raw.entryFiles, opened, captures.1, captures.2, missing, manifestRead, markerRead, runRead, walReads,
    selectedAgain, priorReads, phaseFresh, sessionFresh, watermark.1, watermark.2.1, watermark.2.2, afterRestart, newAuthority, sameTarget, sameRuns, sameWal, segments, ?_, replay, ledger, ?_⟩
  · intro restored parent afterCall laws
    obtain ⟨files, root⟩ := attempts.carriesCheckpointReset physical selectedPath dir.path checkpointFiles
      (.inl rfl) restored parent afterCall
    have writerHistory := next.readPrefix.refines.2.1.trans history.symm
    have firstAtReturn : next.state.writer.wal.active.first = layout.keeper.first :=
      (congrArg (fun image : WalSegmentImage => image.active.first) sameWal).trans (congrArg WalSegment.first keeper.symm)
    have bytesAtReturn : next.state.writer.wal.active.bytes = layout.keeper.bytes :=
      (congrArg (fun image : WalSegmentImage => image.active.bytes) sameWal).trans (congrArg WalSegment.bytes keeper.symm)
    have manifest : (names (next.state.session.directory.file .manifest)).map contents = next.state.writer.target.pair.manifest := by
      rw [returned.resolvedDirectory, sameTarget]
      rfl
    have seals (segment : WalSegment) (present : segment ∈ next.state.writer.wal.sealed) :
        (names (next.state.session.directory.file (.walSegment segment.first))).map contents = some segment.bytes := by
      rw [sameWal] at present
      obtain ⟨inode, bound, stored⟩ := segments segment (List.mem_append_left _ present)
      change names (dir.file (.walSegment segment.first)) = some inode at bound
      change [contents inode] = [segment.bytes] at stored
      rw [returned.resolvedDirectory, bound, Option.map_some, (List.cons.inj stored).1]
    have runMap (generation : UInt64) (index : Nat) : next.state.writer.published.durable generation index =
        (names (next.state.session.directory.file (.run generation index))).map contents := by
      rw [sameRuns, returned.resolvedDirectory]
    have markerAtSample : (names (next.state.session.directory.file .walBoundary)).map contents =
        some (WAL.Boundary.encode (WAL.encode next.state.writer.history).size.toUInt64) := by
      rw [returned.resolvedDirectory, writerHistory]
      exact markerSelected
    let keeperPath := dir.file (.walSegment layout.keeper.first)
    let held := opening.reads.wal.keeper
    have object := opening.keeperChild.sameObject held.calls held.bound held.contents
    obtain ⟨inode, bound, bytes⟩ := segments layout.keeper (by rw [keeper]; exact List.mem_append_right _ (by simp))
    change names keeperPath = some inode at bound
    change [contents inode] = [layout.keeper.bytes] at bytes
    have sameInode := Option.some.inj (object.symm.trans bound)
    subst inode
    have keeperLive : (physical entry).files.names keeperPath = some held.observesFile.object ∧
        (inodes entry).visible held.observesFile.object = layout.keeper.bytes ++ layout.tail := by
      have onKeeper : keeperPath = dir.file (.walSegment state.writer.wal.active.first) := by
        dsimp only [keeperPath]
        rw [keeper]
      have inside : selectedPath keeperPath := .inr (.inr (.inr (.inl (.inr (.inl onKeeper)))))
      obtain ⟨binding, value⟩ := survivor keeperPath inside
      have payload := value held.observesFile.object object
      change [(inodes entry).visible held.observesFile.object] = [contents held.observesFile.object] at payload
      exact ⟨binding.trans object, (List.cons.inj payload).1.trans
        ((List.cons.inj bytes).1.trans opening.finish.keeperPayload.symm)⟩
    obtain ⟨cache, dirRef, activeRef, pendingRef, readyWrite⟩ :=
      returned.writeStorageFromCheckpointSample physical (fun heap => (inodes heap).visible)
        contents firstAtReturn bytesAtReturn newAuthority manifest seals runMap (sameScope.symm ▸ files)
        markerAtSample (returned.resolvedDirectory.symm ▸ root) keeperLive laws
    refine ⟨cache, dirRef, activeRef, pendingRef, readyWrite, ?_⟩
    intro α appender stager syncer inode buffered request lookup rename sequence writeReached nonempty observed read token
    obtain ⟨_, wrote, batch, table, written, last, reference, events, prepared, committed, atWrite, trace, suffix,
      replay, reads, _⟩ := returned.start.acknowledgesAndReadsLatest afterRestart appender stager syncer view cache
        inodes runs physical inode buffered request lookup rename nonempty readyWrite observed read token
    have sameHistory : returned.start.current.history = current.current.history := by rw [returned.position]
    exact ⟨wrote, batch, table, written, last, reference, events, prepared, committed, atWrite, trace,
      suffix, sameHistory ▸ replay, reads⟩
  · intro α request compareAtAcquire
    obtain ⟨issuer⟩ := returned.handle.hasLatestIssuer
    obtain ⟨_, _, last, reference, _, _, _, _, calls, reads, snapshotReplay, agrees, _⟩ :=
      returned.start.acquiresAndReadsLatest issuer rfl request compareAtAcquire
    have sameHistory : returned.start.current.history = current.current.history := by rw [returned.position]
    refine ⟨last, _, reference, calls, ?_, sameHistory ▸ snapshotReplay, ?_, agrees⟩
    · exact afterRestart.append calls.common.ledgerSuffix
    · rwa [priorReads] at reads

/-- A reboot restores a sampled final checkpoint image. Scoped effects
carry it across the actual failed calls to the healthy aligned opener,
which reads the same files and returns the exact replayed table. With
the durable effects, the same handle can publish a batch and read it. -/
theorem NativeCheckpointSourceStop.reopensSampledFinalCheckpoint
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : RenamedCheckpointStorageEffects stop inodes runs observe) (effective : Bool)
    (directoryEffect : CheckpointManifestDirectoryEffect dbDir effective storage.scope
      (observe stop.atIssue.2).storageObservation (observe reached.2).storageObservation)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    (resetCensus : (view.descriptors rebooted).slots = [])
    (resetLock : (view.files rebooted).owners ((dbDir).file .lock) = none)
    {errors : List (FilePath × IO.Error)} (attempts : source.FailedCalls rebooted errors entry)
    (effects : OpenPhaseCellEffects view.phase get set)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prefixLedger : origin.LedgerSuffix earlier current.current) :
    NativeOpenedPosition.SampledCheckpointRecovery (view := view) (source := source) (input := input)
      (rebooted := rebooted) (entry := entry) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      (write := write) (get := get) (set := set) (ptrEq := ptrEq) current inodes observe stop.manifest names contents origin earlier errors := by
  have selection := stop.replaysSampledFinalCheckpoint inodes runs observe storage effective directoryEffect names chosen contents sampled
  exact stop.toNativeCheckpointSourcePrefix.reopensSampledCheckpoint inodes runs observe names contents selection
    resetCensus resetLock attempts effects prefixLedger

/-- A returned rename error supplies the exact selected files to the
fixed opener. The caller supplies local rename effects and one allowed
crash map. The same incoming ledger continues on the returned table. -/
theorem NativeCheckpointSourceError.reopensSampledRenameError
    (stop : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : CheckpointPublicationStorageEffects stop.toNativeCheckpointSourcePrefix inodes runs observe)
    (effective : Bool)
    (renameEffect : stop.ManifestRenameEffect inodes observe storage.scope effective)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    (resetCensus : (view.descriptors rebooted).slots = [])
    (resetLock : (view.files rebooted).owners ((dbDir).file .lock) = none)
    {errors : List (FilePath × IO.Error)} (attempts : source.FailedCalls rebooted errors entry)
    (effects : OpenPhaseCellEffects view.phase get set)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prefixLedger : origin.LedgerSuffix earlier current.current) :
    stop.SelectsManifest effective names contents ∧
    NativeOpenedPosition.SampledCheckpointRecovery (view := view) (source := source) (input := input)
      (rebooted := rebooted) (entry := entry) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      (write := write) (get := get) (set := set) (ptrEq := ptrEq) current inodes observe stop.manifest names contents origin earlier errors := by
  obtain ⟨choice, selection⟩ := stop.replaysSampledRenameError inodes runs observe storage effective renameEffect names chosen contents sampled
  exact ⟨choice, stop.toNativeCheckpointSourcePrefix.reopensSampledCheckpoint inodes runs observe names contents selection
    resetCensus resetLock attempts effects prefixLedger⟩

end Alvoki.Storage.DiskSession
