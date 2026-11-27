import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.Proofs.Write.NativeRawWriteReboot
import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeMarkedEntryObservations
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeMarkedOpenInterpreter
import Alvoki.Storage.Disk.Proofs.Write.NativeWriteCrashReads
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The file bindings selected by the marked opener. This footprint
contains exactly the chosen runs and WAL files, even if another
directory entry with a staging name survived. -/
def CanonicalKeeperLayout.selectedFilePath {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.file .manifest ∨ path = directory.file .walBoundary ∨
    (∃ segment ∈ layout.sealed ++ [layout.keeper], path = directory.file (.walSegment segment.first)) ∨
    ∃ bytes metadata index, image.directory.active.manifest = some bytes ∧
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata ∧ index < metadata.header.runCount.toNat ∧
      path = directory.file (.run metadata.header.generation index)

/-- The same admission also observes the enclosing directory and lock. -/
def CanonicalKeeperLayout.reopenPath {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ path = directory.file .lock ∨ layout.selectedFilePath directory path

section

variable {heap stream : Type} {state : NativeReadyState} {crash : WriteCrashView} {input : FilePath}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage} {vacant : TryLockObserves retry.owners state.session.directory (.ok true)}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    retry.image.directory.active.manifest state.writer.checkpoint}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {rebooted entry : heap} {returns : List (FilePath × IO.Error)}
  {release : IO.FS.Handle → heap → heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

local notation "dir" => state.session.directory
local notation "selection" => layout.selectedFilePath state.session.directory
local notation "footprint" => layout.reopenPath state.session.directory

/-- Result of the reported source open at its own entry heap, including
the exact installed session and the replay used for prior snapshot reads. -/
def RawHealthyMarkedOpenEffects.SelectedReturn
    {opening : MarkedReadyOpenObservations input dir inventory retry layout state.writer.published vacant selected}
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) : Prop :=
    opening.finish.UsesMeasuredRepair ∧
    ∃ (next : NativeReadPosition history log)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      (∃ action : IO DiskTable.OpenSyncFiles, DiskTable.OpenSyncFiles.IsOpenAction (dir).path action ∧
        action = openSyncFilesWith (m := IO) (IO.FS.Handle.mk (dir).path .read)
          (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
          (fun value => liftM (IO.mkRef value)) makeCache) ∧
      (let cache := makeCache raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
       cache.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef raw.seed.directoryRef ∧ cache.AtDirectory (dir).path) ∧
      execute makeCache = .ok handle.table start.reached ∧
      start.current = ⟨history, log, next⟩ ∧ next.reads = reads ∧ next.initial = next.state ∧
      next.state.writer.target = layout.target ∧ next.state.files.image.Ready layout.target ∧
      next.state.writer.checkpoint = state.writer.checkpoint ∧
      next.state.writer.published.durable = state.writer.published.durable ∧
      handle.lock = raw.raw.lock ∧ handle.files.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef
        raw.seed.directoryRef ∧ handle.files.AtDirectory (dir).path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      phaseIdentity handle.phase = next.state.session.phaseRef ∧ tokenIdentity handle.token = next.state.session.sessionRef ∧
      phaseIdentity handle.phase ≠ state.session.phaseRef ∧ tokenIdentity handle.token ≠ state.session.sessionRef ∧
      start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef = next.state.cache ∧
      next.state.session.directory = dir ∧ next.state.census = opening.finish.census ∧
      next.state.owner = opening.admission.owner ∧ next.state.directorySlot = opening.admission.cached ∧
      next.state.cache = opening.admission.cache ∧
      next.state.files.image.kept = retry.image.kept ∧
      next.state.writer.wal.active.first = layout.keeper.first ∧ next.state.writer.wal.active.bytes = layout.keeper.bytes ∧
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase next.state.writer.installed raw.repaired,
        (handle.phase, handle.token, start.reached) = (allocation.phase, allocation.token, allocation.afterToken)

/-- Install the marked replay from the files and descriptor inventory used
by the actual healthy admission. The earlier write, crash and failed
opens have no role in the worker and reference allocation proof. -/
theorem RawHealthyMarkedOpenEffects.opensWithSelectedReplay
    {opening : MarkedReadyOpenObservations input dir inventory retry layout state.writer.published vacant selected}
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (previousTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧
      state.session.sessionRef ∈ opening.callbacks.liveRefs)
    (prepared : Prepared retry.image layout.target layout.plan)
    (accepted : state.writer.published.AcceptsVersioned history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix history) retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (descriptors : layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (pending : PendingClientReplay log reads history) (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache
      (assemble resolved lock cache))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    raw.SelectedReturn log reads (raw.openTable bootstrap assemble) get set ptrEq := by
  have following := opening.reads.walReads.selectedAfterWatermark offsets descriptors
  let marked : MarkedOpenSuccessReports input dir history log reads := {
    inventory := inventory
    retry := retry
    layout := layout
    published := state.writer.published
    checkpoint := state.writer.checkpoint
    selected := selected
    vacant := vacant
    opening := opening
    prepared := prepared
    following := following
    accepted := accepted
    ordered := ordered
    wal := wal
    walLayout := walLayout
    walValid := walValid
    spans := spans
    active := active
    keeper := keeper
    kept := kept
    pending := pending
    bounded := bounded
  }
  obtain ⟨next, seeded, cache, census, owner, slot, _, durable, checkpoint, directory, target, seals, _, _, freshRefs⟩ :=
    opening.finish.startsNativeReadPrefix opening.chronology opening.markerFound
      prepared.newer following accepted ordered walLayout walValid spans active keeper kept pending bounded
  let position : NativeReadPosition history log :=
    ⟨opening.finish.run opening.chronology, next, next, reads, seeded⟩
  obtain ⟨measured, installed, cacheOpen, makeCache, action, source, cacheUses, ran⟩ :=
    marked.opensHealthyFromAdmission raw.raw raw.seed raw.checkpoint raw.listing raw.extents raw.seals raw.keeper
      raw.sameLookup raw.flat raw.marked bootstrap assemble constructs raw.allocations
  obtain ⟨handle, start, table, _, sameLock, sameCache, samePhase, sameToken, contents, sameGet, sameSet, sameCompare,
    positionEq, reached, pins, sameFiles, sameCensus, cached, _, _, _, phaseId, tokenId⟩ :=
    installed.startsAtReportedPosition position rfl seeded.frames.1 cache owner slot phase ptrEq
  have freshPhase : phaseIdentity handle.phase ≠ state.session.phaseRef :=
    fun same => freshRefs.1 ((phaseId.symm.trans same).symm ▸ previousTokens.1)
  have freshToken : tokenIdentity handle.token ≠ state.session.sessionRef :=
    fun same => freshRefs.2 ((tokenId.symm.trans same).symm ▸ previousTokens.2)
  have retained := seeded.refines.1.retained
  have keeperFirst : next.writer.wal.active.first = layout.keeper.first :=
    retained.active.symm.trans (congrArg Target.first target)
  have keeperBytes : next.writer.wal.active.bytes = layout.keeper.bytes :=
    retained.layout.activeBytes.trans (by rw [seeded.refines.2.1, keeperFirst, layout.chain.keeperBytes])
  refine ⟨measured, position, makeCache, handle, start, ⟨cacheOpen, action, source⟩, cacheUses, ?_, positionEq, rfl, rfl, target,
    target ▸ seeded.refines.1.retained.resumed.ready, checkpoint, durable, sameLock,
    sameCache.symm ▸ installed.cacheReferences, sameCache.symm ▸ installed.cacheDirectory,
    contents, sameGet, sameSet, sameCompare, phaseId, tokenId, freshPhase, freshToken, pins, sameFiles, sameCensus, cached,
    directory, census, owner, slot, cache, seals, keeperFirst, keeperBytes, ?_⟩
  · rw [table, reached]
    exact ran
  · have session := (EStateM.Result.ok.inj (installed.nativeReturned.symm.trans seeded.frames.1)).1
    have payload := Phase.ready.inj (installed.ready.refines.1.phase.symm.trans
      ((congrArg SegmentedSession.phase session).trans seeded.refines.1.phase))
    have value := installed.installed.trans payload
    let Allocated (payload : Installed) : Prop :=
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase payload raw.repaired,
        (handle.phase, handle.token, start.reached) = (allocation.phase, allocation.token, allocation.afterToken)
    have allocated : Allocated installed.opened.installed := ⟨installed.allocation, by rw [samePhase, sameToken, reached]⟩
    exact Eq.mp (congrArg Allocated value) allocated

/-- A selected crash image supplies the same canonical inodes and
bytes after the actual failed opens. The next measured keeper repair
and reference allocations return the table of that same replay. -/
theorem NativeWriteCrashReads.reopensAfterReadOnlyAttempts
    (reader : NativeWriteCrashReads crash input vacant layout selected)
    (raw : RawHealthyMarkedOpenEffects reader.opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (attempts : RawFinalizedOpenAttempts view dir calls init release rebooted returns entry)
    (files : heap → CheckpointSurvivingFiles)
    (rebootNames : ∀ path, footprint path → (files rebooted).names path = crash.names path)
    (rebootBytes : ∀ path, selection path → ∀ inode, crash.names path = some inode →
      (files rebooted).bytes inode = [crash.contents inode])
    (beforeFlockFrame : ∀ path before (failed : RawBeforeFlockRejection view calls path before),
      (files before).Frames footprint (files failed.reached))
    (flockErrorFrame : ∀ path before (failed : RawFlockRejection view calls dir release path before),
      (files before).Frames footprint (files failed.reached))
    (heldFrame : ∀ path before (failed : RawFinalizedOpenAttempt view dir calls init release path before),
      (files before).Frames footprint (files failed.reached))
    (prepared : Prepared retry.image layout.target layout.plan)
    (accepted : state.writer.published.AcceptsVersioned history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix history) retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (descriptors : layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (pending : PendingClientReplay log reads history) (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache
      (assemble resolved lock cache))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    (view.files rebooted).image = retry.image ∧
    (files entry).names (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description) ∧
    (files entry).names ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description) ∧
    (∀ path, selection path → (files entry).names path = crash.names path) ∧
    (∀ path payload, selection path → reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        (files entry).names path = some read.object ∧ (files entry).bytes read.object = [payload]) ∧
    raw.SelectedReturn log reads (raw.openTable bootstrap assemble) get set ptrEq := by
  have frame := attempts.frames (frame := fun a b => (files a).Frames footprint (files b))
    (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) CheckpointSurvivingFiles.Frames.trans
    beforeFlockFrame flockErrorFrame heldFrame
  have names : ∀ path, footprint path → (files entry).names path = crash.names path := by
    intro path inScope
    exact (frame path inScope).1.trans (rebootNames path inScope)
  have reachedBytes : ∀ path, selection path → ∀ inode, crash.names path = some inode →
      (files entry).bytes inode = [crash.contents inode] := by
    intro path inScope inode bound
    have protects : footprint path := .inr (.inr inScope)
    exact ((frame path protects).2 _ ((rebootNames path protects).trans bound)).trans (rebootBytes path inScope inode bound)
  have entryImage := congrArg LockedFileState.image raw.raw.entryFiles
  refine ⟨attempts.preserves.2.symm.trans entryImage, ?_, ?_, ?_, ?_, ?_⟩
  · rw [raw.seed.sameHandle, raw.seed.openedHandle]
    exact (names _ (.inl rfl)).trans (reader.directory.symm.trans reader.opening.reads.sameObjects.1)
  · rw [raw.raw.sameLock, raw.raw.appendHandle]
    exact (names _ (.inr (.inl rfl))).trans (reader.lock.symm.trans reader.opening.reads.sameObjects.2.1)
  · intro path selectedFile
    exact names path (.inr (.inr selectedFile))
  · intro path payload selectedFile ⟨read, bound, bytes⟩
    exact ⟨read, (names _ (.inr (.inr selectedFile))).trans bound,
      (reachedBytes path selectedFile _ bound).trans (congrArg (fun payload => [payload]) bytes)⟩
  · exact raw.opensWithSelectedReplay reader.previousTokens prepared accepted ordered walLayout walValid spans
      active keeper descriptors offsets kept pending bounded bootstrap assemble constructs phase ptrEq

end

section Retry

variable {heap stream : Type} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {returns : List (FilePath × IO.Error)}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}

variable {prior : List WAL.Write} {log : List DatabaseSubmissions} {batch : List WAL.Write}
  (current : NativeReadPosition prior log) {target : Target} {reached : heap}

local notation "dir" => current.state.session.directory
local notation "retryFiles" => (view.files reached)
local notation "census" => (view.descriptors reached)

/-- Primitive observations tying a healthy admission to this interpreter and
to the actual names at the final retry heap. -/
def NativeReadPosition.ObservesHealthyWriteRetry
    (source : RawMarkedOpenInterpreter heap stream)
    (names : heap → FilePath → Option Nat)
    (vacant : TryLockObserves (retryFiles).owners dir (.ok true)) : Prop :=
    ∀ plan : current.SelectedWritePlan batch target (retryFiles).image,
      ∃ (opening : MarkedReadyOpenObservations input dir census retryFiles plan.layout
          current.state.writer.published vacant plan.selected)
        (raw : RawHealthyMarkedOpenEffects opening view source.calls source.init reached phaseIdentity tokenIdentity
          source.allocatePhase source.allocateToken stream source.remove source.stage source.rename),
        raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧
        raw.callbacks = source.keeperCallbacks ∧
        (current.state.session.phaseRef ∈ opening.callbacks.liveRefs ∧
          current.state.session.sessionRef ∈ opening.callbacks.liveRefs) ∧
        names reached (dir).path = opening.reads.bindings (dir).path ∧
        names reached ((dir).file .lock) = opening.reads.bindings ((dir).file .lock) ∧
        ∀ path metadata inode, plan.layout.selectedFilePath dir path →
          opening.reads.reads.stat path = .ok (metadata, inode) → names reached path = some inode

/-- The chronological failures and the successful source return share one
interpreter. Every selected file is read through its reached name and inode. -/
def NativeReadPosition.SelectedWriteRecovery
    (source : RawMarkedOpenInterpreter heap stream)
    (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (first : heap)
    (vacant : TryLockObserves (retryFiles).owners dir (.ok true))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) : Prop :=
    source.FailedCalls first returns reached ∧
    NativeReadyProtectedStorage current.state ⟨names reached, fun inode => [visible reached inode]⟩ ∧
    (retryFiles).image.kept = current.state.writer.files.kept ∧
    target.pair.manifest = current.state.writer.target.pair.manifest ∧
    ∃ (plan : current.SelectedWritePlan batch target (retryFiles).image)
      (opening : MarkedReadyOpenObservations input dir census retryFiles plan.layout
        current.state.writer.published vacant plan.selected)
      (raw : RawHealthyMarkedOpenEffects opening view source.calls source.init reached phaseIdentity tokenIdentity
        source.allocatePhase source.allocateToken stream source.remove source.stage source.rename),
      raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧ raw.callbacks = source.keeperCallbacks ∧
      names reached (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
        (view.handle raw.seed.afterPending raw.seed.handle).2.1.description) ∧
      names reached ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
        (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description) ∧
      (∀ bytes, (retryFiles).image.directory.active.walBoundary = some bytes →
        ∃ read : opening.reads.reads.ObservesFile ((dir).file .walBoundary) bytes,
          names reached ((dir).file .walBoundary) = some read.object ∧ visible reached read.object = bytes) ∧
      (∀ segment ∈ plan.layout.sealed,
        ∃ read : opening.reads.reads.ObservesFile ((dir).file (.walSegment segment.first)) segment.bytes,
          names reached ((dir).file (.walSegment segment.first)) = some read.object ∧ visible reached read.object = segment.bytes) ∧
      (names reached ((dir).file (.walSegment plan.layout.keeper.first)) =
        some opening.reads.wal.keeper.observesFile.object ∧
        visible reached opening.reads.wal.keeper.observesFile.object = plan.layout.keeper.bytes ++ plan.layout.tail) ∧
      (∀ bytes, (retryFiles).image.directory.active.manifest = some bytes →
        ∃ read : opening.reads.reads.ObservesFile ((dir).file .manifest) bytes,
          names reached ((dir).file .manifest) = some read.object ∧ visible reached read.object = bytes) ∧
      (∀ bytes metadata, (retryFiles).image.directory.active.manifest = some bytes →
        Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
        ∀ payload, current.state.writer.published.durable metadata.header.generation index = some payload →
        ∃ run : opening.reads.reads.ObservesFile ((dir).file (.run metadata.header.generation index)) payload,
          names reached ((dir).file (.run metadata.header.generation index)) = some run.object ∧ visible reached run.object = payload) ∧
      raw.SelectedReturn (log ++ [.uncertainBatch batch]) current.reads (fun _ => source.openTable input reached) get set ptrEq

/-- The next successful open uses the actual last retry heap. Its native
stat and open identify the live keeper, while the derived bounded plan
carries the selected checkpoint and earlier client reads into the table.
The retry fold also carries any independently framed observation. -/
theorem NativeReadPosition.opensAfterWriteRetries
    (source : RawMarkedOpenInterpreter heap stream)
    {rows : List (UInt64 × Option UInt64)} {table : PackedTable}
    (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    {first : heap} (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {keep : heap → Prop} {attempts : source.FailedCalls first returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) current.state.selectedRetryPath
      keep attempts)
    (initial : RawOpenRetryTrace.SelectedEntry view current.state target names visible first)
    (atEntry : keep first)
    (liveKeeper : keep reached → RawOpenRetryTrace.KeeperAt view dir target names visible reached)
    (vacant : TryLockObserves (retryFiles).owners dir (.ok true))
    (observe : current.ObservesHealthyWriteRetry
        (input := input) (view := view) (batch := batch) (target := target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names vacant)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    keep reached ∧ current.SelectedWriteRecovery (returns := returns)
    (input := input) (view := view) (batch := batch) (target := target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names visible first vacant get set ptrEq := by
  obtain ⟨⟨plan⟩, kept, frame, carries⟩ := current.preparesWriteRetry prepared fits admitted initial.manifest effects initial.valid
  obtain ⟨opening, raw, fileCalls, directoryCalls, keeperCallbacks, refs, root, lock, actualStat⟩ := observe plan
  let files (heap : heap) : CheckpointSurvivingFiles := ⟨names heap, fun inode => [visible heap inode]⟩
  obtain ⟨rootObject, lockObject⟩ := raw.entryAuthority files root lock
  let file := opening.reads.wal.keeper
  let read := file.calls.observesFile file.bound file.contents
  have named := actualStat _ _ _ (.inr (.inr (.inl ⟨plan.layout.keeper, by simp, rfl⟩))) read.stat
  have samePath := congrArg (fun (target : Target) => (dir).file (.walSegment target.first)) plan.targetEq
  change (dir).file (.walSegment plan.layout.keeper.first) = _ at samePath
  have keeperName := (congrArg (names reached) samePath).symm.trans named
  have atReached := carries atEntry
  have keeperAt := liveKeeper atReached
  unfold RawOpenRetryTrace.KeeperAt at keeperAt
  have contents : visible reached read.object = plan.layout.keeper.bytes ++ plan.layout.tail := by
    rw [keeperName, Option.map_some, plan.layout.visible] at keeperAt
    exact (Option.some.inj keeperAt).symm
  have keptFiles := initial.protectedFiles.frame (fun path keep => frame path (.inr keep))
  have reachedManifest : (retryFiles).image.directory.active.manifest = current.state.writer.target.pair.manifest :=
    (congrArg (fun (target : Target) => target.pair.manifest) plan.targetEq).trans initial.manifest
  refine ⟨atReached, attempts, keptFiles, kept.trans initial.kept, initial.manifest, plan, opening, raw, fileCalls,
    directoryCalls, keeperCallbacks, rootObject, lockObject, ?_, ?_, ⟨named, contents⟩, ?_, ?_, ?_⟩
  · intro bytes selectedMarker
    have sameMarker : (retryFiles).image.directory.active.walBoundary = target.pair.walBoundary :=
      congrArg (fun (t : Target) => t.pair.walBoundary) plan.targetEq
    have live := (frame.visiblePayload (.inl rfl)).trans (initial.marker.trans (sameMarker.symm.trans selectedMarker))
    have stored : (files reached).Stored ((dir).file .walBoundary) bytes := by
      change (names reached ((dir).file .walBoundary)).map (visible reached) = some bytes at live
      obtain ⟨inode, bound, content⟩ := Option.map_eq_some_iff.mp live
      exact ⟨inode, bound, congrArg (fun bytes => [bytes]) content⟩
    obtain ⟨read, bound, content⟩ := opening.readsEntryMarker (files reached) selectedMarker
      (fun _ _ stat => actualStat _ _ _ (.inr (.inl rfl)) stat) stored
    exact ⟨read, bound, (List.cons.inj content).1⟩
  · intro segment chosen
    have selectedPath : plan.layout.selectedFilePath dir ((dir).file (.walSegment segment.first)) :=
      .inr (.inr (.inl ⟨segment, List.mem_append_left _ chosen, rfl⟩))
    obtain ⟨read, bound, content⟩ := opening.readsEntrySeal (files reached) segment chosen
      (fun _ _ stat => actualStat _ _ _ selectedPath stat) (keptFiles.sealedFiles segment (NativeReadPosition.SelectedWritePlan.retainsSeal current plan chosen))
    exact ⟨read, bound, (List.cons.inj content).1⟩
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes present
    let read := file.calls.observesFile file.bound file.contents
    have stored := keptFiles.manifest
    rw [← reachedManifest, present] at stored
    obtain ⟨bound, content⟩ := read.matchesStoredEntry (files reached)
      (fun _ _ stat => actualStat _ _ _ (.inl rfl) stat) stored
    exact ⟨read, bound, (List.cons.inj content).1⟩
  · intro bytes metadata present decoded index within payload stored
    obtain ⟨run⟩ := opening.reads.chunkReads bytes metadata present decoded index within payload stored
    have selectedPath : plan.layout.selectedFilePath dir ((dir).file (.run metadata.header.generation index)) :=
      .inr (.inr (.inr ⟨bytes, metadata, index, present, decoded, within, rfl⟩))
    obtain ⟨bound, content⟩ := run.matchesStoredEntry (files reached)
      (fun _ _ stat => actualStat _ _ _ selectedPath stat)
      (keptFiles.runs bytes metadata (reachedManifest.symm.trans present) decoded index within payload stored)
    exact ⟨run, bound, (List.cons.inj content).1⟩
  ·
    obtain ⟨ready, _, _⟩ := current.readPrefix.refines
    have selected := raw.opensWithSelectedReplay refs plan.prepared plan.accepted plan.ordered plan.walLayout plan.walValid
      ready.retained.spans rfl (congrArg WalSegment.first plan.keeper) plan.descriptors plan.offsets
      (kept.trans (initial.kept.trans ready.retained.sealedFiles)) plan.pending plan.bounded source.bootstrap RawMarkedOpenInterpreter.assemble RawMarkedOpenInterpreter.assembles
      phase ptrEq
    obtain ⟨measured, next, makeCache, handle, start, action, cacheUses, returned, ready⟩ := selected
    exact ⟨measured, next, makeCache, handle, start, action, cacheUses,
      raw.returnsFixedInterpreterOfRun source fileCalls directoryCalls keeperCallbacks
        RawMarkedOpenInterpreter.assemble RawMarkedOpenInterpreter.assembles makeCache cacheUses returned, ready⟩

end Retry

end Alvoki.Storage.DiskSession
