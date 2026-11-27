import Alvoki.Storage.Disk.NativeCheckpointStopContinuation
import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawManifestStatError

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

section Admission

variable {heap image : Type} {input : FilePath} {directory : DiskDirectory} {initial : DescriptorInventory}
  {files : LockedFileState image} {admission : CensusOpenAdmissionReports input directory initial files}
  {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}

/-- The names captured by the modeled admission identify the same
descriptions as the actual cache open and acquired flock. -/
theorem RawOpenAdmissionReport.capturesNamedAuthority
    (raw : RawOpenAdmissionReport admission view calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view init raw.afterFlock)
    (names : FilePath → Option Nat)
    (root : names directory.path = some (admission.reached.inode admission.cached.description))
    (lock : names (directory.file .lock) = some (admission.reached.inode admission.owner.description)) :
    names directory.path = some ((view.handle seed.afterPending seed.handle).1.inode
      (view.handle seed.afterPending seed.handle).2.1.description) ∧
    names (directory.file .lock) = some ((view.handle raw.afterFlock raw.lock).1.inode
      (view.handle raw.afterFlock raw.lock).2.1.description) := by
  rw [seed.sameHandle, seed.openedHandle, raw.sameLock, raw.appendHandle]
  exact ⟨root, lock⟩

end Admission

section AlignedOpen

variable {heap stream : Type} {state : NativeReadyState} {input : FilePath} {directory : DiskDirectory}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : Image}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The actual admission's new handles reacquire the prior directory and
LOCK inodes through the chosen sample and the observed entry names. -/
theorem RawAlignedCheckpointReopenEffects.capturesRebootAuthority
    (raw : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (resolved : directory = state.session.directory)
    (namesAt : heap → FilePath → Option Nat) (chosen : FilePath → Option Nat)
    (authority : RebootDirectoryBindings state chosen)
    (entryKeeps : ∀ path, path = directory.path ∨ path = directory.file .lock →
      namesAt entry path = chosen path)
    (readsAtEntry : ∀ path, path = directory.path ∨ path = directory.file .lock →
      opening.reads.bindings path = namesAt entry path) :
    (view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description =
      state.census.inode state.directorySlot.description ∧
    (view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description =
      state.census.inode state.owner.description := by
  subst directory
  have witnessed := opening.reads.sameObjects
  obtain ⟨directory, lock⟩ := raw.raw.capturesNamedAuthority raw.seed chosen
    (((readsAtEntry _ (.inl rfl)).trans (entryKeeps _ (.inl rfl))).symm.trans witnessed.1)
    (((readsAtEntry _ (.inr rfl)).trans (entryKeeps _ (.inr rfl))).symm.trans witnessed.2.1)
  exact ⟨Option.some.inj (directory.symm.trans authority.directory),
    Option.some.inj (lock.symm.trans authority.lock)⟩

end AlignedOpen

section

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}


/-- The two workers share the bounded aligned recovery outcome at this
admission. Equal keeper extents use the same reader and the repair
does not stage a longer keeper. -/
private theorem RawAlignedCheckpointReopenEffects.heldRecoveryAgrees
    (raw : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (stage : LongKeeperStageCallbacks heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks
      raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef remove write rename bootstrap directory cache raw.seed.afterPending =
    recoverHealthyMarkedWithRefs raw.fileCalls raw.directoryCalls raw.callbacks
      raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef remove stage rename calls.lookup directory
      (bootstrap directory cache) raw.seed.afterPending := by
  obtain ⟨opened, oldWorker, oldProjected, _⟩ := raw.keeper.recoversFromOpenedCache raw.extents raw.seals
    valid following accepted ordered raw.flat raw.marked remove write rename (bootstrap directory cache)
  have aligned : NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper
      remove stage rename (.aligned opening.finish) raw.keeper.reached := .aligned raw.keeper
  obtain ⟨_, healthy, worker, projected, _⟩ := aligned.recovers raw.extents raw.seals
    valid following accepted ordered raw.flat raw.marked (bootstrap directory cache)
  have same := (EStateM.Result.ok.inj (oldProjected.symm.trans projected)).1
  subst healthy
  unfold RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs
  rw [← raw.sameLookup]
  exact oldWorker.trans worker.symm

theorem RawAlignedCheckpointReopenEffects.ReturnedAt.returnsFixedInterpreter
    {source : RawMarkedOpenInterpreter heap stream}
    {raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
      phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream}
    {ledgerHistory : List WAL.Write} {submissions : List DatabaseSubmissions}
    {next : NativeReadPosition ledgerHistory submissions}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
      RawMarkedOpenInterpreter.assemble get set ptrEq)
    (files : raw.fileCalls = source.fileCalls) (directoryReads : raw.directoryCalls = source.directoryCalls)
    (keeper : raw.callbacks = source.keeperCallbacks)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    source.openTable input entry = .ok returned.handle.table returned.start.reached := by
  let recover := fun resolved lock cache => do
    let opened ← source.calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks raw.seed.directoryRef
      raw.seed.activeRef raw.seed.pendingRef source.remove write source.rename source.bootstrap resolved cache
    installReady opened.installed source.allocatePhase source.allocateToken
      (fun phase token => pure (RawMarkedOpenInterpreter.assemble resolved lock cache phase token))
  refine raw.raw.returnsFixedAfterWorkerAgreement source raw.seed returned.makeCache returned.cacheUses recover ?_ returned.rawOpen
  intro fixed
  unfold RawMarkedOpenInterpreter.worker
  simp only [recover, Bind.bind, EStateM.bind]
  rw [raw.heldRecoveryAgrees valid following accepted ordered source.remove write source.stage source.rename
    source.bootstrap fixed, files, directoryReads, keeper]

/-- The aligned source opener installs the checkpoint selected by its
actual reader. The fixed interpreter returns that same table and heap,
and the returned position preserves the earlier client replay. -/
theorem RawAlignedCheckpointReopenEffects.returnsSelectedFromFixedInterpreter
    {source : RawMarkedOpenInterpreter heap stream}
    (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
      phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream)
    (files : raw.fileCalls = source.fileCalls) (directoryReads : raw.directoryCalls = source.directoryCalls)
    (keeperCallbacks : raw.callbacks = source.keeperCallbacks)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    {ledgerHistory : List WAL.Write} {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
    (sameHistory : history = ledgerHistory) (pending : PendingClientReplay log recorded ledgerHistory)
    (bounded : ∀ read ∈ recorded, read.BoundedBy ledgerHistory.length)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (next : NativeReadPosition ledgerHistory log)
      (returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
        RawMarkedOpenInterpreter.assemble get set ptrEq),
      source.openTable input entry = .ok returned.handle.table returned.start.reached ∧
      returned.start.current.ready.state.writer.checkpoint = checkpoint ∧
      returned.start.current.ready.reads = recorded ∧
      returned.start.current.ready.state.writer.target = layout.target ∧
      returned.start.current.ready.state.writer.published.durable = published.durable ∧
      returned.start.current.ready.state.writer.wal =
        { wal with directory := returned.start.current.ready.state.files.image.directory } ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode ledgerHistory) =
        .ok returned.start.current.ready.state.writer.installed.table ∧
      InstalledClientReplay log recorded ledgerHistory
        returned.start.current.ready.state.writer.installed returned.start.current.ready.state.session := by
  subst ledgerHistory
  let finish : CapturedKeeperFinish opening.callbacks opening.reads vacant selected := .aligned opening.finish
  let report : MarkedOpenSuccessReports input directory history log recorded :=
    { inventory := inventory
      retry := retry
      layout := layout
      published := published
      checkpoint := checkpoint
      selected := selected
      vacant := vacant
      opening := ⟨opening.admission, opening.callbacks, opening.reads, finish, chronology, opening.marker,
        opening.markerFound⟩
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
      bounded := bounded }
  obtain ⟨state, seeded, cache, _, owner, slot, _, durableAtReturn, selectedAtReturn, _, targetAtReturn, _, retainedWal, exactReplay, _, _⟩ :=
    finish.startsNativeReadPrefix chronology opening.markerFound prepared.newer following accepted ordered walLayout walValid
      spans active keeper kept pending bounded
  let next : NativeReadPosition history log := ⟨finish.run chronology, state, state, recorded, seeded⟩
  obtain ⟨returned⟩ := raw.installsAtReportedPosition (report := report) next source.remove write source.rename
    source.bootstrap RawMarkedOpenInterpreter.assemble ptrEq rfl rfl seeded.frames.1 cache owner slot
    RawMarkedOpenInterpreter.assembles effects
  have opened := returned.returnsFixedInterpreter files directoryReads keeperCallbacks prepared following accepted ordered
  refine ⟨next, returned, opened, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [returned.position]
    exact selectedAtReturn
  · rw [returned.position]
  · rw [returned.position]
    exact targetAtReturn
  · rw [returned.position]
    exact durableAtReturn
  · rw [returned.position]
    exact retainedWal
  · rw [returned.position]
    exact exactReplay
  · rw [returned.position]
    exact seeded.guardedReplay

end

section QuietOpen

variable {heap stream : Type} {state : NativeReadyState} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}

/-- The healthy reader and installer use the selected reboot and the
fixed opener's callbacks at this entry. The writer derives the plan. -/
def RawMarkedOpenInterpreter.ObservesQuietAligned (source : RawMarkedOpenInterpreter heap stream)
    (crash : NativeReadyQuietCrash state) (input : FilePath) (view : OpenCloseHeapView heap FileImage)
    (entry : heap) (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat) : Prop :=
  ∀ layout : CanonicalKeeperLayout crash.retry.image state.writer.history,
    layout.target = state.writer.target → Prepared crash.retry.image layout.target layout.plan →
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint,
    ∃ (reader : NativeReadyRestartReads crash input layout selected)
      (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view source.calls source.init
        entry phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
      raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧ raw.callbacks = source.keeperCallbacks

variable {history : List WAL.Write} {log : List DatabaseSubmissions}
  (current : NativeReadPosition history log) (crash : NativeReadyQuietCrash current.state)
  (source : RawMarkedOpenInterpreter heap stream)
  (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
  (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
  (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
  (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

local notation "selectedFootprint" => checkpointSurvivorPath current.state.session.directory current.state.writer
  current.state.writer.target.pair.manifest

/-- One aligned reader fixes both the selected bytes and the position
installed on the table returned by the fixed opener. -/
def NativeReadPosition.QuietFixedReturnAt (input : FilePath) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (before : heap)
    (entry : heap) (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat) : Prop :=
  ∃ (layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
    (reader : NativeReadyRestartReads crash input layout selected)
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view source.calls source.init
      entry phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
    (view.descriptors entry, view.files entry) = (crash.reboot, crash.retry) ∧
    (layout.keeper = current.state.writer.wal.active ∧
      ∀ path payload, selectedFootprint path → reader.ReadsSurvivor path payload →
        ∃ read : reader.opening.reads.reads.ObservesFile path payload,
          names before path = some read.object ∧ names entry path = some read.object ∧ bytes entry read.object = payload) ∧
    ∃ next : NativeReadPosition history log,
      next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      ∃ returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
          RawMarkedOpenInterpreter.assemble get set ptrEq,
        source.openTable input entry = .ok returned.handle.table returned.start.reached

variable {get set} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before rebooted : heap} {beforeCensus : DescriptorInventory}

/-- The retained writer determines the aligned keeper, descriptors and
prepared repair. The actual reader and allocator determine the table. -/
theorem NativeReadPosition.reopensQuietFromFixedInterpreter
    (reboot : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (frame : (⟨names rebooted, fun inode => [bytes rebooted inode]⟩ : CheckpointSurvivingFiles).Frames selectedFootprint
      ⟨names entry, fun inode => [bytes entry inode]⟩)
    (observed : source.ObservesQuietAligned crash input view entry phaseIdentity tokenIdentity)
    (effects : OpenPhaseCellEffects view.phase get set) :
    current.QuietFixedReturnAt crash source write get set ptrEq input view names bytes before entry phaseIdentity tokenIdentity := by
  have retained := current.readPrefix.refines.1.retained
  obtain ⟨layout, target, keeper, descriptors, offsets, prepared⟩ := retained.powerLossLayout
  let selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.state.writer.checkpoint := retained.resumed.selected
  obtain ⟨reader, raw, files, directoryReads, callbacks⟩ := observed layout target prepared selected
  obtain ⟨next, reads, returnedSession, replay, ⟨returned⟩⟩ :=
    raw.reopensQuietSelection current source.remove write source.rename source.bootstrap
      RawMarkedOpenInterpreter.assemble ptrEq target keeper descriptors offsets prepared
      RawMarkedOpenInterpreter.assembles effects
  have following := reader.opening.reads.walReads.selectedAfterWatermark offsets descriptors
  have fixed := returned.returnsFixedInterpreter files directoryReads callbacks prepared following
    retained.resumed.accepted retained.resumed.ordered
  refine ⟨layout, selected, reader, raw, Prod.ext raw.raw.entryCensus raw.raw.entryFiles,
    ⟨keeper, ?_⟩, next, reads, returnedSession, replay, returned, fixed⟩
  intro path payload kept read
  obtain ⟨actual, atBoot, byteValue⟩ := reboot.readsSurvivingFile kept read
  have protectedPath : current.state.crashPath path := .inr (.inr kept)
  have preBoot := (reboot.liveNames path protectedPath).trans
    ((crash.settled crash.names crash.chosen path protectedPath).symm.trans
      ((reboot.survivorNames path protectedPath).symm.trans atBoot))
  obtain ⟨binding, durableBytes⟩ := frame path kept
  exact ⟨actual, preBoot, binding.trans atBoot, (List.cons.inj (durableBytes actual.object atBoot)).1.trans byteValue⟩

end QuietOpen

section HealthyQuietOpen

variable {heap stream : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {bytes : heap → Nat → ByteArray} {rebooted : heap}

local notation "footprint" => checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
  current.current.ready.state.writer.target.pair.manifest
local notation "liveNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))

/-- Use the settled storage of the last returned operation to choose the
reboot. The raw heap supplies its bindings and bytes, and the local
reader chronology supplies a successful healthy open at that heap. -/
theorem NativeOpenedPosition.reopensQuietFromFixedInterpreter
    (stable : NativeReadyStorage current.current.ready.state (storage current.reached))
    (names : FilePath → Option Nat) (chosen : names ∈ (storage current.reached).crashNames)
    (contents : Nat → ByteArray)
    (durable : ∀ path, footprint path → ∀ inode, names path = some inode →
      contents inode ∈ (storage current.reached).files.bytes inode)
    (rebootObjects : Nat → Nat)
    (census : view.descriptors current.reached = current.current.ready.state.census)
    (survivorNames : ∀ path, current.current.ready.state.crashPath path → liveNames rebooted path = names path)
    (survivorBytes : ∀ path, footprint path →
      ∀ inode, names path = some inode → bytes rebooted inode = contents inode)
    {input : FilePath} (source : RawMarkedOpenInterpreter heap stream)
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (observed : let crash := stable.observeCrash names chosen contents durable rebootObjects
      source.ObservesQuietAligned crash input view rebooted phaseIdentity tokenIdentity)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let crash := stable.observeCrash names chosen contents durable rebootObjects
    RawQuietRebootEntry crash view liveNames bytes current.reached rebooted ∧
    current.current.ready.QuietFixedReturnAt crash source write get set ptrEq input view liveNames bytes current.reached
      rebooted phaseIdentity tokenIdentity := by
  intro crash
  let reboot : RawQuietRebootEntry crash view liveNames bytes current.reached rebooted :=
    ⟨census, fun _ _ => rfl, survivorNames, survivorBytes⟩
  exact ⟨reboot, current.current.ready.reopensQuietFromFixedInterpreter crash source write ptrEq reboot
    (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) observed effects⟩

end HealthyQuietOpen

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {bytes : heap → Nat → ByteArray} {rebooted : heap}

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "footprint" => checkpointSurvivorPath dir current.current.ready.state.writer
  current.current.ready.state.writer.target.pair.manifest
local notation "liveNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "readFiles" => fun atHeap => CheckpointSurvivingFiles.mk (liveNames atHeap) (fun inode => [bytes atHeap inode])

variable (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
  (names : FilePath → Option Nat) (chosen : names ∈ (storage reached.2).crashNames)
  (contents : Nat → ByteArray)
  (durable : ∀ path, checkpointSurvivorPath current.current.ready.state.session.directory
      current.current.ready.state.writer current.current.ready.state.writer.target.pair.manifest path →
    ∀ inode, names path = some inode → contents inode ∈ (storage reached.2).files.bytes inode)
  (rebootObjects : Nat → Nat)

local notation "crash" => NativeReadyStorage.observeCrash stable names chosen contents durable rebootObjects

include durable

/-- Start from the source checkpoint stop's protected storage. The one
reported survivor gives both the reboot entries and the layout of the
later aligned read. A finalized manifest rejection leaves those same
objects at the entry of the successful source open. -/
theorem NativeCheckpointSourceStop.reopensQuietAfterManifestRejection
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (survivorNames : ∀ path, (state).crashPath path → liveNames rebooted path = names path)
    (survivorBytes : ∀ path, footprint path →
      ∀ inode, names path = some inode → bytes rebooted inode = contents inode)
    (booted : (view.descriptors rebooted, view.files rebooted) = ((crash).reboot, (crash).retry))
    {input retryInput : FilePath} (source : RawMarkedOpenInterpreter heap stream)
    {admission : CensusOpenAdmissionReports input dir (view.descriptors rebooted) (view.files rebooted)}
    {admitted : RawOpenAdmissionReport admission view source.calls rebooted}
    {seed : OpenSyncCacheAllocations admission.opened view source.init admitted.afterFlock}
    (seen : RawManifestStatError (admitted := admitted) seed source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (disposes : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view dir source.release admitted.lock admission.owner disposal.reached)
    (frames : seen.FileFrames disposal finalized readFiles footprint)
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (observe : source.ObservesQuietAligned crash retryInput view finalized.reached phaseIdentity tokenIdentity)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    RawQuietRebootEntry crash view liveNames bytes reached.2 rebooted (view.descriptors reached.2) ∧
    source.openTable input rebooted = .error (disposal.diagnostic seen.cause) finalized.reached ∧
    (view.descriptors finalized.reached, view.files finalized.reached) = (view.descriptors rebooted, view.files rebooted) ∧
    (ready).QuietFixedReturnAt crash source write get set ptrEq retryInput view liveNames bytes reached.2
      finalized.reached phaseIdentity tokenIdentity := by
  have reboot := (stop.observesReboot (view := view) (storage := storage) (bytes := bytes) (rebooted := rebooted)
    stable names chosen contents durable rebootObjects survivorNames survivorBytes).2
  obtain ⟨failed, rejected, diagnostic, reached⟩ := seen.finalizesWithInterpreter source disposal disposes finalized
  rw [diagnostic, reached] at rejected
  have fixed := (ready).reopensQuietFromFixedInterpreter crash source write ptrEq reboot frames.preserves observe effects
  have retry : (view.descriptors finalized.reached, view.files finalized.reached) =
      (view.descriptors rebooted, view.files rebooted) := by
    obtain ⟨_, _, _, _, entry, _⟩ := fixed
    exact entry.trans booted.symm
  exact ⟨reboot, rejected, retry, fixed⟩

end Alvoki.Storage.DiskSession
